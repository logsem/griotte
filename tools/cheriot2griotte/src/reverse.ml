(* Reverse-map validation: from the Griotte code the lowering produced
   (Lower.t), regenerate the CHERIoT instructions by inverting each rule,
   and compare them, instruction by instruction (mnemonic, registers,
   immediates, relocation targets, branch targets), with the parsed `.s`.

   Independence. Lower.t is read as data only: the code of each function
   (flattened: labels, instructions, macros; the provenance comments and
   the grouping of the outputs by source instruction are not used), the
   frame slot table of each function, the import table, the global
   layout. No function of Lower, nor Cheriot_perms.and_perm, is called:
   the inverse rules work from the Griotte side, with their own control
   flow, liveness and value analysis of the Griotte code, their own
   global layout (recomputed from the `.s` data and compared with the
   lowering's), their own decoding of import names and their own CHERIoT
   image of a Griotte permission pair. The `.s` side is the parser's
   output (Classify only groups the lines by symbol).

   The lowering is not injective; the checker accepts the `.s` when it is
   one of the preimages of the Griotte code, under the side conditions of
   the rule that produced it:
   - [mov r n]: [li r, n], [lui r, n >> 12], or [ct.cmove r, zero] (n = 0);
     [add r s n]: [addi r, s, n], [mv r, s] (n = 0); [mov r s]:
     [ct.cmove r, s] (a callback's [ct.cmove t1, r] included).
   - [load_imm r s w]: [ct.clc r, o(s)]; followed by [geta r r]:
     [ct.clw r, o(s)]. [store_imm s v w]: [ct.csc v, o(s)], or [ct.csw v,
     o(s)] when v is known to hold an integer; [geta t v; store_imm s t
     w]: [ct.csw v, o(s)], with t dead after the store (or v itself) and
     t <> s. For s = sp, o is the byte offset of slot w of the frame, and
     the slot size decides clc/csc (8) or clw/csw (4); otherwise w = o = 0.
   - [lea sp sp -/+k]: the frame allocation/release, k the number of
     slots, back to the frame's byte size.
   - [lea r cgp k]: the [ct.auicgp r, hi(g); ct.cincoffset r, r, lo_i(L)]
     pair of the global g starting at word k, L the label of the auicgp.
   - [fetch_asm sym r]: [ct.auipcc r, hi(imp); ct.clc r, lo_i(L)(r)], imp
     the CHERIoT import whose Griotte name is sym (decoded here, and
     required unique).
   - [setbounds_asm d s w t1 t2]: [ct.csetbounds d, s, len], len in bytes:
     w times the element size (4, or 8 for the one-word null-capability
     global) of the global whose start s holds (value analysis), as a
     number or as %cheriot_compartment_size of a global of that size;
     t1, t2 distinct, not cnull, not s, each d or dead after the macro;
     len below 512 (CHERIoT's exact bounds).
   - [restrict d s c]: [ct.candperm d, s, m] with m any register holding a
     constant k (value analysis on the Griotte code, through the [mov]
     and [add] of the mask) such that CHERIoT's perms(s) & k is the
     CHERIoT image of the pair c, and is representable.
   - Branches: [jeq]/[jne] back to [beq]/[bne]/[beqz]/[bnez], [jlt l x y]
     to [bltu x, y], [jle l x y] to [bgeu y, x] (both operands known
     non-negative, D5), [jmp] to [j]; the Griotte target and the `.s`
     target must be the same instruction (alignment of both streams).
   - [lshiftl d s k]: [slli d, s, k], s a known constant, no 32-bit
     overflow (D14). [ret]/[jalr cra r]: [ct.cret]/[ct.cjalr r], a call
     right after the fetch of r from the switcher (itself right after the
     fetch of a cross-compartment import into ct1, or a [mov ct1 r'], a
     callback) or from a library import, without a label inside the
     sequence. [ecall]: [ecall].
   - Atomicity: no Griotte label between the instructions of a sequence
     that inverts to one CHERIoT instruction.
   Outside the code: the import table (the switcher first, every CHERIoT
   import exactly once, each name decoding to its entry); the globals
   (order .data then .bss, word offsets, and their words back to bytes,
   equal to the `.s` data); the frame slot tables (sorted, disjoint,
   within the frame); each export's label and word offset.

   Not recoverable, hence not checked against the `.s`: the CHERIoT
   labels themselves (only the targets they designate); the mask register
   of a candperm (only its value); the length form of a csetbounds when
   both a number and a size relocation have the right value; which of
   the alternatives above (e.g. li vs ct.cmove zero) the compiler wrote,
   beyond what the `.s` shows. Not checked at all: the order of the
   imports after the switcher (a convention: fetch_asm names its import);
   the frame layout's choice of one word per slot (D24, only its
   consistency); the minimum stack of the exports; the liveness
   convention itself (the calling convention is restated here, not
   derived); Griotte's PermFlowsTo for the restrict (semantics, Rocq);
   the Rocq printing of the AST (asm_check and the golden diff). *)

module G = Griotte_asm
module C = Cheriot_ast

let signed32 n =
  let n = n land 0xffffffff in
  if n >= 0x80000000 then n - 0x100000000 else n

let fits32 n = n >= -0x80000000 && n < 0x80000000

(* {1 Griotte registers and the calling convention} *)

let cnull = 0 and cra = 1 and csp = 2 and cgp = 3 and ctp = 4
let ct0 = 5 and ct1 = 6 and ct2 = 7 and cs0 = 8 and cs1 = 9
let ca_regs = [ 10; 11; 12; 13; 14; 15 ]

let bit r = if r = cnull then 0 else 1 lsl r
let rset = List.fold_left (fun acc r -> acc lor bit r) 0
let live r s = s land bit r <> 0

(* CHERIoT's calling convention (RV32E, CHERIoT ABI): a call reads its
   jump register, ct1 (the switcher's target), the arguments ca0..ca5 and
   the registers kept across calls (csp, cgp, ctp, cs0, cs1); it clobbers
   cra, the temporaries ct0..ct2 and ca0..ca5. A return reads cra, the
   kept registers and the results ca0, ca1. *)
let call_uses r = rset ([ r; ct1; csp; cgp; ctp; cs0; cs1 ] @ ca_regs)
let call_defs = rset ([ cra; ct0; ct1; ct2 ] @ ca_regs)
let ret_uses = rset [ cra; csp; cgp; ctp; cs0; cs1; 10; 11 ]

(* {1 Permissions}

   The CHERIoT bits (Cheriot_perms' layout, the ISA's): 0 GL, 1 LG, 2 SD,
   3 LM, 4 SL, 5 LD, 6 MC, 7 SR, 8 EX. *)

let b_gl = 1 and b_lg = 2 and b_sd = 4 and b_lm = 8 and b_sl = 16 and b_ld = 32
let b_mc = 64 and b_sr = 128 and b_ex = 256

(* The CHERIoT permissions a Griotte pair stands for. *)
let bits_of_pair (p : Cheriot_perms.pair) =
  let rx = match p.rx with Orx -> 0 | R -> b_ld | X -> b_ld lor b_ex | XSR -> b_ld lor b_ex lor b_sr in
  let w = match p.w with Ow -> 0 | W -> b_sd | WL -> b_sd lor b_sl in
  rx lor w
  lor (if rx <> 0 || w <> 0 then b_mc else 0)
  lor (if p.dl = LG then b_lg else 0)
  lor (if p.dro = LM then b_lm else 0)
  lor if p.g = Global then b_gl else 0

(* The permissions of cgp, CHERIoT's RW global root as the loader builds
   it: GL LG SD LM LD MC (no SL, D33). *)
let cgp_bits = b_gl lor b_lg lor b_sd lor b_lm lor b_ld lor b_mc

(* Sets CHERIoT's compressed permission formats encode exactly (GL free):
   capability read-write, read-only, write-only, data only, executable;
   sealing sets (U0 SE US) are not Griotte's. *)
let representable s =
  let s = s land 0xffe in
  let within m = s land lnot m = 0 in
  let has m = s land m = m in
  (has (b_ld lor b_mc lor b_sd) && within (b_ld lor b_mc lor b_sd lor b_sl lor b_lm lor b_lg))
  || (has (b_ld lor b_mc) && within (b_ld lor b_mc lor b_lm lor b_lg))
  || s = b_sd lor b_mc
  || within (b_ld lor b_sd)
  || (has (b_ex lor b_ld lor b_mc) && within (b_ex lor b_ld lor b_mc lor b_sr lor b_lm lor b_lg))

(* {1 The Griotte side} *)

type node = I of G.instr | M of G.macro

let string_of_node = function I i -> G.string_of_instr i | M m -> G.string_of_macro m

exception Bad of string

let bad fmt = Printf.ksprintf (fun s -> raise (Bad s)) fmt

type gfunc = {
  nodes : node array;
  labels_at : string list array;  (* the Griotte labels right before node i *)
  glabel : (string, int) Hashtbl.t;
}

let flatten (fo : Lower.func_out) =
  let nodes = ref [] and labels = ref [] and pending = ref [] in
  let push nd =
    nodes := nd :: !nodes;
    labels := List.rev !pending :: !labels;
    pending := []
  in
  List.iter
    (fun (b : Lower.block) ->
      List.iter (fun l -> pending := l :: !pending) b.labels;
      List.iter
        (fun (lw : Lower.lowered) ->
          List.iter
            (function
              | Lower.C (G.Instr i) -> push (I i)
              | Lower.C (G.Label l) -> pending := l :: !pending
              | Lower.C (G.Symbol s) -> bad "a symbol %s in the code of a function" s
              | Lower.C (G.Local _) -> bad "a local block in the code of a function"
              | Lower.M m -> push (M m))
            lw.outs)
        b.items)
    fo.fo_blocks;
  if !pending <> [] then bad "labels after the last instruction: %s" (String.concat " " (List.rev !pending));
  let nodes = Array.of_list (List.rev !nodes) and labels_at = Array.of_list (List.rev !labels) in
  let glabel = Hashtbl.create 16 in
  Array.iteri
    (fun i ls ->
      List.iter
        (fun l -> if Hashtbl.mem glabel l then bad "label %s defined twice" l else Hashtbl.replace glabel l i)
        ls)
    labels_at;
  { nodes; labels_at; glabel }

let label_of = function G.E (G.Lbl l) -> Some l | _ -> None

let succs gf i =
  let n = Array.length gf.nodes in
  let target x =
    match label_of x with
    | Some l -> (
        match Hashtbl.find_opt gf.glabel l with Some k -> k | None -> bad "jump to %s, not a label of the function" l)
    | None -> bad "indirect jump %s" (string_of_node gf.nodes.(i))
  in
  let next () = if i + 1 < n then [ i + 1 ] else bad "control falls off the end after %s" (string_of_node gf.nodes.(i)) in
  match gf.nodes.(i) with
  | I (G.Jmp x) -> [ target x ]
  | I (G.Jeq (o, _, _) | G.Jne (o, _, _) | G.Jlt (o, _, _) | G.Jle (o, _, _)) -> List.sort_uniq compare (target o :: next ())
  | I (G.Jalr (d, s)) when d = cnull && s = cra -> []
  | I (G.Jalr (d, _)) when d = cnull -> bad "indirect jump %s" (string_of_node gf.nodes.(i))
  | I (G.Fail | G.Halt) -> []
  | _ -> next ()

let arg_regs = function G.R r -> [ r ] | G.E _ -> []

(* Registers read and written. *)
let uses_defs = function
  | M (G.Fetch (_, r)) -> (0, rset [ r ])
  | M (G.Setbounds (d, s, _, t1, t2)) -> (rset [ s ], rset [ d; t1; t2 ])
  | I i -> (
      match i with
      | G.Jmp x -> (rset (arg_regs x), 0)
      | G.Jeq (o, x, y) | G.Jne (o, x, y) | G.Jlt (o, x, y) | G.Jle (o, x, y) ->
          (rset (arg_regs o @ arg_regs x @ arg_regs y), 0)
      | G.Jalr (d, s) when d = cnull && s = cra -> (ret_uses, 0)
      | G.Jalr (d, r) when d = cra -> (call_uses r, call_defs)
      | G.Jalr (d, s) -> (rset [ s ], rset [ d ])
      | G.Mov (d, x) -> (rset (arg_regs x), rset [ d ])
      | G.CLoad (d, s, _) -> (rset [ s ], rset [ d ])
      | G.Store (d, x, _) -> (rset (d :: arg_regs x), 0)
      | G.Lt (d, x, y) | G.Le (d, x, y) | G.Add (d, x, y) | G.Sub (d, x, y) | G.Mul (d, x, y)
      | G.LAnd (d, x, y) | G.LOr (d, x, y) | G.LShiftL (d, x, y) | G.LShiftR (d, x, y) ->
          (rset (arg_regs x @ arg_regs y), rset [ d ])
      | G.Lea (d, s, x) | G.SetA (d, s, x) | G.Restrict (d, s, x) -> (rset (s :: arg_regs x), rset [ d ])
      | G.Subseg (d, s, x, y) -> (rset ((s :: arg_regs x) @ arg_regs y), rset [ d ])
      | G.GetB (d, s) | G.GetE (d, s) | G.GetLen (d, s) | G.GetA (d, s) | G.GetP (d, s) | G.GetL (d, s)
      | G.GetWType (d, s) | G.GetOType (d, s) | G.GetTag (d, s) | G.ClearTag (d, s) ->
          (rset [ s ], rset [ d ])
      | G.Seal (d, x, y) | G.UnSeal (d, x, y) -> (rset [ x; y ], rset [ d ])
      | G.Ecall | G.Fail | G.Halt -> (0, 0)
      | G.Auipcc (d, _) -> (0, rset [ d ]))

(* live_out.(i): the registers read after node i before being written. *)
let liveness gf sx =
  let n = Array.length gf.nodes in
  let ud = Array.map uses_defs gf.nodes in
  let lin = Array.make n 0 and lout = Array.make n 0 in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = n - 1 downto 0 do
      let o = List.fold_left (fun acc s -> acc lor lin.(s)) 0 sx.(i) in
      let u, d = ud.(i) in
      let x = u lor (o land lnot d) in
      if o <> lout.(i) || x <> lin.(i) then (
        lout.(i) <- o;
        lin.(i) <- x;
        changed := true)
    done
  done;
  lout

(* {2 Values}

   What a register holds in the Griotte code: unknown, an integer (known
   non-negative or not), a constant, or a capability of known CHERIoT
   permission bits, holding the start of global [glob] when known. *)

type value = Top | Int of bool | Const of int | Cap of { bits : int; glob : string option }

let is_int = function Int _ | Const _ -> true | Top | Cap _ -> false
let nonneg = function Int b -> b | Const c -> c >= 0 | Top | Cap _ -> false

let join a b =
  match (a, b) with
  | Const x, Const y when x = y -> a
  | Cap x, Cap y when x.bits = y.bits -> Cap { bits = x.bits; glob = (if x.glob = y.glob then x.glob else None) }
  | _ when is_int a && is_int b -> Int (nonneg a && nonneg b)
  | _ -> Top

(* {1 The global layout, recomputed from the `.s`} *)

type glob = { name : string; word : int; words : int; elem : int; size : int }

let data_bytes loc (d : C.data) =
  let le n k = List.init k (fun j -> (n lsr (8 * j)) land 0xff) in
  match d with
  | C.Word (C.Num n) -> le n 4
  | C.Half (C.Num n) -> le n 2
  | C.Byte (C.Num n) -> le n 1
  | C.Zero k -> List.init k (fun _ -> 0)
  | _ -> bad "%s: data other than numbers" loc

(* {1 Expected CHERIoT instructions} *)

type pop =
  | PReg of int
  | PImm of string * (int -> bool)  (* an integer immediate: description, predicate *)
  | PRel of C.reloc * string
  | PLen of int option
      (* a length of n bytes: n, or %cheriot_compartment_size of a global of n
         bytes; None: unknown (the side condition says why) *)
  | PLoSelf  (* %cheriot_compartment_lo_i(L), L a label of the preceding instruction *)
  | PMem of pop * int
  | PTarget of string  (* the Griotte label a branch goes to *)
  | PAnyReg of (int -> string option)  (* a register the lowering drops; the condition on it *)

type pins = string * pop list

let rec string_of_pop = function
  | PReg r -> C.string_of_reg r
  | PImm (d, _) -> d
  | PRel (r, s) -> C.string_of_imm (C.Reloc (r, s))
  | PLen (Some n) -> Printf.sprintf "%d (or the size of a %d-byte global)" n n
  | PLen None -> "<length>"
  | PLoSelf -> "%cheriot_compartment_lo_i(<its hi>)"
  | PMem (p, r) -> Printf.sprintf "%s(%s)" (string_of_pop p) (C.string_of_reg r)
  | PTarget l -> Printf.sprintf "<the instruction at %s>" l
  | PAnyReg _ -> "<reg>"

let string_of_pins (m, ops) =
  match ops with [] -> m | _ -> m ^ " " ^ String.concat ", " (List.map string_of_pop ops)

(* A way of reading Griotte nodes [i .. i + take - 1] back: the CHERIoT
   instructions, and the side conditions (None: holds). *)
type cand = { take : int; out : pins list; conds : string option list }

let imm n = PImm (string_of_int n, ( = ) n)
let imm32 n = PImm (string_of_int n, fun m -> signed32 m = n)

(* {1 Checking one file} *)

type result = { log : string list; errors : string list }

let check (l : Lower.t) =
  let src = l.src in
  let file = src.file in
  let log = ref [] and errors = ref [] in
  let say fmt = Printf.ksprintf (fun s -> log := s :: !log) fmt in
  let err fmt = Printf.ksprintf (fun s -> errors := s :: !errors) fmt in
  (* {2 Imports} *)
  let strip p s =
    let n = String.length p in
    if String.length s >= n && String.sub s 0 n = p then Some (String.sub s n (String.length s - n)) else None
  in
  let decode gsym =
    if gsym = ".Limport_switcher" then Ok ".compartment_switcher"
    else
      match strip ".Limport_" gsym with
      | None -> Error (Printf.sprintf "%s is not an import name" gsym)
      | Some rest -> (
          let ok (i : Classify.import) =
            match i.ikind with
            | Classify.Switcher -> false
            | Library_call f ->
                let d = Demangle.demangle f in
                d = rest || d = "griotte_" ^ rest
            | Cross_call (c, f) -> c ^ "_" ^ Demangle.demangle f = rest
            | Shared_object (n, _) -> n = rest || n = "griotte_" ^ rest
          in
          match List.filter ok src.imports with
          | [ i ] -> Ok i.isym
          | [] -> Error (Printf.sprintf "%s names no import of %s" gsym file)
          | is ->
              Error
                (Printf.sprintf "%s names several imports: %s" gsym
                   (String.concat ", " (List.map (fun (i : Classify.import) -> i.isym) is))))
  in
  (match l.imports with
   | (i, _) :: _ when i.ikind = Classify.Switcher -> ()
   | _ -> err "import table: the switcher is not the first entry");
  List.iter
    (fun ((i : Classify.import), gsym) ->
      match decode gsym with
      | Ok s when s = i.isym -> ()
      | Ok s -> err "import table: %s decodes to %s, but the entry is %s" gsym s i.isym
      | Error e -> err "import table: %s" e)
    l.imports;
  List.iter
    (fun (i : Classify.import) ->
      let k = List.length (List.filter (fun ((j : Classify.import), _) -> j.isym = i.isym) l.imports) in
      if k <> 1 then err "import table: %s occurs %d times" i.isym k)
    src.imports;
  say "imports: %d entries, the switcher first, each name decoding to its CHERIoT import" (List.length l.imports);
  (* {2 Globals} *)
  let order = List.filter (fun (g : Classify.global) -> not g.gbss) src.globals @ List.filter (fun (g : Classify.global) -> g.gbss) src.globals in
  let globs =
    let w = ref 0 in
    List.filter_map
      (fun (g : Classify.global) ->
        let words, elem =
          match g.ginit with
          | [ C.Chericap (C.Num 0) ] -> (1, 8)
          | _ when g.gsize mod 4 = 0 && not (List.exists (function C.Chericap _ -> true | _ -> false) g.ginit) -> (g.gsize / 4, 4)
          | _ -> (-1, 0)
        in
        if words < 0 then (
          err "global %s: neither 4-byte words nor one null capability" g.gname;
          None)
        else
          let r = { name = g.gname; word = !w; words; elem; size = g.gsize } in
          w := !w + words;
          Some r)
      order
  in
  let lnames = List.map (fun (s : Lower.gslot) -> s.gl.gname) l.gslots in
  if lnames <> List.map (fun g -> g.name) globs then
    err "globals: the lowering's order %s differs from .data then .bss, %s" (String.concat " " lnames)
      (String.concat " " (List.map (fun g -> g.name) globs));
  List.iter
    (fun (s : Lower.gslot) ->
      match List.find_opt (fun g -> g.name = s.gl.gname) globs with
      | None -> ()
      | Some g -> (
          if s.gword <> g.word || s.gwords <> g.words then
            err "global %s: the lowering places it at word %d (%d words), the layout at word %d (%d words)" g.name s.gword
              s.gwords g.word g.words;
          (* Its words back to bytes. *)
          try
            if g.elem = 8 then (
              if s.ginit_words <> [ 0 ] then err "global %s: a null capability whose initial word is not 0" g.name)
            else
              let from_s = List.concat_map (data_bytes ("global " ^ g.name)) s.gl.ginit in
              let from_words = List.concat_map (fun w -> List.init 4 (fun j -> ((w land 0xffffffff) lsr (8 * j)) land 0xff)) s.ginit_words in
              if from_words <> from_s then err "global %s: its initial words, back to bytes, differ from the .s data" g.name
          with Bad m -> err "%s" m))
    l.gslots;
  say "globals: %d, at word offsets .data then .bss; initial words back to bytes equal to the .s data" (List.length globs);
  let glob_at k = List.find_opt (fun g -> g.word = k && g.words > 0) globs in
  let glob_named n = List.find_opt (fun g -> g.name = n) globs in
  (* {2 Functions} *)
  let words_of = function I _ -> 1 | M (G.Fetch _) -> 2 | M (G.Setbounds _) -> 3 in
  let offsets = ref [] and off = ref (List.length l.imports) in
  List.iter
    (fun (fo : Lower.func_out) ->
      let fname = fo.fo_func.fname in
      try
        let gf = flatten fo in
        let n = Array.length gf.nodes in
        offsets := (fname, !off, (match gf.labels_at with [||] -> [] | a -> a.(0))) :: !offsets;
        off := !off + Array.fold_left (fun acc nd -> acc + words_of nd) 0 gf.nodes;
        if n = 0 then bad "no instruction";
        (* The frame. *)
        let fr = fo.fo_frame in
        let slots = Array.of_list fr.slots in
        Array.iteri
          (fun k (o, sz) ->
            if sz <> 4 && sz <> 8 then err "%s: frame slot %d of %d bytes" fname k sz;
            if o < 0 || o + sz > fr.fbytes then err "%s: frame slot %d (byte %d) outside the %d-byte frame" fname k o fr.fbytes;
            if k > 0 && fst slots.(k - 1) + snd slots.(k - 1) > o then err "%s: frame slots %d and %d overlap or are unsorted" fname (k - 1) k)
          slots;
        (* Control flow, liveness, values. *)
        let sx = Array.init n (succs gf) in
        let lout = liveness gf sx in
        Array.iter
          (fun nd -> if live cgp (snd (uses_defs nd)) then bad "cgp written by %s" (string_of_node nd))
          gf.nodes;
        let get st = function G.R r -> if r = cnull then Const 0 else st.(r) | G.E (G.Z k) -> Const k | G.E _ -> Top in
        let transfer st nd =
          let st = Array.copy st in
          let set r v = if r <> cnull then st.(r) <- v in
          (match nd with
           | M (G.Fetch (_, r)) -> set r Top
           | M (G.Setbounds (d, s, w, t1, t2)) ->
               let v =
                 match get st (G.R s) with
                 | Cap ({ glob = Some g; _ } as c) ->
                     let whole = match glob_named g with Some gl -> gl.words = w | None -> false in
                     Cap { c with glob = (if whole then Some g else None) }
                 | Cap c -> Cap { c with glob = None }
                 | _ -> Top
               in
               set t1 (Int false);
               set t2 (Int false);
               set d v
           | I i -> (
               match i with
               | G.Mov (d, x) -> set d (get st x)
               | G.Add (d, x, y) ->
                   set d
                     (match (get st x, get st y) with
                      | Const a, Const b when fits32 (a + b) -> Const (a + b)
                      | ((Int _ | Const _) as v), Const 0 -> v
                      | _ -> Int false)
               | G.LShiftL (d, x, y) ->
                   set d
                     (match (get st x, get st y) with
                      | Const c, Const k when k >= 0 && k < 32 && fits32 (c lsl k) -> Const (c lsl k)
                      | _ -> Int false)
               | G.Sub (d, _, _) | G.Mul (d, _, _) | G.LAnd (d, _, _) | G.LOr (d, _, _) | G.LShiftR (d, _, _) -> set d (Int false)
               | G.Lt (d, _, _) | G.Le (d, _, _) -> set d (Int true)
               | G.Lea (d, s, G.E (G.Z k)) when s = cgp ->
                   set d (Cap { bits = cgp_bits; glob = Option.map (fun g -> g.name) (glob_at k) })
               | G.Restrict (d, s, G.E (G.Perm p)) ->
                   set d (match get st (G.R s) with Cap c -> Cap { c with bits = bits_of_pair p } | _ -> Top)
               | G.GetB (d, _) | G.GetE (d, _) | G.GetLen (d, _) | G.GetA (d, _) | G.GetP (d, _) | G.GetL (d, _)
               | G.GetWType (d, _) | G.GetOType (d, _) | G.GetTag (d, _) ->
                   set d (Int false)
               | G.Jalr (d, _) when d = cra -> List.iter (fun r -> if live r call_defs then st.(r) <- Top) (List.init 16 Fun.id)
               | _ -> List.iter (fun r -> if live r (snd (uses_defs nd)) then st.(r) <- Top) (List.init 16 Fun.id)));
          st
        in
        let vals = Array.make n None in
        vals.(0) <- Some (Array.init 16 (fun r -> if r = cnull then Const 0 else Top));
        let work = Queue.create () in
        Queue.add 0 work;
        while not (Queue.is_empty work) do
          let i = Queue.pop work in
          match vals.(i) with
          | None -> ()
          | Some st ->
              let o = transfer st gf.nodes.(i) in
              List.iter
                (fun s ->
                  let nw = match vals.(s) with None -> o | Some old -> Array.init 16 (fun r -> join old.(r) o.(r)) in
                  if vals.(s) <> Some nw then (
                    vals.(s) <- Some nw;
                    Queue.add s work))
                sx.(i)
        done;
        (* {3 The inverse rules} *)
        let regof = function G.R r -> Some r | G.E (G.Z 0) -> Some cnull | _ -> None in
        let reg_or what x = match regof x with Some r -> r | None -> bad "%s: %s is not a register" what (G.string_of_arg x) in
        let lbl_or x = match label_of x with Some l -> l | None -> bad "jump to %s, not a label" (G.string_of_arg x) in
        let cond b fmt = Printf.ksprintf (fun s -> if b then None else Some s) fmt in
        let no_label_at k = cond (gf.labels_at.(k) = []) "a label (%s) inside a sequence that is one CHERIoT instruction" (String.concat " " gf.labels_at.(k)) in
        let slot w =
          if w < 0 || w >= Array.length slots then bad "word %d outside the %d-word frame" w (Array.length slots) else slots.(w)
        in
        (* The byte offset of word w from s, and the slot size (sp only). *)
        let offset s w =
          if s = csp then
            let o, sz = slot w in
            (o, Some sz)
          else if w = 0 then (0, None)
          else bad "word offset %d from %s, an object of unknown layout" w (G.string_of_reg s)
        in
        let mem_of s w = PMem (imm (fst (offset s w)), s) in
        let size_ok s w want = match snd (offset s w) with None -> true | Some sz -> sz = want in
        let call_ok i r =
          let fetch k reg =
            if k < 0 then None
            else match gf.nodes.(k) with M (G.Fetch (sym, r')) when r' = reg -> Result.to_option (decode sym) | _ -> None
          in
          let kind isym = (List.find (fun (im : Classify.import) -> im.isym = isym) src.imports).ikind in
          match fetch (i - 1) r with
          | Some ".compartment_switcher" ->
              if r = ct1 then Some "the switcher fetched into ct1, which holds the target"
              else if gf.labels_at.(i) <> [] || gf.labels_at.(i - 1) <> [] then Some "a label inside the call sequence"
              else (
                match fetch (i - 2) ct1 with
                | Some s -> (match kind s with Classify.Cross_call _ -> None | _ -> Some ("the target in ct1 is " ^ s ^ ", not an export"))
                | None -> (
                    match if i >= 2 then gf.nodes.(i - 2) else I G.Halt with
                    | I (G.Mov (d, G.R x)) when d = ct1 && x <> ct1 && x <> cnull -> None
                    | _ -> Some "a switcher call without its target fetched or moved into ct1 right before"))
          | Some s -> (
              match kind s with
              | Classify.Library_call _ -> if gf.labels_at.(i) <> [] then Some "a label inside the call sequence" else None
              | _ -> Some (Printf.sprintf "a call through %s, neither the switcher nor a library" s))
          | None -> Some (Printf.sprintf "a call through %s, not fetched from an import right before" (G.string_of_reg r))
        in
        let inverse i : cand list =
          let st = match vals.(i) with Some st -> st | None -> Array.make 16 Top in
          let v x = get st x in
          let next = if i + 1 < n then Some gf.nodes.(i + 1) else None in
          let c1 ?(conds = []) out = { take = 1; out; conds } in
          let c2 ?(conds = []) out = { take = 2; out; conds = no_label_at (i + 1) :: conds } in
          let r x = PReg (reg_or "operand" x) in
          match gf.nodes.(i) with
          | M (G.Fetch (sym, reg)) -> (
              match decode sym with
              | Ok isym -> [ c1 [ ("ct.auipcc", [ PReg reg; PRel (C.Hi, isym) ]); ("ct.clc", [ PReg reg; PMem (PLoSelf, reg) ]) ] ]
              | Error e -> bad "%s" e)
          | M (G.Setbounds (d, s, w, t1, t2)) ->
              let lo = lout.(i) in
              let scratch t =
                cond (t <> cnull && t <> s && (t = d || not (live t lo))) "scratch %s: cnull, the source, or live after"
                  (G.string_of_reg t)
              in
              let len, lconds =
                match v (G.R s) with
                | Cap { glob = Some g; _ } -> (
                    match glob_named g with
                    | Some gl ->
                        let bytes = w * gl.elem in
                        ( Some bytes,
                          [ cond (w > 0 && w <= gl.words) "%d words, outside the %d-word global %s" w gl.words g;
                            cond (bytes < 512) "%d bytes: CHERIoT's bounds are exact only below 512" bytes ] )
                    | None -> (None, [ Some ("unknown global " ^ g) ]))
                | _ ->
                    ( None,
                      [ Some
                          (Printf.sprintf "%s not known to hold the start of a global: its words cannot be turned back to bytes"
                             (G.string_of_reg s)) ] )
              in
              [ c1 ~conds:([ scratch t1; scratch t2; cond (t1 <> t2) "the same scratch register twice" ] @ lconds)
                  [ ("ct.csetbounds", [ PReg d; PReg s; PLen len ]) ] ]
          | I ins -> (
              match ins with
              | G.Mov (d, G.R s) -> [ c1 [ ("ct.cmove", [ PReg d; PReg s ]) ] ]
              | G.Mov (d, G.E (G.Z k)) ->
                  [ c1 [ ("li", [ PReg d; imm32 k ]) ];
                    c1
                      [ ( "lui",
                          [ PReg d;
                            PImm (Printf.sprintf "%d >> 12" k, fun m -> m >= 0 && m < 0x100000 && signed32 (m lsl 12) = k) ] ) ] ]
                  @ if k = 0 then [ c1 [ ("ct.cmove", [ PReg d; PReg cnull ]) ] ] else []
              | G.Add (d, x, G.E (G.Z k)) ->
                  (c1 [ ("addi", [ PReg d; r x; imm k ]) ] :: if k = 0 then [ c1 [ ("mv", [ PReg d; r x ]) ] ] else [])
                  @ if k = 0 then [ c1 [ ("add", [ PReg d; r x; PReg cnull ]) ] ] else []
              | G.Add (d, x, y) -> [ c1 [ ("add", [ PReg d; r x; r y ]) ] ]
              | G.LShiftL (d, x, G.E (G.Z k)) ->
                  [ c1
                      ~conds:
                        [ cond
                            (match v x with Const c -> k >= 0 && k < 32 && fits32 (c lsl k) | _ -> false)
                            "slli of a value not known to be a constant within 32 bits" ]
                      [ ("slli", [ PReg d; r x; imm k ]) ] ]
              | G.Jmp x -> [ c1 [ ("j", [ PTarget (lbl_or x) ]) ] ]
              | G.Jeq (o, x, y) ->
                  c1 [ ("beq", [ r x; r y; PTarget (lbl_or o) ]) ]
                  :: (if y = G.E (G.Z 0) then [ c1 [ ("beqz", [ r x; PTarget (lbl_or o) ]) ] ] else [])
              | G.Jne (o, x, y) ->
                  c1 [ ("bne", [ r x; r y; PTarget (lbl_or o) ]) ]
                  :: (if y = G.E (G.Z 0) then [ c1 [ ("bnez", [ r x; PTarget (lbl_or o) ]) ] ] else [])
              | G.Jlt (o, x, y) | G.Jle (o, y, x) ->
                  let m = match ins with G.Jlt _ -> "bltu" | _ -> "bgeu" in
                  let nn a = cond (nonneg (v a)) "%s not known to be non-negative (D5)" (G.string_of_arg a) in
                  [ c1 ~conds:[ nn x; nn y ] [ (m, [ r x; r y; PTarget (lbl_or o) ]) ] ]
              | G.Jalr (d, s) when d = cnull && s = cra -> [ c1 [ ("ct.cret", []) ] ]
              | G.Jalr (d, s) when d = cra -> [ c1 ~conds:[ call_ok i s ] [ ("ct.cjalr", [ PReg s ]) ] ]
              | G.Ecall -> [ c1 [ ("ecall", []) ] ]
              | G.Lea (d, s, G.E (G.Z k)) when d = csp && s = csp ->
                  let nslots = Array.length slots in
                  if fr.fbytes = 0 || (k <> nslots && k <> -nslots) then
                    bad "lea csp csp %d, but the frame has %d slots" k nslots
                  else [ c1 [ ("ct.cincoffset", [ PReg csp; PReg csp; imm (if k < 0 then -fr.fbytes else fr.fbytes) ]) ] ]
              | G.Lea (d, s, G.E (G.Z k)) when s = cgp -> (
                  match glob_at k with
                  | Some g ->
                      [ c1 [ ("ct.auicgp", [ PReg d; PRel (C.Hi, g.name) ]); ("ct.cincoffset", [ PReg d; PReg d; PLoSelf ]) ] ]
                  | None -> bad "lea from cgp to word %d, the start of no global" k)
              | G.Restrict (d, s, G.E (G.Perm p)) ->
                  let want = bits_of_pair p in
                  let src_bits = match v (G.R s) with Cap c -> Some c.bits | _ -> None in
                  let mask m =
                    match (src_bits, v (G.R m)) with
                    | None, _ -> Some (Printf.sprintf "the permissions of %s are unknown" (G.string_of_reg s))
                    | Some sb, Const k ->
                        cond (sb land k land 0xfff = want) "mask %s = %d (%#x): %s & mask = %#x, but the restrict to %s means %#x"
                          (C.string_of_reg m) k (k land 0xfff) (G.string_of_reg s) (sb land k land 0xfff)
                          (Cheriot_perms.string_of_pair p) want
                    | Some _, _ -> Some (Printf.sprintf "the mask %s is not known to be a constant" (C.string_of_reg m))
                  in
                  [ c1 ~conds:[ cond (representable want) "%#x is not representable in CHERIoT" want ]
                      [ ("ct.candperm", [ PReg d; PReg s; PAnyReg mask ]) ] ]
              | G.CLoad (d, s, G.Z w) ->
                  (match next with
                   | Some (I (G.GetA (d', d''))) when d' = d && d'' = d ->
                       [ c2 ~conds:[ cond (size_ok s w 4) "clw of an 8-byte frame slot" ] [ ("ct.clw", [ PReg d; mem_of s w ]) ] ]
                   | _ -> [])
                  @ [ c1 ~conds:[ cond (size_ok s w 8) "clc of a 4-byte frame slot (geta missing?)" ] [ ("ct.clc", [ PReg d; mem_of s w ]) ] ]
              | G.GetA (t, x) -> (
                  match next with
                  | Some (I (G.Store (s, G.R t', G.Z w))) when t' = t ->
                      [ c2
                          ~conds:
                            [ cond (t <> cnull && t <> s && not (live t lout.(i + 1)))
                                "geta scratch %s: cnull, the store's base, or live after the store" (G.string_of_reg t);
                              cond (size_ok s w 4) "csw to an 8-byte frame slot" ]
                          [ ("ct.csw", [ PReg x; mem_of s w ]) ] ]
                  | _ -> bad "geta outside the clw/csw sequences")
              | G.Store (s, x, G.Z w) ->
                  [ c1 ~conds:[ cond (size_ok s w 8) "csc to a 4-byte frame slot" ] [ ("ct.csc", [ r x; mem_of s w ]) ];
                    c1
                      ~conds:
                        [ cond (size_ok s w 4) "csw to an 8-byte frame slot";
                          cond (is_int (v x)) "csw of %s, not known to hold an integer, without geta (D11)" (G.string_of_arg x) ]
                      [ ("ct.csw", [ r x; mem_of s w ]) ] ]
              | _ -> bad "no inverse rule for %s" (G.string_of_instr ins))
        in
        (* {3 The `.s` side} *)
        let sins = Array.of_list (Classify.func_instrs fo.fo_func) in
        let ns = Array.length sins in
        let slabels = Array.make (ns + 1) [] and slabel = Hashtbl.create 16 in
        let k = ref 0 in
        List.iter
          (function
            | Classify.FLabel lb -> slabels.(!k) <- slabels.(!k) @ [ lb ]; Hashtbl.replace slabel lb !k
            | Classify.FInstr _ -> incr k)
          fo.fo_func.fitems;
        (* {3 Matching} *)
        let rec match_op si p (o : C.operand) =
          (* Some (branch targets, conditions) when the operand fits. *)
          match (p, o) with
          | PReg r, C.Reg r' when r = r' -> Some ([], [])
          | PImm (_, f), C.Imm (C.Int m) when f m -> Some ([], [])
          | PRel (k, s), C.Imm (C.Reloc (k', s')) when k = k' && s = s' -> Some ([], [])
          | PLen (Some b), C.Imm (C.Int m) when m = b -> Some ([], [])
          | PLen (Some b), C.Imm (C.Reloc (C.Size, g)) when (match glob_named g with Some gl -> gl.size = b | None -> false) ->
              Some ([], [])
          | PLen None, C.Imm _ -> Some ([], [])
          | PLoSelf, C.Imm (C.Reloc (C.Lo_i, lb)) when si > 0 && List.mem lb slabels.(si - 1) -> Some ([], [])
          | PMem (p', r), C.Mem (im, r') when r = r' -> match_op si p' (C.Imm im)
          | PTarget gl, C.Sym sl -> Some ([ (gl, sl, si) ], [])
          | PAnyReg f, C.Reg r -> Some ([], [ f r ])
          | _ -> None
        in
        let match_ins si ((m, ops) : pins) =
          if si >= ns then None
          else
            let ins = sins.(si) in
            if ins.mnemonic <> m || List.length ins.operands <> List.length ops then None
            else
              List.fold_left2
                (fun acc p o ->
                  match (acc, match_op si p o) with
                  | Some (t, c), Some (t', c') -> Some (t @ t', c @ c')
                  | _ -> None)
                (Some ([], [])) ops ins.operands
        in
        let match_cand si (c : cand) =
          let rec go si acc = function
            | [] -> acc
            | p :: rest -> (
                match (acc, match_ins si p) with
                | Some (t, cs), Some (t', cs') -> go (si + 1) (Some (t @ t', cs @ cs')) rest
                | _ -> None)
          in
          Option.map (fun (t, cs) -> (t, c.conds @ cs)) (go si (Some ([], [])) c.out)
        in
        let align = Hashtbl.create 64 and targets = ref [] and nconds = ref 0 in
        let sline si = if si < ns then Printf.sprintf ".s line %d (%s)" sins.(si).iloc.line (C.string_of_instr sins.(si)) else "the end of the .s function" in
        let rec walk gi si =
          if gi >= n then (
            if si < ns then err "%s: %s and after: no Griotte code left" fname (sline si))
          else
            let cands = inverse gi in
            let matched = List.filter_map (fun c -> Option.map (fun r -> (c, r)) (match_cand si c)) cands in
            let ok (_, (_, cs)) = List.for_all Option.is_none cs in
            match (List.filter ok matched, matched) with
            | [], [] ->
                err "%s: Griotte %s inverts to %s; the .s has %s" fname (string_of_node gf.nodes.(gi))
                  (String.concat " | " (List.map (fun c -> String.concat "; " (List.map string_of_pins c.out)) cands))
                  (sline si)
            | (c, (t, cs)) :: _, _ | [], (c, (t, cs)) :: _ ->
                List.iter
                  (function
                    | Some why -> err "%s: Griotte %s, %s: %s" fname (string_of_node gf.nodes.(gi)) (sline si) why
                    | None -> incr nconds)
                  cs;
                Hashtbl.replace align gi si;
                targets := t @ !targets;
                walk (gi + c.take) (si + List.length c.out)
        in
        walk 0 0;
        List.iter
          (fun (gl, sl, si) ->
            match (Hashtbl.find_opt gf.glabel gl, Hashtbl.find_opt slabel sl) with
            | Some gi, Some sj -> (
                match Hashtbl.find_opt align gi with
                | Some sj' when sj' = sj -> ()
                | _ -> err "%s: %s: the Griotte target %s is not the instruction at %s" fname (sline si) gl sl)
            | _ -> err "%s: %s: unknown target %s / %s" fname (sline si) gl sl)
          !targets;
        say "function %s: %d Griotte instructions/macros back to %d CHERIoT instructions; %d branch target(s) aligned; %d side condition(s) hold"
          fname n ns (List.length !targets) !nconds
      with Bad m -> err "%s: %s" fname m)
    l.funcs;
  (* {2 Exports} *)
  List.iter
    (fun (e : Lower.export_out) ->
      match List.find_opt (fun (f, _, _) -> f = e.ex.efunc) !offsets with
      | None -> err "export %s: no function %s" e.ex.esym e.ex.efunc
      | Some (_, o, labels) ->
          if not (List.mem e.ex_label labels) then err "export %s: entry %s is not the first label of %s" e.ex.esym e.ex_label e.ex.efunc;
          if o <> e.ex_offset then err "export %s: word offset %d, but %s starts at word %d" e.ex.esym e.ex_offset e.ex.efunc o)
    l.exports;
  say "exports: %d, each at the entry label and word offset of its function" (List.length l.exports);
  { log = List.rev !log; errors = List.rev !errors }

let print (r : result) =
  List.iter print_endline r.log;
  List.iter (fun e -> print_endline ("mismatch: " ^ e)) r.errors;
  print_endline (if r.errors = [] then "reverse map: OK" else Printf.sprintf "reverse map: %d mismatch(es)" (List.length r.errors))
