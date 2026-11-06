(* Lowering: from a classified `.s` file (Classify.t) to Griotte assembly
   (Griotte_asm), cut into blocks, for the in-scope subset only. Anything
   the tool cannot translate soundly is an error naming the file, the line
   and the CHERIoT instruction.

   Passes, per function:
   1. [nodes]: the instructions, with each %cheriot_compartment_hi/lo_i
      pair (Classify) merged into one node ([Fetch] of an import, [Gaddr]
      of a global), and the supported subset checked.
   2. Control flow: fall-through, branch targets, [ct.cret] exits;
      [ct.cjalr] is a call that returns to the next instruction.
   3. Liveness (backward), to choose scratch registers (D3, D11).
   4. Integer values (forward): which registers hold an integer, a
      constant, or a non-negative integer, in the translated code (D5,
      D11).
   5. Stack frame (forward): the offset of [sp] from its value at entry;
      frames only through constant [sp] offsets (D6).
   6. Translation of each node, block cuts and generated labels (D8).

   Conventions of the translation (see also setbounds.v, fetch.v):
   - Registers: the bijection zero->cnull, ra->cra, ..., a5->ca5 (same
     numbering on both sides).
   - Calls. A [ct.cjalr r] must jump to a sentry fetched right before it
     from the switcher import (a cross-compartment call, target in t1) or
     from a library import (a library call). The target in t1 is fetched
     from an import right before the switcher fetch, or (a callback: a
     sealed capability received as an argument) moved there from another
     register by a [ct.cmove t1, r] right before it. For liveness, a call reads
     its jump register, t1, a0-a5, sp, gp, tp, s0, s1, and clobbers ra,
     t0-t2, a0-a5 (the CHERIoT calling convention: t0 is never an argument;
     the switcher overwrites ct0 before reading it and zeroes it for the
     callee). [ct.cret] reads ra, sp, gp, tp, s0, s1, a0, a1.
   - Scratch registers are taken, in this order, among t0, t1, t2, a5, a4,
     a3, a2, a1, a0 that are dead after the instruction (never read before
     being written again, on every path).
   - Integer accesses (D11, review R6): CHERIoT's [mv], [ct.clw] and
     [ct.csw] drop the tag; Griotte's [Mov], [CLoad] and [Store] copy whole
     words. [mv r, s] -> [add r s 0]; [ct.clw r, o(s)] -> [load_imm r s o'],
     then [geta r r]; [ct.csw v, o(s)] -> [geta t v], then [store_imm s t
     o'], the [geta] skipped when [v] is known to hold an integer (zero, a
     constant, the result of an arithmetic instruction or of a [geta]).
   - Layout (D6): the frame of a function gets one word per stack slot
     (an [sp] offset accessed by a load or a store), in offset order; the
     [sp] adjustments are rescaled to the number of slots. Globals get one
     word per 4-byte integer, in section order ([.data], then [.bss]);
     only globals whose element type is known to be a 4-byte integer are
     accepted, or a single null capability ([.chericap 0], one word).
     Accesses through other pointers must be at offset 0.
   - Permissions: a capability derived from [cgp] (auicgp pair, then
     csetbounds) has cgp's permissions (RW, Global); [ct.candperm] with a
     mask known to be a constant (li, lui, addi) on such a capability is a
     [restrict] to the exact Griotte counterpart of the remaining CHERIoT
     permissions (Cheriot_perms), or an error.
   - [ecall] (yield, inline assembly) is Griotte's [ecall]; registers are
     preserved across it. *)

open Cheriot_ast
module G = Griotte_asm

(* {1 Nodes} *)

type op =
  | Ins of instr
  | Fetch of { reg : reg; imp : string; hi : instr; lo : instr }
  | Gaddr of { reg : reg; glob : string; hi : instr; lo : instr }

type node = { op : op; src_labels : string list }

let op_loc = function Ins i -> i.iloc | Fetch { hi; _ } | Gaddr { hi; _ } -> hi.iloc

let op_texts = function
  | Ins i -> [ string_of_instr i ]
  | Fetch { hi; lo; _ } | Gaddr { hi; lo; _ } -> [ string_of_instr hi; string_of_instr lo ]

let fail op fmt =
  Printf.ksprintf
    (fun msg -> Diag.error (op_loc op) "cannot translate %s: %s" (String.concat "; " (op_texts op)) msg)
    fmt

let nodes_of_func (f : Classify.func) =
  let rec go acc labels = function
    | [] -> List.rev acc
    | Classify.FLabel l :: rest -> go acc (l :: labels) rest
    | Classify.FInstr hi :: rest -> (
        match (hi.mnemonic, hi.operands) with
        | ("ct.auipcc" | "ct.auicgp"), [ Reg r; Imm (Reloc (Hi, sym)) ] -> (
            match rest with
            | Classify.FInstr lo :: rest' ->
                let op =
                  if hi.mnemonic = "ct.auipcc" then Fetch { reg = r; imp = sym; hi; lo }
                  else Gaddr { reg = r; glob = sym; hi; lo }
                in
                go ({ op; src_labels = List.rev labels } :: acc) [] rest'
            | _ -> Diag.error hi.iloc "%%cheriot_compartment_hi not followed by its lo_i")
        | _ -> go ({ op = Ins hi; src_labels = List.rev labels } :: acc) [] rest)
  in
  Array.of_list (go [] [] f.fitems)

(* {1 Registers} *)

let zero = 0 and ra = 1 and sp = 2 and gp = 3 and tp = 4
let t0 = 5 and t1 = 6 and t2 = 7 and s0 = 8 and s1 = 9
let a_regs = [ 10; 11; 12; 13; 14; 15 ]

let bit r = if r = zero then 0 else 1 lsl r
let set l = List.fold_left (fun acc r -> acc lor bit r) 0 l
let mem r s = s land bit r <> 0

let call_uses jr = set ([ jr; t1; sp; gp; tp; s0; s1 ] @ a_regs)
let call_defs = set ([ ra; t0; t1; t2 ] @ a_regs)
let exit_uses = set [ ra; sp; gp; tp; s0; s1; 10; 11 ]

(* The scratch registers, in order of preference. *)
let scratch_order = [ t0; t1; t2; 15; 14; 13; 12; 11; 10 ]

(* {1 The supported subset, with uses and definitions} *)

let int_imm op = function Imm (Int n) -> n | _ -> fail op "expected an integer immediate"

let target_of op = function Sym t -> t | _ -> fail op "expected a label"

(* Registers read and written by a node. Fails on anything outside the
   subset. *)
let uses_defs (n : node) =
  match n.op with
  | Fetch { reg; _ } -> (0, set [ reg ])
  | Gaddr { reg; _ } -> (set [ gp ], set [ reg ])
  | Ins i -> (
      let op = n.op in
      match (i.mnemonic, i.operands) with
      | ("li" | "lui"), [ Reg d; Imm (Int _) ] -> (0, set [ d ])
      | "ecall", [] -> (0, 0)
      | "ct.candperm", [ Reg d; Reg x; Reg m ] -> (set [ x; m ], set [ d ])
      | ("mv" | "ct.cmove"), [ Reg d; Reg s ] -> (set [ s ], set [ d ])
      | ("addi" | "slli"), [ Reg d; Reg s; Imm (Int _) ] -> (set [ s ], set [ d ])
      | "add", [ Reg d; Reg x; Reg y ] -> (set [ x; y ], set [ d ])
      | ("beq" | "bne" | "bltu" | "bgeu"), [ Reg x; Reg y; Sym _ ] -> (set [ x; y ], 0)
      | ("beqz" | "bnez"), [ Reg x; Sym _ ] -> (set [ x ], 0)
      | "j", [ Sym _ ] -> (0, 0)
      | "ct.cret", [] -> (exit_uses, 0)
      | "ct.cjalr", [ Reg r ] -> (call_uses r, call_defs)
      | "ct.cincoffset", [ Reg d; Reg s; Imm (Int _) ] -> (set [ s ], set [ d ])
      | "ct.csetbounds", [ Reg d; Reg s; Imm _ ] -> (set [ s ], set [ d ])
      | ("ct.clc" | "ct.clw"), [ Reg d; Mem (Int _, s) ] -> (set [ s ], set [ d ])
      | ("ct.csc" | "ct.csw"), [ Reg v; Mem (Int _, s) ] -> (set [ v; s ], 0)
      | _ -> fail op "not in the subset the lowering supports")

(* {1 Control flow} *)

type cfg = {
  nodes : node array;
  label_index : (string, int) Hashtbl.t;  (* source label -> node; n at the end *)
  succs : int list array;
  uses : int array;
  defs : int array;
}

let build_cfg (f : Classify.func) =
  let nodes = nodes_of_func f in
  let n = Array.length nodes in
  let label_index = Hashtbl.create 16 in
  Array.iteri (fun i nd -> List.iter (fun l -> Hashtbl.replace label_index l i) nd.src_labels) nodes;
  (* Labels after the last instruction (.Lfunc_end0). *)
  List.iter
    (function Classify.FLabel l when not (Hashtbl.mem label_index l) -> Hashtbl.replace label_index l n | _ -> ())
    f.fitems;
  let idx op t =
    match Hashtbl.find_opt label_index t with
    | Some k when k < n -> k
    | _ -> fail op "branch to %s, which is not an instruction of %s" t f.fname
  in
  let ud = Array.map uses_defs nodes in
  let succs =
    Array.mapi
      (fun i nd ->
        let next () = if i + 1 < n then [ i + 1 ] else fail nd.op "control falls off the end of %s" f.fname in
        match nd.op with
        | Ins { mnemonic = "j"; operands = [ t ]; _ } -> [ idx nd.op (target_of nd.op t) ]
        | Ins { mnemonic = "beq" | "bne" | "bltu" | "bgeu"; operands = [ _; _; t ]; _ }
        | Ins { mnemonic = "beqz" | "bnez"; operands = [ _; t ]; _ } ->
            List.sort_uniq compare (next () @ [ idx nd.op (target_of nd.op t) ])
        | Ins { mnemonic = "ct.cret"; _ } -> []
        | _ -> next ())
      nodes
  in
  { nodes; label_index; succs; uses = Array.map fst ud; defs = Array.map snd ud }

(* {1 Liveness} *)

(* live_out.(i): the registers read after node i before being written. *)
let liveness cfg =
  let n = Array.length cfg.nodes in
  let live_in = Array.make n 0 and live_out = Array.make n 0 in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = n - 1 downto 0 do
      let out = List.fold_left (fun acc s -> acc lor live_in.(s)) 0 cfg.succs.(i) in
      let inn = cfg.uses.(i) lor (out land lnot cfg.defs.(i)) in
      if out <> live_out.(i) || inn <> live_in.(i) then (
        live_out.(i) <- out;
        live_in.(i) <- inn;
        changed := true)
    done
  done;
  live_out

(* {1 Integer values} *)

(* The value of a register in the translated code: unknown (possibly a
   capability), an integer (known non-negative or not), a constant, or a
   capability of known Griotte permissions, whose address is at the start
   of the global [glob] (with bounds that contain it) when known. *)
type capv = { perm : Cheriot_perms.pair; glob : string option }

type value = Top | Int of bool | Const of int | Cap of capv

let signed32 n =
  let n = n land 0xffffffff in
  if n >= 0x80000000 then n - 0x100000000 else n

let fits32 n = n >= -0x80000000 && n < 0x80000000

let is_int = function Top | Cap _ -> false | Int _ | Const _ -> true
let nonneg = function Top | Cap _ -> false | Int b -> b | Const c -> c >= 0

let join a b =
  match (a, b) with
  | Const x, Const y when x = y -> Const x
  | Cap x, Cap y when x.perm = y.perm -> Cap { perm = x.perm; glob = (if x.glob = y.glob then x.glob else None) }
  | _ when is_int a && is_int b -> Int (nonneg a && nonneg b)
  | _ -> Top

let read st r = if r = zero then Const 0 else st.(r)

(* [lui d, n]: n << 12, as a signed 32-bit integer. *)
let lui_value n = signed32 (n lsl 12)
let lui_ok n = n >= 0 && n < 0x100000

(* The result of [ct.candperm] of [s] with the mask in [m], when both are
   known. *)
let candperm_result st s m =
  match (read st s, read st m) with
  | Cap c, Const k -> Some (c, k, Cheriot_perms.and_perm c.perm k)
  | _ -> None

(* [gsize g]: the size in bytes of the global [g]. *)
let transfer ~gsize (st : value array) (nd : node) =
  let st = Array.copy st in
  let set r v = if r <> zero then st.(r) <- v in
  (match nd.op with
   | Fetch { reg; _ } -> set reg Top
   | Gaddr { reg; glob; _ } -> set reg (Cap { perm = Cheriot_perms.cgp_perms; glob = Some glob })
   | Ins i -> (
       match (i.mnemonic, i.operands) with
       | "li", [ Reg d; Imm (Int n) ] -> set d (Const (signed32 n))
       | "lui", [ Reg d; Imm (Int n) ] -> set d (if lui_ok n then Const (lui_value n) else Int false)
       | "mv", [ Reg d; Reg s ] -> set d (match read st s with Top | Cap _ -> Int false | v -> v)
       | "ct.cmove", [ Reg d; Reg s ] -> set d (read st s)
       | "addi", [ Reg d; Reg s; Imm (Int n) ] ->
           set d (match read st s with Const c when fits32 (c + n) -> Const (c + n) | _ -> Int false)
       | "add", [ Reg d; Reg x; Reg y ] ->
           set d (match (read st x, read st y) with Const a, Const b when fits32 (a + b) -> Const (a + b) | _ -> Int false)
       | "slli", [ Reg d; Reg s; Imm (Int k) ] ->
           (* checked in the translation: s is a constant and no overflow *)
           set d (match read st s with Const c when k >= 0 && k < 32 && fits32 (c lsl k) -> Const (c lsl k) | _ -> Int false)
       | "ct.clw", [ Reg d; _ ] -> set d (Int false)
       | "ct.csetbounds", [ Reg d; Reg s; Imm len ] ->
           (* bounds [a, a + len): still the whole global when len is its size *)
           set d
             (match read st s with
              | Cap ({ glob = Some g; _ } as c) ->
                  let whole = match len with Reloc (Size, g') -> g' = g | Int n -> Some n = gsize g | _ -> false in
                  Cap { c with glob = (if whole then Some g else None) }
              | Cap c -> Cap { c with glob = None }
              | _ -> Top)
       | "ct.candperm", [ Reg d; Reg s; Reg m ] ->
           set d (match candperm_result st s m with Some (c, _, Ok p) -> Cap { c with perm = p } | _ -> Top)
       | ("ct.clc" | "ct.cincoffset" | "ct.csetbounds"), Reg d :: _ -> set d Top
       | "ct.cjalr", _ -> for r = 1 to 15 do if mem r call_defs then st.(r) <- Top done
       | _ -> ()));
  st

(* The value of each register before each node. *)
let values ~gsize cfg =
  let n = Array.length cfg.nodes in
  let before = Array.make n None in
  if n > 0 then before.(0) <- Some (Array.init 16 (fun r -> if r = zero then Const 0 else Top));
  let work = Queue.create () in
  if n > 0 then Queue.add 0 work;
  while not (Queue.is_empty work) do
    let i = Queue.pop work in
    match before.(i) with
    | None -> ()
    | Some st ->
        let out = transfer ~gsize st cfg.nodes.(i) in
        List.iter
          (fun s ->
            let nw =
              match before.(s) with None -> out | Some old -> Array.init 16 (fun r -> join old.(r) out.(r))
            in
            if before.(s) <> Some nw then (
              before.(s) <- Some nw;
              Queue.add s work))
          cfg.succs.(i)
  done;
  before

(* {1 Stack frame} *)

type frame = {
  fbytes : int;  (* N of ct.cincoffset sp, sp, -N; 0 without frame *)
  slots : (int * int) list;  (* (byte offset, size), sorted *)
  sp_before : int option array;  (* sp - sp at entry, before each node *)
}

let slot_word fr op off =
  let rec find k = function
    | [] -> fail op "no frame slot at byte offset %d" off
    | (o, _) :: _ when o = off -> k
    | _ :: rest -> find (k + 1) rest
  in
  find 0 fr.slots

let frame_words fr = List.length fr.slots

let frame_analysis fname cfg =
  let n = Array.length cfg.nodes in
  let before = Array.make n None in
  let fbytes = ref None in
  let slots = ref [] in
  if n > 0 then before.(0) <- Some 0;
  let work = Queue.create () in
  if n > 0 then Queue.add 0 work;
  let frame_size op = match !fbytes with Some f -> f | None -> fail op "stack access without a frame" in
  while not (Queue.is_empty work) do
    let i = Queue.pop work in
    let nd = cfg.nodes.(i) in
    let op = nd.op in
    let d = Option.get before.(i) in
    (* sp as a value: only as a memory base or in the frame adjustment. *)
    let after =
      match op with
      | Ins { mnemonic = "ct.cincoffset"; operands = [ Reg 2; Reg 2; Imm (Int k) ]; _ } ->
          if d = 0 && k < 0 && (!fbytes = None || !fbytes = Some (-k)) then (
            fbytes := Some (-k);
            k)
          else if !fbytes = Some k && d = -k then 0
          else fail op "sp adjustment other than the frame allocation and release (D6)"
      | Ins { mnemonic = ("ct.clc" | "ct.clw" | "ct.csc" | "ct.csw") as m; operands = [ Reg v; Mem (Int o, 2) ]; _ } ->
          let f = frame_size op in
          if d <> -f then fail op "stack access outside the frame";
          if (m = "ct.csc" || m = "ct.csw") && v = sp then fail op "sp stored to memory (D6)";
          if (m = "ct.clc" || m = "ct.clw") && v = sp then fail op "sp loaded from memory (D6)";
          let size = if m = "ct.clc" || m = "ct.csc" then 8 else 4 in
          if o < 0 || o + size > f then fail op "stack slot %d..%d outside the %d-byte frame" o (o + size) f;
          slots := (o, size) :: !slots;
          d
      | Ins { mnemonic = "ct.cret"; _ } ->
          if d <> 0 then fail op "return with the frame still allocated";
          d
      | Ins { mnemonic = "ct.cjalr"; _ } -> d
      | _ ->
          if mem sp cfg.uses.(i) || mem sp cfg.defs.(i) then
            fail op "sp used other than as the base of a frame access (D6: escaping stack objects need a layout)";
          d
    in
    List.iter
      (fun s ->
        match before.(s) with
        | None -> before.(s) <- Some after; Queue.add s work
        | Some d' when d' = after -> ()
        | Some _ -> fail cfg.nodes.(s).op "sp differs between the paths reaching this instruction (D6)")
      cfg.succs.(i)
  done;
  let slots = List.sort_uniq compare !slots in
  let rec check = function
    | (o1, s1) :: ((o2, _) :: _ as rest) ->
        if o1 + s1 > o2 then
          Diag.error (op_loc cfg.nodes.(0).op) "%s: overlapping stack slots at bytes %d and %d (D6)" fname o1 o2;
        check rest
    | _ -> ()
  in
  check slots;
  { fbytes = Option.value ~default:0 !fbytes; slots; sp_before = before }

(* {1 Globals} *)

type gslot = { gl : Classify.global; gword : int; gwords : int; ginit_words : int list; gcap : bool }

(* One word per 4-byte integer. A global is accepted when its element type
   is known to be a 4-byte integer: it is 4 bytes long (a capability takes
   8), or all its data are [.word] constants. A global that is exactly one
   null capability ([.chericap 0]) is one word, initially [WInt 0] (the
   null capability of Griotte). *)
let globals_layout (t : Classify.t) =
  let order = List.filter (fun g -> not g.Classify.gbss) t.globals @ List.filter (fun g -> g.Classify.gbss) t.globals in
  let words_of (g : Classify.global) =
    match g.ginit with
    | [ Chericap (Num 0) ] -> [ 0 ]
    | _ when List.exists (function Chericap _ -> true | _ -> false) g.ginit ->
        Diag.error g.gloc "global %s: a capability other than a single null [.chericap 0] (D6)" g.gname
    | _ ->
    let consts = List.map (function Word (Num n) -> Some (signed32 n) | Zero 4 -> Some 0 | _ -> None) g.ginit in
    if g.gsize = 4 || List.for_all (function Word (Num _) -> true | _ -> false) g.ginit then
      if List.exists Option.is_none consts || g.gsize mod 4 <> 0 then
        Diag.error g.gloc "global %s: data other than 4-byte integers (D6)" g.gname
      else List.map Option.get consts
    else Diag.error g.gloc "global %s: element type unknown (%d bytes of %s data); only 4-byte integers are laid out (D6)"
        g.gname g.gsize (if g.gbss then ".bss" else ".data")
  in
  let _, l =
    List.fold_left
      (fun (w, acc) g ->
        let ws = words_of g in
        let gcap = match g.ginit with [ Chericap _ ] -> true | _ -> false in
        (w + List.length ws, { gl = g; gword = w; gwords = List.length ws; ginit_words = ws; gcap } :: acc))
      (0, []) order
  in
  List.rev l

(* {1 Imports} *)

let strip_griotte s = if Classify.starts_with "griotte_" s then Classify.drop_prefix "griotte_" s else s

let import_name (i : Classify.import) =
  match i.ikind with
  | Classify.Switcher -> ".Limport_switcher"
  | Library_call f -> ".Limport_" ^ strip_griotte (Demangle.demangle f)
  | Cross_call (c, f) -> ".Limport_" ^ c ^ "_" ^ Demangle.demangle f
  | Shared_object (name, _) -> ".Limport_" ^ strip_griotte name

let find_import (t : Classify.t) sym =
  match List.find_opt (fun (i : Classify.import) -> i.isym = sym) t.imports with
  | Some i -> i
  | None -> failwith ("unknown import " ^ sym)

(* The import table, a data prefix before the code, in every compartment
   and library, as CHERIoT's linker scripts lay it out
   (cheriot-rtos/sdk/{compartment,library}.ldscript: the switcher slot
   first, reserved even when unused, then the other imports, then the
   code). Canonical order of the other imports (the hand-written case
   studies): the library calls, the cross-compartment calls, the shared
   objects; within a kind, by first use in the code, then the unused ones
   in declaration order. *)
let import_order (t : Classify.t) (cfgs : cfg list) =
  let uses =
    List.concat_map
      (fun c -> List.filter_map (fun nd -> match nd.op with Fetch { imp; _ } -> Some imp | _ -> None) (Array.to_list c.nodes))
      cfgs
  in
  let first_use sym =
    let rec go k = function [] -> max_int | s :: r -> if s = sym then k else go (k + 1) r in
    go 0 uses
  in
  let rank (i : Classify.import) =
    match i.ikind with Switcher -> 0 | Library_call _ -> 1 | Cross_call _ -> 2 | Shared_object _ -> 3
  in
  let indexed = List.mapi (fun k i -> (k, i)) t.imports in
  List.map snd
    (List.stable_sort
       (fun (k1, i1) (k2, i2) -> compare (rank i1, first_use i1.Classify.isym, k1) (rank i2, first_use i2.Classify.isym, k2))
       indexed)

(* {1 Translation} *)

(* One translated node: the CHERIoT lines it comes from (provenance), the
   deviations, and the Griotte code. *)
type out = C of G.code | M of G.macro

type lowered = { prov : string list; devs : string list; outs : out list }

let words_of_outs outs =
  List.fold_left (fun acc -> function C (G.Instr _) -> acc + 1 | C _ -> acc | M m -> acc + G.macro_words m) 0 outs

type block = { labels : string list; items : lowered list }

type func_out = {
  fo_func : Classify.func;
  fo_name : string;  (* demangled *)
  fo_entry : string;  (* entry label *)
  fo_blocks : block list;
  fo_frame : frame;
  fo_switcher_calls : bool;
  fo_words : int;
}

let arg_of r = if r = zero then G.E (G.Z 0) else G.R r

let pick_scratch live_out exclude =
  List.filter (fun r -> (not (mem r live_out)) && not (List.mem r exclude)) scratch_order

let lower_func ~prefix ~(t : Classify.t) ~gslots (f : Classify.func) =
  let cfg = build_cfg f in
  let n = Array.length cfg.nodes in
  if n = 0 then Diag.error f.floc "function %s without instructions" f.fname;
  let live_out = liveness cfg in
  let gsize g = Option.map (fun s -> s.gl.Classify.gsize) (List.find_opt (fun s -> s.gl.Classify.gname = g) gslots) in
  let vals = values ~gsize cfg in
  let fr = frame_analysis f.fname cfg in
  let fname = Demangle.demangle f.fname in
  let base =
    match List.find_opt (fun (e : Classify.export) -> e.efunc = f.fname) t.exports with
    | Some e -> ".L" ^ prefix ^ "_" ^ Demangle.demangle e.efunc
    | None -> ".L" ^ prefix ^ "_" ^ fname
  in
  (* {2 Cuts and their labels} *)
  let cuts = Array.make n [] in
  let add_cut i l = if i < n then cuts.(i) <- cuts.(i) @ [ l ] in
  add_cut 0 base;
  if fr.fbytes > 0 then add_cut 0 (base ^ "_prologue");
  let is_fetch_of i reg pred =
    i >= 0
    && match cfg.nodes.(i).op with Fetch { reg = r; imp; _ } -> r = reg && pred (find_import t imp) | _ -> false
  in
  let callee_of i =
    match cfg.nodes.(i).op with
    | Fetch { imp; _ } -> (
        match (find_import t imp).ikind with
        | Classify.Cross_call (c, fn) -> c ^ "_" ^ Demangle.demangle fn
        | Library_call fn -> strip_griotte (Demangle.demangle fn)
        | _ -> assert false)
    | _ -> assert false
  in
  (* The source register of a [ct.cmove t1, r] at node [i], if any. *)
  let move_to_t1 i =
    if i < 0 then None
    else
      match cfg.nodes.(i).op with
      | Ins { mnemonic = "ct.cmove"; operands = [ Reg 6; Reg r ]; _ } when r <> zero && r <> t1 -> Some r
      | _ -> None
  in
  (* Calls: (index of the cjalr, start of the call sequence, kind, callee).
     A callback's callee is the register it comes from. *)
  let calls =
    List.filter_map
      (fun i ->
        match cfg.nodes.(i).op with
        | Ins { mnemonic = "ct.cjalr"; operands = [ Reg r ]; _ } as op ->
            if is_fetch_of (i - 1) r (fun im -> im.ikind = Classify.Switcher) then
              if r = t1 then fail op "switcher fetched into t1, which holds the target"
              else if is_fetch_of (i - 2) t1 (fun im -> match im.ikind with Cross_call _ -> true | _ -> false) then
                Some (i, i - 2, `Cross, callee_of (i - 2))
              else
                match move_to_t1 (i - 2) with
                | Some src -> Some (i, i - 2, `Callback, string_of_reg src)
                | None ->
                    fail op
                      "switcher call without the fetch of its target into t1, or its move into t1 from another register, right before"
            else if is_fetch_of (i - 1) r (fun im -> match im.ikind with Library_call _ -> true | _ -> false) then
              Some (i, i - 1, `Lib, callee_of (i - 1))
            else fail op "indirect call: the jump register is not fetched from an import right before"
        | _ -> None)
      (List.init n Fun.id)
  in
  let count_callee c = List.length (List.filter (fun (_, _, _, c') -> c' = c) calls) in
  let seen = Hashtbl.create 8 in
  List.iter
    (fun (i, start, kind, callee) ->
      let k = 1 + Option.value ~default:0 (Hashtbl.find_opt seen callee) in
      Hashtbl.replace seen callee k;
      let name =
        match kind with
        | `Lib -> callee ^ "_" ^ string_of_int k
        | `Cross | `Callback -> if count_callee callee > 1 then callee ^ "_" ^ string_of_int k else callee
      in
      (match kind with
       | `Lib -> add_cut start (base ^ "_" ^ name)
       | `Cross | `Callback -> add_cut start (base ^ "_call_" ^ name));
      add_cut (i + 1) (base ^ "_return_" ^ name))
    calls;
  (* Epilogues: the reloads from the frame, the release, the return. *)
  let rets =
    List.filter (fun i -> match cfg.nodes.(i).op with Ins { mnemonic = "ct.cret"; _ } -> true | _ -> false) (List.init n Fun.id)
  in
  if fr.fbytes > 0 then
    List.iteri
      (fun k i ->
        let start = ref (i - 1) in
        (match cfg.nodes.(!start).op with
         | Ins { mnemonic = "ct.cincoffset"; operands = [ Reg 2; Reg 2; _ ]; _ } -> ()
         | op -> fail op "return not right after the release of the frame");
        let rec back j =
          if j >= 0 then
            match cfg.nodes.(j).op with
            | Ins { mnemonic = "ct.clc" | "ct.clw"; operands = [ _; Mem (_, 2) ]; _ } -> start := j; back (j - 1)
            | _ -> ()
        in
        back (!start - 1);
        add_cut !start (base ^ "_epilogue" ^ if List.length rets > 1 then "_" ^ string_of_int (k + 1) else ""))
      rets;
  (* Branch targets. *)
  let targets = Array.make n false in
  Array.iteri
    (fun i nd ->
      match nd.op with
      | Ins { mnemonic = "j" | "beq" | "bne" | "bltu" | "bgeu" | "beqz" | "bnez"; operands; _ } ->
          List.iter (function Sym l -> targets.(Hashtbl.find cfg.label_index l) <- true | _ -> ()) operands;
          ignore i
      | _ -> ())
    cfg.nodes;
  let k = ref 0 in
  Array.iteri (fun i b -> if b then (incr k; add_cut i (base ^ "_bb_" ^ string_of_int !k))) targets;
  let target_label op l =
    let i = Hashtbl.find cfg.label_index l in
    match cuts.(i) with [] -> fail op "no generated label at %s" l | x :: _ -> x
  in
  (* {2 Translation of each node} *)
  let gslot op g =
    match List.find_opt (fun s -> s.gl.Classify.gname = g) gslots with
    | Some s -> s
    | None -> fail op "%s is not a global" g
  in
  let mem_word op o s =
    if s = sp then
      let w = slot_word fr op o in
      (w, [ Printf.sprintf "byte offset %d = word %d of the %d-word frame" o w (frame_words fr) ])
    else if o = 0 then (0, [])
    else fail op "offset %d from %s: the layout of the object is unknown (D6)" o (string_of_reg s)
  in
  let switcher_calls = List.exists (fun (_, _, k, _) -> k = `Cross || k = `Callback) calls in
  let callback_starts = List.filter_map (fun (_, start, k, _) -> if k = `Callback then Some start else None) calls in
  let lower_node idx nd =
    let op = nd.op in
    let st = Option.value vals.(idx) ~default:(Array.make 16 Top) in
    let prov =
      match op_texts op with
      | first :: rest ->
          (match nd.src_labels with [] -> first | ls -> String.concat " " (List.map (fun l -> l ^ ":") ls) ^ " " ^ first) :: rest
      | [] -> []
    in
    let mk ?(devs = []) outs = { prov; devs; outs } in
    let ci x = C (G.Instr x) in
    match op with
    | Fetch { reg; imp; _ } -> mk [ M (G.Fetch (import_name (find_import t imp), reg)) ]
    | Gaddr { reg; glob; _ } ->
        let s = gslot op glob in
        mk
          ~devs:[ Printf.sprintf "the auicgp/cincoffset pair is one lea from cgp: %s at word %d of the globals" glob s.gword ]
          [ ci (G.Lea (reg, gp, G.E (G.Z s.gword))) ]
    | Ins i -> (
        let lbl l = G.E (G.Lbl (target_label op l)) in
        match (i.mnemonic, i.operands) with
        | "li", [ Reg d; Imm (Int v) ] -> mk [ ci (G.Mov (d, G.E (G.Z (signed32 v)))) ]
        | "lui", [ Reg d; Imm (Int v) ] ->
            if not (lui_ok v) then fail op "lui immediate outside 0..0xfffff";
            mk
              ~devs:[ Printf.sprintf "lui: the constant %d << 12 = %d (a signed 32-bit integer)" v (lui_value v) ]
              [ ci (G.Mov (d, G.E (G.Z (lui_value v)))) ]
        | "ecall", [] -> mk [ ci G.Ecall ]
        | "ct.cmove", [ Reg d; Reg s ] when List.mem idx callback_starts ->
            mk
              ~devs:
                [ Printf.sprintf
                    "callback: the target of the switcher call is the capability in %s (received as an argument), not an import"
                    (G.string_of_reg s) ]
              [ ci (G.Mov (d, arg_of s)) ]
        | "ct.candperm", [ Reg d; Reg s; Reg m ] -> (
            match candperm_result st s m with
            | None -> (
                match (read st s, read st m) with
                | Cap _, _ -> fail op "candperm with a mask in %s not known to be a constant" (string_of_reg m)
                | _ -> fail op "candperm of %s, a capability of unknown permissions (known: those derived from cgp)" (string_of_reg s))
            | Some (_, _, Error why) -> fail op "candperm: %s" why
            | Some (c, k, Ok p) ->
                let src = Cheriot_perms.to_bits c.perm in
                mk
                  ~devs:
                    [ Printf.sprintf "candperm: %s has the permissions of cgp %s = CHERIoT %s; the mask %s = %d (low 12 bits %#x) keeps %s"
                        (G.string_of_reg s) (Cheriot_perms.string_of_pair c.perm) (Cheriot_perms.string_of_bits src)
                        (G.string_of_reg m) k (k land Cheriot_perms.all)
                        (Cheriot_perms.string_of_bits (src land k land Cheriot_perms.all));
                      Printf.sprintf "restrict to their Griotte counterpart: encodePermPair %s" (Cheriot_perms.string_of_pair p) ]
                  [ ci (G.Restrict (d, s, G.E (G.Perm p))) ])
        | "mv", [ Reg d; Reg s ] -> mk [ ci (G.Add (d, arg_of s, G.E (G.Z 0))) ]
        | "ct.cmove", [ Reg d; Reg s ] -> mk [ ci (G.Mov (d, arg_of s)) ]
        | "addi", [ Reg d; Reg s; Imm (Int v) ] -> mk [ ci (G.Add (d, arg_of s, G.E (G.Z v))) ]
        | "add", [ Reg d; Reg x; Reg y ] -> mk [ ci (G.Add (d, arg_of x, arg_of y)) ]
        | "slli", [ Reg d; Reg s; Imm (Int k) ] -> (
            match read st s with
            | Const c when k >= 0 && k < 32 && fits32 (c lsl k) -> mk [ ci (G.LShiftL (d, arg_of s, G.E (G.Z k))) ]
            | _ -> fail op "slli of a value not known to stay within 32 bits (Griotte integers are unbounded, D14)")
        | "beq", [ Reg x; Reg y; Sym l ] -> mk [ ci (G.Jeq (lbl l, arg_of x, arg_of y)) ]
        | "bne", [ Reg x; Reg y; Sym l ] -> mk [ ci (G.Jne (lbl l, arg_of x, arg_of y)) ]
        | "beqz", [ Reg x; Sym l ] -> mk [ ci (G.Jeq (lbl l, arg_of x, G.E (G.Z 0))) ]
        | "bnez", [ Reg x; Sym l ] -> mk [ ci (G.Jne (lbl l, arg_of x, G.E (G.Z 0))) ]
        | (("bltu" | "bgeu") as m), [ Reg x; Reg y; Sym l ] ->
            List.iter
              (fun r ->
                if not (nonneg (read st r)) then
                  fail op "unsigned comparison of %s, not known to be non-negative (D5)" (string_of_reg r))
              [ x; y ];
            let dev = "signed comparison: both operands are known non-negative" in
            if m = "bltu" then mk ~devs:[ dev ] [ ci (G.Jlt (lbl l, arg_of x, arg_of y)) ]
            else mk ~devs:[ dev ] [ ci (G.Jle (lbl l, arg_of y, arg_of x)) ]
        | "j", [ Sym l ] -> mk [ ci (G.Jmp (lbl l)) ]
        | "ct.cret", [] -> mk [ ci (G.Jalr (zero, ra)) ]
        | "ct.cjalr", [ Reg r ] -> mk [ ci (G.Jalr (ra, r)) ]
        | "ct.cincoffset", [ Reg 2; Reg 2; Imm (Int v) ] ->
            let w = if v < 0 then - frame_words fr else frame_words fr in
            mk
              ~devs:
                [ Printf.sprintf "frame of %d bytes = %d word%s, one per stack slot" fr.fbytes (frame_words fr)
                    (if frame_words fr = 1 then "" else "s") ]
              [ ci (G.Lea (sp, sp, G.E (G.Z w))) ]
        | "ct.cincoffset", _ -> fail op "pointer arithmetic on an object of unknown layout (D6)"
        | "ct.csetbounds", [ Reg d; Reg s; Imm len ] ->
            let bytes, words, ldev =
              match len with
              | Reloc (Size, g) ->
                  let sl = gslot op g in
                  (sl.gl.gsize, sl.gwords, Printf.sprintf "length %%cheriot_compartment_size(%s) = %d bytes = %d word(s)" g sl.gl.gsize sl.gwords)
              | Int n -> (
                  (* An immediate length: only the whole of a global whose
                     start the source is known to hold. *)
                  match read st s with
                  | Cap { glob = Some g; _ } when gsize g = Some n ->
                      let sl = gslot op g in
                      ( n, sl.gwords,
                        Printf.sprintf "length %d bytes = the whole of %s (%s holds its start) = %d word(s)" n g
                          (G.string_of_reg s) sl.gwords )
                  | _ -> fail op "bounds of %d bytes, not the whole of a global known to start at %s (D6)" n (string_of_reg s))
              | _ -> fail op "bounds of an object of unknown layout (D6)"
            in
            (* CHERIoT's bounds are exact below 512 bytes (a 9-bit mantissa,
               exponent 0, any base); Griotte's subseg is always exact. *)
            if bytes >= 512 then
              fail op "bounds of %d bytes, which CHERIoT may round (exact only below 512 bytes), while subseg is exact" bytes;
            let cands = pick_scratch live_out.(idx) [ d; s ] in
            let x1, x2 =
              match cands with
              | a :: b :: _ -> (a, b)
              | [ b ] when d <> s -> (d, b)
              | _ -> fail op "no two scratch registers dead here for setbounds_asm (D3)"
            in
            mk
              ~devs:
                [ Printf.sprintf "no CSetBounds in Griotte: setbounds_asm = geta %s %s; add %s %s %d; subseg %s %s %s %s"
                    (G.string_of_reg x1) (G.string_of_reg s) (G.string_of_reg x2) (G.string_of_reg x1) words
                    (G.string_of_reg d) (G.string_of_reg s) (G.string_of_reg x1) (G.string_of_reg x2);
                  Printf.sprintf "scratch %s, %s: dead after this instruction" (G.string_of_reg x1) (G.string_of_reg x2);
                  ldev;
                  Printf.sprintf
                    "Griotte's subseg sets exact bounds, while CHERIoT's csetbounds may round them: exact here, as %d bytes is below 512"
                    bytes ]
              [ M (G.Setbounds (d, s, words, x1, x2)) ]
        | "ct.clc", [ Reg d; Mem (Int o, s) ] ->
            let w, devs = mem_word op o s in
            mk ~devs [ ci (G.CLoad (d, s, G.Z w)) ]
        | "ct.clw", [ Reg d; Mem (Int o, s) ] ->
            let w, devs = mem_word op o s in
            if d = zero then fail op "load into zero";
            mk
              ~devs:(devs @ [ "integer load: geta keeps the address only, as clw drops the tag" ])
              [ ci (G.CLoad (d, s, G.Z w)); ci (G.GetA (d, d)) ]
        | "ct.csc", [ Reg v; Mem (Int o, s) ] ->
            let w, devs = mem_word op o s in
            mk ~devs [ ci (G.Store (s, arg_of v, G.Z w)) ]
        | "ct.csw", [ Reg v; Mem (Int o, s) ] ->
            let w, devs = mem_word op o s in
            if is_int (read st v) then mk ~devs [ ci (G.Store (s, arg_of v, G.Z w)) ]
            else
              let tmp =
                if v <> s && not (mem v live_out.(idx)) then v
                else
                  match pick_scratch live_out.(idx) [ s ] with
                  | x :: _ -> x
                  | [] -> fail op "no scratch register dead here for the integer store (D11)"
              in
              mk
                ~devs:
                  (devs
                  @ [ Printf.sprintf "integer store: geta %s %s keeps the address only, as csw drops the tag; %s dead after"
                        (G.string_of_reg tmp) (G.string_of_reg v) (G.string_of_reg tmp) ])
                [ ci (G.GetA (tmp, v)); ci (G.Store (s, G.R tmp, G.Z w)) ]
        | _ -> fail op "not in the subset the lowering supports")
  in
  let lowered = Array.mapi lower_node cfg.nodes in
  (* {2 Blocks} *)
  let blocks = ref [] and cur = ref None in
  Array.iteri
    (fun i lw ->
      (match (cuts.(i), !cur) with
       | [], Some b -> cur := Some { b with items = lw :: b.items }
       | [], None -> assert false
       | ls, prev ->
           Option.iter (fun b -> blocks := { b with items = List.rev b.items } :: !blocks) prev;
           cur := Some { labels = ls; items = [ lw ] }))
    lowered;
  Option.iter (fun b -> blocks := { b with items = List.rev b.items } :: !blocks) !cur;
  let words = Array.fold_left (fun acc lw -> acc + words_of_outs lw.outs) 0 lowered in
  { fo_func = f; fo_name = fname; fo_entry = base; fo_blocks = List.rev !blocks; fo_frame = fr;
    fo_switcher_calls = switcher_calls; fo_words = words }

(* {1 Label overrides (D8)}

   A map file: one "generated-label new-label" pair per line; blank lines
   and lines starting with # are ignored. Every generated label it names
   must exist (a stale map is an error). *)

let read_overrides file =
  List.filter_map
    (fun (k, line) ->
      let l = String.trim line in
      if l = "" || l.[0] = '#' then None
      else
        match List.filter (( <> ) "") (String.split_on_char ' ' (String.map (function '\t' -> ' ' | c -> c) l)) with
        | [ a; b ] -> Some (a, b, { Diag.file; line = k + 1 })
        | _ -> Diag.error { Diag.file; line = k + 1 } "expected: <generated label> <new label>")
    (List.mapi (fun k l -> (k, l)) (Cheriot_parser.read_lines file))

let rename_labels overrides funcs =
  let all = List.concat_map (fun fo -> List.concat_map (fun b -> b.labels) fo.fo_blocks) funcs in
  List.iter (fun (a, _, loc) -> if not (List.mem a all) then Diag.error loc "no generated label %s" a) overrides;
  let rn l = match List.find_opt (fun (a, _, _) -> a = l) overrides with Some (_, b, _) -> b | None -> l in
  let rn_arg = function G.E (G.Lbl l) -> G.E (G.Lbl (rn l)) | x -> x in
  let rn_instr = function
    | G.Jmp x -> G.Jmp (rn_arg x)
    | G.Jeq (o, x, y) -> G.Jeq (rn_arg o, x, y)
    | G.Jne (o, x, y) -> G.Jne (rn_arg o, x, y)
    | G.Jlt (o, x, y) -> G.Jlt (rn_arg o, x, y)
    | G.Jle (o, x, y) -> G.Jle (rn_arg o, x, y)
    | i -> i
  in
  let funcs =
    List.map
      (fun fo ->
        { fo with
          fo_entry = rn fo.fo_entry;
          fo_blocks =
            List.map
              (fun b ->
                { labels = List.map rn b.labels;
                  items =
                    List.map
                      (fun lw -> { lw with outs = List.map (function C (G.Instr i) -> C (G.Instr (rn_instr i)) | o -> o) lw.outs })
                      b.items })
              fo.fo_blocks })
      funcs
  in
  let all' = List.concat_map (fun fo -> List.concat_map (fun b -> b.labels) fo.fo_blocks) funcs in
  List.iter
    (fun l ->
      if List.length (List.filter (( = ) l) all') > 1 then
        Diag.error (Diag.no_loc "label map") "label %s defined twice after renaming" l)
    all';
  funcs

(* {1 The whole file} *)

type export_out = {
  ex : Classify.export;
  ex_label : string;
  ex_offset : int;  (* words from the start of the PCC region *)
  ex_min_stack : int;  (* words *)
  ex_frame_words : int;
  ex_switcher_spill : bool;
}

type t = {
  src : Classify.t;
  imports : (Classify.import * string) list;  (* in table order, with their symbol *)
  funcs : func_out list;
  gslots : gslot list;
  exports : export_out list;
}

(* The words of the switcher's spill of a cross-compartment call
   (SpillSlot_size, switcher/code/export_table_layout.v). *)
let spill_slot_size = 4

let lower ?(overrides = []) ~prefix (t : Classify.t) =
  let gslots = globals_layout t in
  let funcs = List.map (lower_func ~prefix ~t ~gslots) t.funcs in
  let funcs = rename_labels overrides funcs in
  let cfgs = List.map build_cfg t.funcs in
  let switcher_slot =
    if List.exists (fun (i : Classify.import) -> i.ikind = Classify.Switcher) t.imports then []
    else [ { Classify.isym = ".compartment_switcher"; ikind = Switcher; iwords = []; iloc = Diag.no_loc t.file } ]
  in
  let imports =
    List.map (fun i -> (i, import_name i)) (import_order { t with imports = switcher_slot @ t.imports } cfgs)
  in
  let library = t.ukind = Classify.Library in
  let prefix_words = List.length imports in
  let exports =
    List.map
      (fun (e : Classify.export) ->
        let rec find off = function
          | [] -> assert false
          | fo :: rest -> if fo.fo_func.fname = e.efunc then (fo, off) else find (off + fo.fo_words) rest
        in
        let fo, off = find 0 funcs in
        if (not library) && e.eposture = Classify.Inherit then
          Diag.error e.eloc "export %s: interrupt posture inherit, which a compartment export cannot have in Griotte (review R26)"
            e.esym;
        let fw = frame_words fo.fo_frame in
        { ex = e; ex_label = fo.fo_entry; ex_offset = prefix_words + off;
          ex_min_stack = fw + (if fo.fo_switcher_calls then spill_slot_size else 0);
          ex_frame_words = fw; ex_switcher_spill = fo.fo_switcher_calls })
      t.exports
  in
  { src = t; imports; funcs; gslots; exports }
