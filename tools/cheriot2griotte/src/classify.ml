(* Classification of a parsed `.s` file (one compartment or library):
   functions, exports, imports, globals, sealed objects, and the
   [%cheriot_compartment_hi]/[lo_i] pairs of the code.

   The lines are first grouped into symbol blocks: a non-local label opens
   a block in the current section, and every later line of that section
   belongs to it, even after a switch to another section and back (the
   compiler does this around inline assembly, e.g. the sealed-object import
   of the KVS client). A local label ([.L...]) opens a block only in a
   section without one; otherwise it is a label inside the current block. *)

open Cheriot_ast

(* {1 Result types} *)

type func_item = FLabel of string | FInstr of instr

type func = {
  fname : string;  (* the mangled symbol *)
  fsection : string;
  fitems : func_item list;  (* labels and instructions, in order *)
  floc : Diag.loc;
}

let func_instrs f =
  List.filter_map (function FInstr i -> Some i | FLabel _ -> None) f.fitems

type posture = Inherit | Enabled | Disabled

let string_of_posture = function
  | Inherit -> "inherit"
  | Enabled -> "enabled"
  | Disabled -> "disabled"

type export_kind =
  | Compartment_export of string  (* the compartment name of the symbol *)
  | Library_export

type export = {
  esym : string;  (* __export_<cmpt>_<f> or __library_export_libcalls_<f> *)
  ekind : export_kind;
  efunc : string;  (* the mangled function symbol *)
  emin_stack : int;  (* the min-stack byte, as is *)
  eflags : int;
  enargs : int;  (* flags & 7 *)
  eposture : posture;  (* (flags >> 3) & 3 *)
  eloc : Diag.loc;
}

type import_kind =
  | Switcher  (* .compartment_switcher: referenced, not declared *)
  | Library_call of string  (* the mangled function *)
  | Cross_call of string * string  (* compartment, mangled function *)
  | Shared_object of string * string  (* name, permissions *)

type import = {
  isym : string;
  ikind : import_kind;
  iwords : expr list;  (* the words of the import table entry *)
  iloc : Diag.loc;
}

type global = {
  gname : string;
  gsection : string;
  gbss : bool;
  gsize : int;  (* bytes *)
  ginit : data list;
  gloc : Diag.loc;
}

type sealed_object = {
  oname : string;
  otype : string;  (* the sealing type, without __export.sealing_type. *)
  osize : int;
  odata : data list;
  oloc : Diag.loc;
}

(* What a [%cheriot_compartment_hi]/[lo_i] pair computes. *)
type pair_kind =
  | Fetch_import of string  (* ct.auipcc r, hi(imp); ct.clc r, lo_i(L)(r) *)
  | Global_addr of string  (* ct.auicgp r, hi(g); ct.cincoffset r, r, lo_i(L) *)

type pair = { plabel : string; preg : reg; pkind : pair_kind; ploc : Diag.loc }

type unit_kind = Compartment of string | Library

type t = {
  file : string;
  ukind : unit_kind;
  funcs : func list;
  exports : export list;
  imports : import list;  (* declared ones, plus the switcher if used *)
  globals : global list;
  sealed_objects : sealed_object list;
  pairs : (string * pair list) list;  (* per function *)
}

(* {1 Grouping into blocks} *)

type sect_kind = Text | Bss | Data_ | Exports | Imports | Sealed | Note

let sect_kind loc name =
  let starts p = String.length name >= String.length p && String.sub name 0 (String.length p) = p in
  if starts ".text." then Text
  else if starts ".bss." then Bss
  else if starts ".data." then Data_
  else if name = ".compartment_exports" then Exports
  else if starts ".compartment_imports." then Imports
  else if name = ".sealed_objects" then Sealed
  else if name = ".note.GNU-stack" then Note
  else Diag.error loc "unsupported section %s" name

type block = {
  bname : string;
  bsect : string;
  bkind : sect_kind;
  bloc : Diag.loc;
  mutable blines : located_line list;  (* reversed *)
}

let is_local name = String.length name >= 2 && String.sub name 0 2 = ".L"

let group file (lines : located_line list) =
  let blocks = ref [] in
  let open_block = Hashtbl.create 16 in  (* section name -> block *)
  let cur = ref None in
  let sizes = Hashtbl.create 16 in
  let current loc what =
    match !cur with
    | Some s -> s
    | None -> Diag.error loc "%s before any .section" what
  in
  List.iter
    (fun ({ loc; line } as ll) ->
      match line with
      | Directive (Section s) ->
          ignore (sect_kind loc s.sname);
          cur := Some s.sname
      | Directive (Noise _ | Globl _ | Weak _) -> ()
      | Directive (Size (sym, e)) -> Hashtbl.replace sizes sym (e, loc)
      | Label name -> (
          let s = current loc "label" in
          match Hashtbl.find_opt open_block s with
          | Some b when is_local name -> b.blines <- ll :: b.blines
          | _ ->
              let b = { bname = name; bsect = s; bkind = sect_kind loc s; bloc = loc; blines = [] } in
              Hashtbl.replace open_block s b;
              blocks := b :: !blocks)
      | Instr _ | Directive (Data _) -> (
          let s = current loc "content" in
          match Hashtbl.find_opt open_block s with
          | Some b -> b.blines <- ll :: b.blines
          | None -> Diag.error loc "content before any label in section %s" s))
    lines;
  ignore file;
  (List.rev_map (fun b -> { b with blines = List.rev b.blines }) !blocks, sizes)

(* {1 Helpers} *)

let block_data b =
  List.map
    (fun { loc; line } ->
      match line with
      | Directive (Data d) -> d
      | Label l -> Diag.error loc "label %s inside data symbol %s" l b.bname
      | Instr _ -> Diag.error loc "instruction in data section %s" b.bsect
      | Directive _ -> assert false)
    b.blines

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p

let drop_prefix p s = String.sub s (String.length p) (String.length s - String.length p)

let byte_value loc = function
  | Byte (Num n) when n >= 0 && n < 256 -> n
  | _ -> Diag.error loc "expected a .byte constant"

let symbol_size sizes b =
  match Hashtbl.find_opt sizes b.bname with
  | Some (Num n, _) -> n
  | Some (e, loc) -> Diag.error loc "non-constant .size %s for %s" (string_of_expr e) b.bname
  | None -> Diag.error b.bloc "no .size for %s" b.bname

(* {1 Exports} *)

let classify_export b =
  let loc = b.bloc in
  let efunc, emin_stack, eflags =
    match block_data b with
    | [ Half (Sub (Symbol f, Symbol "__compartment_pcc_start")); m; fl ] ->
        (f, byte_value loc m, byte_value loc fl)
    | _ -> Diag.error loc "unexpected export entry %s" b.bname
  in
  let ekind =
    if starts_with "__library_export_libcalls_" b.bname then (
      if drop_prefix "__library_export_libcalls_" b.bname <> efunc then
        Diag.error loc "library export %s does not name %s" b.bname efunc;
      Library_export)
    else if starts_with "__export_" b.bname then
      let rest = drop_prefix "__export_" b.bname in
      let suffix = "_" ^ efunc in
      let n = String.length rest and k = String.length suffix in
      if n > k && String.sub rest (n - k) k = suffix then Compartment_export (String.sub rest 0 (n - k))
      else Diag.error loc "export %s does not name %s" b.bname efunc
    else Diag.error loc "unsupported export symbol %s" b.bname
  in
  if eflags land lnot 0x1f <> 0 then Diag.error loc "unexpected export flag bits 0x%x in %s" eflags b.bname;
  let eposture =
    match (eflags lsr 3) land 3 with
    | 0 -> Inherit
    | 1 -> Enabled
    | 2 -> Disabled
    | _ -> Diag.error loc "invalid interrupt posture in %s" b.bname
  in
  { esym = b.bname; ekind; efunc; emin_stack; eflags; enargs = eflags land 7; eposture; eloc = loc }

(* {1 Imports} *)

let classify_import b =
  let loc = b.bloc and s = b.bname in
  let iwords =
    match block_data b with
    | [ Word e1; Word e2 ] -> [ e1; e2 ]
    | _ -> Diag.error loc "unexpected import entry %s" s
  in
  let ikind =
    if starts_with "__library_import_libcalls_" s then (
      let f = drop_prefix "__library_import_libcalls_" s in
      (match iwords with
       | Add (Symbol t, Num 1) :: _ when t = "__library_export_libcalls_" ^ f -> ()
       | _ -> Diag.error loc "unexpected library import target in %s" s);
      Library_call f)
    else if starts_with "__import_cheriot_shared_object_" s then
      let rest = drop_prefix "__import_cheriot_shared_object_" s in
      match String.rindex_opt rest '_' with
      | Some i -> Shared_object (String.sub rest 0 i, String.sub rest (i + 1) (String.length rest - i - 1))
      | None -> Diag.error loc "cannot read shared-object import %s" s
    else if starts_with "__import_" s then (
      (* __import_<cmpt>_<mangled f>, the mangled name starting with _Z *)
      let rest = drop_prefix "__import_" s in
      match Str.search_forward (Str.regexp_string "__Z") rest 0 with
      | i ->
          let cmpt = String.sub rest 0 i and f = String.sub rest (i + 1) (String.length rest - i - 1) in
          (match iwords with
           | Symbol t :: _ when t = "__export_" ^ cmpt ^ "_" ^ f -> ()
           | _ -> Diag.error loc "unexpected cross-compartment import target in %s" s);
          Cross_call (cmpt, f)
      | exception Not_found -> Diag.error loc "unsupported import %s (no mangled function name)" s)
    else Diag.error loc "unsupported import kind %s" s
  in
  { isym = s; ikind; iwords; iloc = loc }

(* {1 Functions and relocation pairs} *)

let func_of_block b =
  let fitems =
    List.map
      (fun { loc; line } ->
        match line with
        | Label l -> FLabel l
        | Instr i -> FInstr i
        | Directive _ -> Diag.error loc "data in code section %s" b.bsect)
      b.blines
  in
  { fname = b.bname; fsection = b.bsect; fitems; floc = b.bloc }

(* Check the branch targets and the hi/lo_i pairs of a function, and
   return its pairs. Each lo_i(L) must complete the instruction labelled L,
   which comes right before it, on the same register. *)
let function_pairs ~is_import ~is_global f =
  let labels = List.filter_map (function FLabel l -> Some l | FInstr _ -> None) f.fitems in
  let pairs = ref [] in
  (* [pending] is the label and hi instruction awaiting its lo_i. *)
  let rec go pending cur_labels = function
    | [] -> (
        match pending with
        | Some (_, (hi : instr)) -> Diag.error hi.iloc "%%cheriot_compartment_hi without its lo_i"
        | None -> ())
    | FLabel l :: rest -> go pending (l :: cur_labels) rest
    | FInstr i :: rest -> (
        List.iter
          (function
            | Sym t when not (List.mem t labels) ->
                Diag.error i.iloc "branch target %s is not a label of %s" t f.fname
            | Imm (Reloc (Size, g)) when not (is_global g) ->
                Diag.error i.iloc "%%cheriot_compartment_size of %s, not a global" g
            | _ -> ())
          i.operands;
        match (pending, i.mnemonic, i.operands) with
        | None, ("ct.auipcc" | "ct.auicgp"), [ Reg r; Imm (Reloc (Hi, _)) ] -> (
            match cur_labels with
            | l :: _ -> go (Some (l, i)) [] rest
            | [] -> Diag.error i.iloc "%%cheriot_compartment_hi instruction without a label")
        | None, _, ([ _; Mem (Reloc (Lo_i, _), _) ] | [ _; _; Imm (Reloc (Lo_i, _)) ]) ->
            Diag.error i.iloc "%%cheriot_compartment_lo_i without its hi"
        | None, _, _ -> go None [] rest
        | Some (l, hi), _, _ ->
            let r, target =
              match hi.operands with
              | [ Reg r; Imm (Reloc (Hi, t)) ] -> (r, t)
              | _ -> assert false
            in
            let kind =
              match (hi.mnemonic, i.mnemonic, i.operands) with
              | "ct.auipcc", "ct.clc", [ Reg d; Mem (Reloc (Lo_i, l'), b) ]
                when d = r && b = r && l' = l && is_import target ->
                  Fetch_import target
              | "ct.auicgp", "ct.cincoffset", [ Reg d; Reg s; Imm (Reloc (Lo_i, l')) ]
                when d = r && s = r && l' = l && is_global target ->
                  Global_addr target
              | _ ->
                  Diag.error i.iloc "unsupported %%cheriot_compartment_hi/lo_i pair: %s; %s"
                    (string_of_instr hi) (string_of_instr i)
            in
            pairs := { plabel = l; preg = r; pkind = kind; ploc = hi.iloc } :: !pairs;
            go None [] rest)
  in
  go None [] f.fitems;
  List.rev !pairs

(* {1 The whole file} *)

let classify file lines =
  let blocks, sizes = group file lines in
  let of_kind k = List.filter (fun b -> b.bkind = k) blocks in
  List.iter (fun b -> Diag.error b.bloc "symbol %s in %s" b.bname b.bsect) (of_kind Note);
  let funcs = List.map func_of_block (of_kind Text) in
  let exports = List.map classify_export (of_kind Exports) in
  let declared = List.map classify_import (of_kind Imports) in
  let global_of_block bss b =
    let ginit = block_data b in
    let gsize = symbol_size sizes b in
    let total = List.fold_left (fun acc d -> acc + data_size d) 0 ginit in
    if total <> gsize then Diag.error b.bloc "%s: .size %d, but %d bytes of data" b.bname gsize total;
    { gname = b.bname; gsection = b.bsect; gbss = bss; gsize; ginit; gloc = b.bloc }
  in
  let globals =
    List.filter_map
      (fun b ->
        match b.bkind with
        | Bss -> Some (global_of_block true b)
        | Data_ -> Some (global_of_block false b)
        | _ -> None)
      blocks
  in
  let sealed_objects =
    List.map
      (fun b ->
        let odata = block_data b in
        let otype =
          match odata with
          | Word (Symbol t) :: _ when starts_with "__export.sealing_type." t ->
              drop_prefix "__export.sealing_type." t
          | _ -> Diag.error b.bloc "sealed object %s without a sealing type" b.bname
        in
        { oname = b.bname; otype; osize = symbol_size sizes b; odata; oloc = b.bloc })
      (of_kind Sealed)
  in
  let is_global g = List.exists (fun x -> x.gname = g) globals in
  let is_import t = t = ".compartment_switcher" || List.exists (fun x -> x.isym = t) declared in
  let pairs = List.map (fun f -> (f.fname, function_pairs ~is_import ~is_global f)) funcs in
  (* Every export names a function of the file. *)
  List.iter
    (fun e ->
      if not (List.exists (fun f -> f.fname = e.efunc) funcs) then
        Diag.error e.eloc "export %s of an unknown function %s" e.esym e.efunc)
    exports;
  let switcher_used =
    List.exists
      (fun (_, ps) -> List.exists (fun p -> p.pkind = Fetch_import ".compartment_switcher") ps)
      pairs
  in
  let imports =
    (if switcher_used then
       [ { isym = ".compartment_switcher"; ikind = Switcher; iwords = []; iloc = Diag.no_loc file } ]
     else [])
    @ declared
  in
  let ukind =
    match exports with
    | [] -> Diag.error (Diag.no_loc file) "no export"
    | _ ->
        let cmpts =
          List.sort_uniq compare
            (List.map (fun e -> match e.ekind with Compartment_export c -> Some c | Library_export -> None) exports)
        in
        (match cmpts with
         | [ Some c ] -> Compartment c
         | [ None ] -> Library
         | _ -> Diag.error (Diag.no_loc file) "exports of several compartments or of a library and a compartment")
  in
  { file; ukind; funcs; exports; imports; globals; sealed_objects; pairs }

let classify_file file = classify file (Cheriot_parser.parse_file file)

(* Number of times the code fetches an import. *)
let import_uses t sym =
  List.fold_left
    (fun acc (_, ps) -> acc + List.length (List.filter (fun p -> p.pkind = Fetch_import sym) ps))
    0 t.pairs

(* {1 Exports only (untrusted compartments)}

   Untrusted compartments are arbitrary code in Griotte ([UntrustedBody]):
   only their export names, nargs and postures matter. Their code may use
   constructs outside the subset, so this reader parses the
   [.compartment_exports] section strictly and only follows the [.section]
   directives elsewhere, without reading the other lines. *)
let section_line_re = Str.regexp "^[ \t]*\\.section[ \t]"

let exports_only file =
  let raw = Cheriot_parser.read_lines file in
  let in_exports = ref false in
  let kept =
    List.concat
      (List.mapi
         (fun i s ->
           if Str.string_match section_line_re s 0 then (
             let ls = Cheriot_parser.parse_line ~file ~line:(i + 1) s in
             List.iter
               (function
                 | { line = Directive (Section sec); _ } -> in_exports := sec.sname = ".compartment_exports"
                 | _ -> ())
               ls;
             ls)
           else if !in_exports then Cheriot_parser.parse_line ~file ~line:(i + 1) s
           else [])
         raw)
  in
  (* Only the export section's blocks, without the Text/... checks. *)
  let cur = ref false and blocks = ref [] in
  List.iter
    (fun ({ loc; line } as ll) ->
      match line with
      | Directive (Section s) -> cur := s.sname = ".compartment_exports"
      | _ when not !cur -> ()
      | Label name ->
          blocks := { bname = name; bsect = ".compartment_exports"; bkind = Exports; bloc = loc; blines = [] } :: !blocks
      | Directive (Data _) -> (
          match !blocks with
          | b :: _ -> b.blines <- ll :: b.blines
          | [] -> Diag.error loc "export data before any label")
      | Directive _ -> ()
      | Instr _ -> Diag.error loc "instruction in .compartment_exports")
    kept;
  List.rev_map (fun b -> classify_export { b with blines = List.rev b.blines }) !blocks
