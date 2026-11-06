(* Cross-check of the `.s` against the `.dump` of the linked compartment:
   per function, the instruction streams must agree on the mnemonic and on
   the register operands, in order. Immediates are not compared: objdump
   prints them in hex and shows 0 in place of unresolved relocations.

   Pairing of functions with dump segments: by demangled name
   ([_Z3runv] <-> [run()]). The symbol at offset 0 is printed as
   [__compartment_code_start] (it coincides with the first function), so
   that segment is paired with the first function left unpaired.

   No spelling normalisation is needed for the in-scope files: the
   compiler and objdump print the same pseudo-instructions ([li], [mv],
   [j], [beqz], [ct.cret], ...), and the compartment objects are not
   relaxed (the [auipcc]/[auicgp] pairs keep both instructions; the
   firmware link may relax them, which this check cannot see). A construct
   that needs one (e.g. [ct.ccall], which objdump shows expanded) is
   reported as a mismatch, not hidden. *)

open Cheriot_ast

type result = {
  matched : (string * int) list;  (* function, instruction count *)
  mismatches : string list;
  dump_only : (string * int) list;  (* segments without a function *)
  absent : string list;  (* functions without a segment *)
}

let expected (i : instr) =
  let regs =
    List.concat_map
      (function Reg r -> [ string_of_reg r ] | Mem (_, r) -> [ string_of_reg r ] | Imm _ | Sym _ -> [])
      i.operands
  in
  (i.mnemonic, regs)

let compare_function file (f : Classify.func) (seg : Objdump.segment) dump_file =
  let s_instrs = Classify.func_instrs f in
  let rec go k ss ds =
    match (ss, ds) with
    | [], [] -> None
    | (s : instr) :: ss', (d : Objdump.dinstr) :: ds' ->
        let m, regs = expected s in
        let dregs = Objdump.registers d.doperands in
        if m = d.dmnemonic && regs = dregs then go (k + 1) ss' ds'
        else
          Some
            (Printf.sprintf "%s: instruction %d differs: %s:%d `%s` vs %s:%d `%s %s`"
               (Demangle.demangle f.fname) k file s.iloc.line (string_of_instr s) dump_file d.dline
               d.dmnemonic d.doperands)
    | _ ->
        Some
          (Printf.sprintf "%s: %d instructions in the .s, %d in the .dump" (Demangle.demangle f.fname)
             (List.length s_instrs) (List.length seg.sinstrs))
  in
  go 1 s_instrs seg.sinstrs

let check (t : Classify.t) dump_file =
  let segs = Objdump.parse_file dump_file in
  let used = Hashtbl.create 8 in
  let find_by_name f =
    let key = Demangle.demangle f.Classify.fname in
    List.find_opt
      (fun (s : Objdump.segment) -> (not (Hashtbl.mem used s.sname)) && Demangle.objdump_key s.sname = key)
      segs
  in
  let pairs = List.map (fun f -> (f, find_by_name f)) t.funcs in
  List.iter (function _, Some (s : Objdump.segment) -> Hashtbl.replace used s.sname () | _, None -> ()) pairs;
  (* The segment at offset 0, named __compartment_code_start. *)
  let start =
    List.find_opt
      (fun (s : Objdump.segment) -> s.sname = "__compartment_code_start" && not (Hashtbl.mem used s.sname))
      segs
  in
  let pairs, _ =
    List.fold_left
      (fun (acc, start) (f, s) ->
        match (s, start) with
        | None, Some st ->
            Hashtbl.replace used st.Objdump.sname ();
            ((f, Some st) :: acc, None)
        | _ -> ((f, s) :: acc, start))
      ([], start) pairs
  in
  let pairs = List.rev pairs in
  let matched = ref [] and mismatches = ref [] and absent = ref [] in
  List.iter
    (fun ((f : Classify.func), s) ->
      match s with
      | None -> absent := Demangle.demangle f.fname :: !absent
      | Some seg -> (
          match compare_function t.file f seg dump_file with
          | None -> matched := (Demangle.demangle f.fname, List.length seg.sinstrs) :: !matched
          | Some m -> mismatches := m :: !mismatches))
    pairs;
  let dump_only =
    List.filter_map
      (fun (s : Objdump.segment) ->
        if Hashtbl.mem used s.sname then None else Some (s.sname, List.length s.sinstrs))
      segs
  in
  { matched = List.rev !matched; mismatches = List.rev !mismatches; dump_only; absent = List.rev !absent }

(* Every function of the .s found in the dump with the same instructions,
   and no unexplained dump code. *)
let ok r = r.mismatches = [] && r.dump_only = [] && r.absent = []
