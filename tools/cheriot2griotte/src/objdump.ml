(* Reader of the `.dump` files: [llvm-objdump -d -r --no-show-raw-insn
   --demangle] of the linked compartment or library (asm/README.md, step 3).

   Line forms:
   {v
   00000000 <__compartment_code_start>:            symbol
          0:      	ct.cincoffset	sp, sp, -0x20     instruction
   			00000008:  R_RISCV_CHERIOT_COMPARTMENT_HI	b   relocation
   v}
   The instructions are cut into segments at the non-local symbols
   ([.L...] symbols are labels inside a function). *)

type dinstr = {
  addr : int;
  dmnemonic : string;
  doperands : string;  (* as printed *)
  dline : int;
}

type segment = { sname : string; sinstrs : dinstr list }

let symbol_re = Str.regexp "^\\([0-9a-f]+\\) <\\(.*\\)>:$"
let reloc_re = Str.regexp "^[0-9a-f]+:[ \t]+R_"
let instr_re = Str.regexp "^\\([0-9a-f]+\\):[ \t]*\\([^ \t]+\\)[ \t]*\\(.*\\)$"

let parse_file file =
  let lines = Cheriot_parser.read_lines file in
  let segments = ref [] and cur = ref None in
  let flush () =
    match !cur with
    | Some (name, instrs) -> segments := { sname = name; sinstrs = List.rev instrs } :: !segments
    | None -> ()
  in
  List.iteri
    (fun i raw ->
      let loc = { Diag.file; line = i + 1 } in
      let s = String.trim raw in
      if s = "" then ()
      else if Str.string_match symbol_re s 0 then (
        let name = Str.matched_group 2 s in
        if not (Classify.is_local name) then (
          flush ();
          cur := Some (name, [])))
      else if Str.string_match reloc_re s 0 then ()
      else if s = "Disassembly of section .text:" then ()
      else if Str.string_match (Str.regexp ".*:[ \t]+file format ") s 0 then ()
      else if Str.string_match instr_re s 0 then (
        let addr = int_of_string ("0x" ^ Str.matched_group 1 s) in
        let dmnemonic = Str.matched_group 2 s and doperands = String.trim (Str.matched_group 3 s) in
        match !cur with
        | Some (name, instrs) -> cur := Some (name, { addr; dmnemonic; doperands; dline = i + 1 } :: instrs)
        | None -> Diag.error loc "instruction before any symbol")
      else Diag.error loc "cannot parse objdump line %S" s)
    lines;
  flush ();
  List.rev !segments

(* The registers of an objdump operand string, in order. Symbolic branch
   targets ([0xc <f+0xc>]) are dropped first. *)
let registers ops =
  let ops = Str.global_replace (Str.regexp "<[^>]*>") "" ops in
  List.filter
    (fun t -> Cheriot_ast.reg_of_name t <> None)
    (Str.split (Str.regexp "[ ,()\t]+") ops)
