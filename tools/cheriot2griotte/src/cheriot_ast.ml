(* The CHERIoT side: the subset of the compiler's symbolic assembly (`.s`,
   clang -S for the CHERIoT target) that the in-scope examples use.

   The parser (Cheriot_parser) produces a flat list of lines; the
   classification (Classify) groups them by section and symbol. *)

(* RV32E registers x0..x15, by ABI name. Griotte's [RegName] has the same
   sixteen registers with the same numbering (cnull, cra, csp, cgp, ctp,
   ct0..ct2, cs0, cs1, ca0..ca5). *)
type reg = int

let reg_names =
  [| "zero"; "ra"; "sp"; "gp"; "tp"; "t0"; "t1"; "t2";
     "s0"; "s1"; "a0"; "a1"; "a2"; "a3"; "a4"; "a5" |]

let reg_of_name s =
  let rec find i =
    if i >= Array.length reg_names then None
    else if reg_names.(i) = s then Some i
    else find (i + 1)
  in
  find 0

let string_of_reg r = reg_names.(r)

(* The CHERIoT compartment relocations:
   - [%cheriot_compartment_hi(sym)] on [ct.auipcc] (imports, switcher) and
     on [ct.auicgp] (globals);
   - [%cheriot_compartment_lo_i(L)] on the [ct.clc]/[ct.cincoffset] that
     completes the pair, where [L] labels the [hi] instruction;
   - [%cheriot_compartment_size(sym)] on [ct.csetbounds]. *)
type reloc = Hi | Lo_i | Size

let string_of_reloc = function
  | Hi -> "%cheriot_compartment_hi"
  | Lo_i -> "%cheriot_compartment_lo_i"
  | Size -> "%cheriot_compartment_size"

(* An immediate: an integer, or a relocation against a symbol. *)
type imm = Int of int | Reloc of reloc * string

type operand =
  | Reg of reg
  | Imm of imm
  | Mem of imm * reg  (* off(reg) *)
  | Sym of string  (* branch target *)

type instr = { mnemonic : string; operands : operand list; iloc : Diag.loc }

(* Expressions of data directives: [.word sym+1],
   [.half f-__compartment_pcc_start], [.word a_end-a-1073741824]. *)
type expr =
  | Num of int
  | Symbol of string
  | Add of expr * expr
  | Sub of expr * expr

type section = {
  sname : string;
  sflags : string;  (* "ax", "aw", ...; "" when absent *)
  sgroup : string option;  (* the comdat/section group, if any *)
}

type data =
  | Word of expr  (* 4 bytes *)
  | Half of expr  (* 2 bytes *)
  | Byte of expr  (* 1 byte *)
  | Zero of int  (* n zero bytes *)
  | Chericap of expr  (* 8 bytes: a capability ([.chericap 0]: null) *)

let data_size = function Word _ -> 4 | Half _ -> 2 | Byte _ -> 1 | Zero n -> n | Chericap _ -> 8

type directive =
  | Section of section
  | Globl of string
  | Weak of string
  | Size of string * expr  (* .size sym, expr *)
  | Data of data
  | Noise of string
      (* directives without information for the tool, by name: see
         Cheriot_parser.noise_directives *)

type line =
  | Label of string
  | Instr of instr
  | Directive of directive

type located_line = { loc : Diag.loc; line : line }

(* Printing, for the summary and error messages. *)

let rec string_of_expr = function
  | Num n -> string_of_int n
  | Symbol s -> s
  | Add (a, b) -> string_of_expr a ^ "+" ^ string_of_expr b
  | Sub (a, b) -> string_of_expr a ^ "-" ^ string_of_expr b

let string_of_imm = function
  | Int n -> string_of_int n
  | Reloc (r, s) -> Printf.sprintf "%s(%s)" (string_of_reloc r) s

let string_of_operand = function
  | Reg r -> string_of_reg r
  | Imm i -> string_of_imm i
  | Mem (i, r) -> Printf.sprintf "%s(%s)" (string_of_imm i) (string_of_reg r)
  | Sym s -> s

let string_of_instr i =
  match i.operands with
  | [] -> i.mnemonic
  | ops -> i.mnemonic ^ " " ^ String.concat ", " (List.map string_of_operand ops)
