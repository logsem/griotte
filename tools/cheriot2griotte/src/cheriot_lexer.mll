(* Lexer of the CHERIoT `.s` subset (grammar: cheriot_grammar.mly).

   - Comments run from `#` to the end of the line (outside strings); the
     inline-assembly markers `#APP`/`#NO_APP` are comments too.
   - Mnemonics, registers, relocation operators and directives are
     keywords, by the tables below; any other name is an identifier.
   - The directives without information for the tool ([noise_directives])
     are returned as one [NOISE] token, the rest of their line skipped.
   - An unknown [%relocation] or an unexpected character is an error with
     file:line. *)

{
open Cheriot_grammar

(* Directives the tool ignores: assembler attributes, file name,
   address-significance tables, compiler identification, alignment, symbol
   types. None changes the code or data the tool reads ([.type] is not
   needed: functions are the symbols of executable sections). *)
let noise_directives =
  [ ".attribute"; ".file"; ".addrsig"; ".addrsig_sym"; ".ident"; ".p2align"; ".type" ]

let directives =
  [ (".section", DSECTION); (".globl", DGLOBL); (".weak", DWEAK); (".size", DSIZE);
    (".word", DWORD); (".half", DHALF); (".byte", DBYTE); (".zero", DZERO) ]

(* The mnemonics of the subset; their operands are in the grammar. *)
let mnemonics =
  [ ("li", LI); ("lui", LUI); ("mv", MV); ("addi", ADDI); ("andi", ANDI); ("add", ADD);
    ("slli", SLLI); ("beq", BEQ); ("bne", BNE); ("bltu", BLTU); ("bgeu", BGEU); ("beqz", BEQZ); ("bnez", BNEZ);
    ("j", J); ("ecall", ECALL); ("unimp", UNIMP);
    ("ct.cret", CRET); ("ct.cjalr", CJALR);
    ("ct.auipcc", AUIPCC); ("ct.auicgp", AUICGP);
    ("ct.cincoffset", CINCOFFSET); ("ct.csetbounds", CSETBOUNDS);
    ("ct.clc", CLC); ("ct.clw", CLW); ("ct.csc", CSC); ("ct.csw", CSW);
    ("ct.cmove", CMOVE);
    ("ct.cgettag", CGETTAG); ("ct.cgetbase", CGETBASE); ("ct.cgetlen", CGETLEN);
    ("ct.cgetperm", CGETPERM);
    ("ct.csetaddr", CSETADDR); ("ct.candperm", CANDPERM) ]

let loc lexbuf =
  let p = Lexing.lexeme_start_p lexbuf in
  { Diag.file = p.Lexing.pos_fname; line = p.Lexing.pos_lnum }

let keyword lexbuf s =
  match List.assoc_opt s mnemonics with
  | Some t -> t
  | None -> (
      match List.assoc_opt s directives with
      | Some t -> t
      | None -> (
          match Cheriot_ast.reg_of_name s with
          | Some r -> REG r
          | None -> ignore lexbuf; IDENT s))
}

let ident = ['A'-'Z' 'a'-'z' '_' '.' '$'] ['A'-'Z' 'a'-'z' '0'-'9' '_' '.' '$']*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '#' [^ '\n']* { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; NEWLINE }
  | ':' { COLON }
  | ',' { COMMA }
  | '(' { LPAREN }
  | ')' { RPAREN }
  | '+' { PLUS }
  | '-' { MINUS }
  | "0x" ['0'-'9' 'a'-'f' 'A'-'F']+ as n { INT (int_of_string n) }
  | ['0'-'9']+ as n { INT (int_of_string n) }
  | '"' ([^ '"' '\n']* as s) '"' { STRING s }
  | '@' (ident as s) { AT_IDENT s }
  | "%cheriot_compartment_hi" { RELOC_HI }
  | "%cheriot_compartment_lo_i" { RELOC_LO_I }
  | "%cheriot_compartment_size" { RELOC_SIZE }
  | '%' (ident as s) { Diag.error (loc lexbuf) "unknown relocation %%%s" s }
  | ident as s
      { if List.mem s noise_directives then (skip_line lexbuf; NOISE s) else keyword lexbuf s }
  | eof { EOF }
  | _ as c { Diag.error (loc lexbuf) "unexpected character %C" c }

(* The rest of a noise directive's line, up to (not including) the newline. *)
and skip_line = parse
  | [^ '\n']* { () }
