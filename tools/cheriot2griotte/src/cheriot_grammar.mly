/* Grammar of the CHERIoT `.s` subset that cheriot2griotte accepts: the
   compiler's symbolic assembly (clang -S, CHERIoT target) of the in-scope
   examples. Lexer: cheriot_lexer.mll.

   This file states the subset. A file is a sequence of lines; a line is
   zero or more label definitions followed by at most one instruction or
   directive. The accepted instructions are the [instr] productions below,
   each with its operand shapes; the accepted directives are the
   [directive] productions, plus the noise directives skipped by the lexer
   (.attribute, .file, .addrsig, .addrsig_sym, .ident, .p2align, .type).

   Failure modes, all reported with file:line:
   - an unknown mnemonic or directive: the [unknown] production reads the
     line as a name with generic operands, and its action fails with
     "unknown mnemonic" / "unknown directive";
   - a known mnemonic or directive with operands of the wrong shape, or any
     other ill-formed line: a syntax error (Cheriot_parser reports it);
   - an unknown relocation operator or character: the lexer.

   The meaning of the accepted lines (sections, symbols, imports, exports,
   relocation pairs) is checked afterwards by Classify. */

%{
open Cheriot_ast

let loc (p : Lexing.position) = { Diag.file = p.pos_fname; line = p.pos_lnum }

let ins p mnemonic operands = Instr { mnemonic; operands; iloc = loc p }
%}

%token <int> INT
%token <int> REG
%token <string> IDENT STRING AT_IDENT NOISE
%token COLON COMMA LPAREN RPAREN PLUS MINUS NEWLINE EOF
%token RELOC_HI RELOC_LO_I RELOC_SIZE
%token DSECTION DGLOBL DWEAK DSIZE DWORD DHALF DBYTE DZERO
%token LI LUI MV ADDI ANDI ADD SLLI BEQ BNE BLTU BGEU BEQZ BNEZ J ECALL UNIMP
%token CRET CJALR AUIPCC AUICGP CINCOFFSET CSETBOUNDS CLC CLW CSC CSW CMOVE
%token CGETTAG CGETBASE CGETLEN CGETPERM CSETADDR CANDPERM

%start <Cheriot_ast.located_line list> file

%%

file:
  | ls = line* EOF { List.concat ls }

(* Written right-recursively, so that a line starting with a name needs no
   decision before the token after it (':' for a label). *)
line:
  | NEWLINE { [] }
  | s = statement NEWLINE { [ s ] }
  | l = label rest = line { l :: rest }

label:
  | s = symbol COLON { { loc = loc $startpos; line = Label s } }

statement:
  | i = instr { { loc = loc $startpos; line = i } }
  | d = directive { { loc = loc $startpos; line = Directive d } }
  | unknown { assert false }

symbol:
  | s = IDENT { s }
  | s = STRING { s }

/* {1 Operands} */

reg:
  | r = REG { r }

int:
  | n = INT { n }
  | MINUS n = INT { - n }

(* Integer or %cheriot_compartment_hi(sym): ct.auipcc, ct.auicgp. *)
hi_imm:
  | n = int { Imm (Int n) }
  | RELOC_HI LPAREN s = symbol RPAREN { Imm (Reloc (Hi, s)) }

(* Register, integer or %cheriot_compartment_lo_i(L): ct.cincoffset. *)
offset:
  | r = reg { Reg r }
  | n = int { Imm (Int n) }
  | RELOC_LO_I LPAREN s = symbol RPAREN { Imm (Reloc (Lo_i, s)) }

(* Register, integer or %cheriot_compartment_size(sym): ct.csetbounds. *)
length:
  | r = reg { Reg r }
  | n = int { Imm (Int n) }
  | RELOC_SIZE LPAREN s = symbol RPAREN { Imm (Reloc (Size, s)) }

(* off(reg), off an integer or %cheriot_compartment_lo_i(L): loads, stores. *)
mem:
  | n = int LPAREN r = reg RPAREN { Mem (Int n, r) }
  | RELOC_LO_I LPAREN s = symbol RPAREN LPAREN r = reg RPAREN { Mem (Reloc (Lo_i, s), r) }

target:
  | s = IDENT { Sym s }

/* {1 Instructions: the accepted subset} */

instr:
  | LI d = reg COMMA n = int { ins $startpos "li" [ Reg d; Imm (Int n) ] }
  | LUI d = reg COMMA n = int { ins $startpos "lui" [ Reg d; Imm (Int n) ] }
  | MV d = reg COMMA s = reg { ins $startpos "mv" [ Reg d; Reg s ] }
  | ADDI d = reg COMMA s = reg COMMA n = int { ins $startpos "addi" [ Reg d; Reg s; Imm (Int n) ] }
  | ANDI d = reg COMMA s = reg COMMA n = int { ins $startpos "andi" [ Reg d; Reg s; Imm (Int n) ] }
  | ADD d = reg COMMA s1 = reg COMMA s2 = reg { ins $startpos "add" [ Reg d; Reg s1; Reg s2 ] }
  | SLLI d = reg COMMA s = reg COMMA n = int { ins $startpos "slli" [ Reg d; Reg s; Imm (Int n) ] }
  | BEQ a = reg COMMA b = reg COMMA t = target { ins $startpos "beq" [ Reg a; Reg b; t ] }
  | BNE a = reg COMMA b = reg COMMA t = target { ins $startpos "bne" [ Reg a; Reg b; t ] }
  | BLTU a = reg COMMA b = reg COMMA t = target { ins $startpos "bltu" [ Reg a; Reg b; t ] }
  | BGEU a = reg COMMA b = reg COMMA t = target { ins $startpos "bgeu" [ Reg a; Reg b; t ] }
  | BEQZ a = reg COMMA t = target { ins $startpos "beqz" [ Reg a; t ] }
  | BNEZ a = reg COMMA t = target { ins $startpos "bnez" [ Reg a; t ] }
  | J t = target { ins $startpos "j" [ t ] }
  | ECALL { ins $startpos "ecall" [] }
  | UNIMP { ins $startpos "unimp" [] }
  | CRET { ins $startpos "ct.cret" [] }
  | CJALR r = reg { ins $startpos "ct.cjalr" [ Reg r ] }
  | AUIPCC d = reg COMMA i = hi_imm { ins $startpos "ct.auipcc" [ Reg d; i ] }
  | AUICGP d = reg COMMA i = hi_imm { ins $startpos "ct.auicgp" [ Reg d; i ] }
  | CINCOFFSET d = reg COMMA s = reg COMMA o = offset
    { ins $startpos "ct.cincoffset" [ Reg d; Reg s; o ] }
  | CSETBOUNDS d = reg COMMA s = reg COMMA l = length
    { ins $startpos "ct.csetbounds" [ Reg d; Reg s; l ] }
  | CLC d = reg COMMA m = mem { ins $startpos "ct.clc" [ Reg d; m ] }
  | CLW d = reg COMMA m = mem { ins $startpos "ct.clw" [ Reg d; m ] }
  | CSC v = reg COMMA m = mem { ins $startpos "ct.csc" [ Reg v; m ] }
  | CSW v = reg COMMA m = mem { ins $startpos "ct.csw" [ Reg v; m ] }
  | CMOVE d = reg COMMA s = reg { ins $startpos "ct.cmove" [ Reg d; Reg s ] }
  | CGETTAG d = reg COMMA s = reg { ins $startpos "ct.cgettag" [ Reg d; Reg s ] }
  | CGETBASE d = reg COMMA s = reg { ins $startpos "ct.cgetbase" [ Reg d; Reg s ] }
  | CGETLEN d = reg COMMA s = reg { ins $startpos "ct.cgetlen" [ Reg d; Reg s ] }
  | CGETPERM d = reg COMMA s = reg { ins $startpos "ct.cgetperm" [ Reg d; Reg s ] }
  | CSETADDR d = reg COMMA s = reg COMMA a = reg
    { ins $startpos "ct.csetaddr" [ Reg d; Reg s; Reg a ] }
  | CANDPERM d = reg COMMA s = reg COMMA m = reg
    { ins $startpos "ct.candperm" [ Reg d; Reg s; Reg m ] }

/* {1 Directives: the accepted subset} */

(* Data expressions: [sym+1], [f-__compartment_pcc_start],
   [a_end-a-1073741824]. A leading minus belongs to a number. *)
expr:
  | a = atom { a }
  | MINUS n = INT { Num (- n) }
  | e = expr PLUS a = atom { Add (e, a) }
  | e = expr MINUS a = atom { Sub (e, a) }

atom:
  | n = INT { Num n }
  | s = symbol { Symbol s }

directive:
  (* .section name[,"flags",@type[,group[,comdat]]] *)
  | DSECTION n = symbol { Section { sname = n; sflags = ""; sgroup = None } }
  | DSECTION n = symbol COMMA f = STRING COMMA AT_IDENT g = section_group?
    { Section { sname = n; sflags = f; sgroup = (if String.contains f 'G' then g else None) } }
  | DGLOBL s = symbol { Globl s }
  | DWEAK s = symbol { Weak s }
  | DSIZE s = symbol COMMA e = expr { Size (s, e) }
  | DWORD e = expr { Data (Word e) }
  | DHALF e = expr { Data (Half e) }
  | DBYTE e = expr { Data (Byte e) }
  | DZERO n = INT { Data (Zero n) }
  | n = NOISE { Noise n }

(* ,group or ,group,comdat *)
section_group:
  | COMMA g = symbol { g }
  | COMMA g = symbol COMMA IDENT { g }

/* {1 Anything else: an error} */

any_operand:
  | reg { () }
  | int { () }
  | symbol { () }
  | int LPAREN reg RPAREN { () }
  | RELOC_HI LPAREN symbol RPAREN { () }
  | RELOC_LO_I LPAREN symbol RPAREN { () }
  | RELOC_LO_I LPAREN symbol RPAREN LPAREN reg RPAREN { () }
  | RELOC_SIZE LPAREN symbol RPAREN { () }

unknown:
  | m = IDENT separated_list(COMMA, any_operand)
    { if m <> "" && m.[0] = '.' then Diag.error (loc $startpos) "unknown directive %s" m
      else Diag.error (loc $startpos) "unknown mnemonic %S" m }
