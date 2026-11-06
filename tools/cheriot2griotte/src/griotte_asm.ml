(* The Griotte side: an OCaml mirror of the assembler DSL of
   theories/opsem/assembler.v ([asm_expr], [asm_arg], [asm_instr],
   [asm_code]), plus the macros the tool emits as Rocq calls rather than
   expanded ([fetch_asm], [setbounds_asm]).

   Registers have the numbering of Cheriot_ast (and of Griotte's
   [RegName]): x0..x15 are cnull, cra, csp, cgp, ctp, ct0..ct2, cs0, cs1,
   ca0..ca5. Rocq's [asm_check] on the printed file catches any drift of
   this mirror. *)

type reg = int

let reg_names =
  [| "cnull"; "cra"; "csp"; "cgp"; "ctp"; "ct0"; "ct1"; "ct2";
     "cs0"; "cs1"; "ca0"; "ca1"; "ca2"; "ca3"; "ca4"; "ca5" |]

let string_of_reg r = reg_names.(r)

type expr =
  | Lbl of string
  | Z of int
  | Plus of expr * expr
  | Minus of expr * expr
  | Perm of Cheriot_perms.pair
      (* [encodePermPair (P, g)], printed as the name of a constant (see
         [perm_name]): the encoding is abstract in [MachineParameters] *)

type arg = E of expr | R of reg

type instr =
  | Jmp of arg
  | Jeq of arg * arg * arg
  | Jne of arg * arg * arg
  | Jlt of arg * arg * arg
  | Jle of arg * arg * arg
  | Jalr of reg * reg
  | Mov of reg * arg
  | CLoad of reg * reg * expr  (* dst, src, imm *)
  | Store of reg * arg * expr  (* dst (the capability), src (the value), imm *)
  | Lt of reg * arg * arg
  | Le of reg * arg * arg
  | Add of reg * arg * arg
  | Sub of reg * arg * arg
  | Mul of reg * arg * arg
  | LAnd of reg * arg * arg
  | LOr of reg * arg * arg
  | LShiftL of reg * arg * arg
  | LShiftR of reg * arg * arg
  | Lea of reg * reg * arg
  | SetA of reg * reg * arg
  | Restrict of reg * reg * arg
  | Subseg of reg * reg * arg * arg
  | GetB of reg * reg
  | GetE of reg * reg
  | GetLen of reg * reg
  | GetA of reg * reg
  | GetP of reg * reg
  | GetL of reg * reg
  | GetWType of reg * reg
  | GetOType of reg * reg
  | Seal of reg * reg * reg
  | UnSeal of reg * reg * reg
  | Ecall
  | Fail
  | Halt
  | GetTag of reg * reg
  | ClearTag of reg * reg
  | Auipcc of reg * expr
(* Not mirrored, since no lowering produces them: [SpecialRW], [SetMIE],
   [CsrMIE], [Mret]. *)

type code =
  | Label of string  (* #"s" *)
  | Symbol of string  (* #@"s" *)
  | Instr of instr
  | Local of code list

(* Macros of theories/case_studies/macros/, printed as calls. *)
type macro =
  | Fetch of string * reg  (* fetch_asm sym rdst (fetch.v) *)
  | Setbounds of reg * reg * int * reg * reg
      (* setbounds_asm rdst rsrc len t1 t2 (setbounds.v): rdst gets rsrc
         with bounds [a, a + len), a the address of rsrc *)

(* {1 Printing, in the notations of the DSL} *)

(* A Rocq [Z] literal, in parentheses when negative. *)
let z n = if n < 0 then Printf.sprintf "(%d)" n else string_of_int n

let str s = Printf.sprintf "%S" s

(* The Rocq constant that holds [encodePermPair (P, g)]; set by the
   printer, which defines it. *)
let perm_name : (Cheriot_perms.pair -> string) ref = ref Cheriot_perms.ident

let rec string_of_expr = function
  | Perm p -> !perm_name p
  | Lbl s -> Printf.sprintf "(%s)%%asm" (str s)
  | Z n -> z n
  | Plus (a, b) -> Printf.sprintf "(%s + %s)%%asm" (string_of_expr a) (string_of_expr b)
  | Minus (a, b) -> Printf.sprintf "(%s - %s)%%asm" (string_of_expr a) (string_of_expr b)

let string_of_arg = function E e -> string_of_expr e | R r -> string_of_reg r

let r = string_of_reg
let a = string_of_arg
let e = string_of_expr

let string_of_instr = function
  | Jmp x -> Printf.sprintf "jmp %s" (a x)
  | Jeq (o, x, y) -> (
      match y with
      | E (Z 0) -> (
          match x with R rx -> Printf.sprintf "jeqz %s %s" (a o) (r rx) | E _ -> Printf.sprintf "jeq %s %s %s" (a o) (a x) (a y))
      | _ -> Printf.sprintf "jeq %s %s %s" (a o) (a x) (a y))
  | Jne (o, x, y) -> (
      match (x, y) with
      | R rx, E (Z 0) -> Printf.sprintf "jnez %s %s" (a o) (r rx)
      | _ -> Printf.sprintf "jne %s %s %s" (a o) (a x) (a y))
  | Jlt (o, x, y) -> Printf.sprintf "jlt %s %s %s" (a o) (a x) (a y)
  | Jle (o, x, y) -> Printf.sprintf "jle %s %s %s" (a o) (a x) (a y)
  | Jalr (0, 1) -> "ret"
  | Jalr (d, s) -> Printf.sprintf "jalr %s %s" (r d) (r s)
  | Mov (d, x) -> Printf.sprintf "mov %s %s" (r d) (a x)
  | CLoad (d, s, Z 0) -> Printf.sprintf "load %s %s" (r d) (r s)
  | CLoad (d, s, i) -> Printf.sprintf "load_imm %s %s %s" (r d) (r s) (e i)
  | Store (d, x, Z 0) -> Printf.sprintf "store %s %s" (r d) (a x)
  | Store (d, x, i) -> Printf.sprintf "store_imm %s %s %s" (r d) (a x) (e i)
  | Lt (d, x, y) -> Printf.sprintf "lt %s %s %s" (r d) (a x) (a y)
  | Le (d, x, y) -> Printf.sprintf "le %s %s %s" (r d) (a x) (a y)
  | Add (d, x, y) -> Printf.sprintf "add %s %s %s" (r d) (a x) (a y)
  | Sub (d, x, y) -> Printf.sprintf "sub %s %s %s" (r d) (a x) (a y)
  | Mul (d, x, y) -> Printf.sprintf "mul %s %s %s" (r d) (a x) (a y)
  | LAnd (d, x, y) -> Printf.sprintf "land %s %s %s" (r d) (a x) (a y)
  | LOr (d, x, y) -> Printf.sprintf "lor %s %s %s" (r d) (a x) (a y)
  | LShiftL (d, x, y) -> Printf.sprintf "lshiftl %s %s %s" (r d) (a x) (a y)
  | LShiftR (d, x, y) -> Printf.sprintf "lshiftr %s %s %s" (r d) (a x) (a y)
  | Lea (d, s, x) -> Printf.sprintf "lea %s %s %s" (r d) (r s) (a x)
  | SetA (d, s, x) -> Printf.sprintf "seta %s %s %s" (r d) (r s) (a x)
  | Restrict (d, s, x) -> Printf.sprintf "restrict %s %s %s" (r d) (r s) (a x)
  | Subseg (d, s, x, y) -> Printf.sprintf "subseg %s %s %s %s" (r d) (r s) (a x) (a y)
  | GetB (d, s) -> Printf.sprintf "getb %s %s" (r d) (r s)
  | GetE (d, s) -> Printf.sprintf "gete %s %s" (r d) (r s)
  | GetLen (d, s) -> Printf.sprintf "getlen %s %s" (r d) (r s)
  | GetA (d, s) -> Printf.sprintf "geta %s %s" (r d) (r s)
  | GetP (d, s) -> Printf.sprintf "getp %s %s" (r d) (r s)
  | GetL (d, s) -> Printf.sprintf "getl %s %s" (r d) (r s)
  | GetWType (d, s) -> Printf.sprintf "getwtype %s %s" (r d) (r s)
  | GetOType (d, s) -> Printf.sprintf "getotype %s %s" (r d) (r s)
  | Seal (d, x, y) -> Printf.sprintf "seal %s %s %s" (r d) (r x) (r y)
  | UnSeal (d, x, y) -> Printf.sprintf "unseal %s %s %s" (r d) (r x) (r y)
  | Ecall -> "ecall"
  | Fail -> "fail"
  | Halt -> "halt"
  | GetTag (d, s) -> Printf.sprintf "gettag %s %s" (r d) (r s)
  | ClearTag (d, s) -> Printf.sprintf "cleartag %s %s" (r d) (r s)
  | Auipcc (d, i) -> Printf.sprintf "auipcc %s %s" (r d) (e i)

let rec string_of_code = function
  | Label s -> "#" ^ str s
  | Symbol s -> "#@" ^ str s
  | Instr i -> string_of_instr i
  | Local l -> Printf.sprintf "macro: [ %s ]" (String.concat "; " (List.map string_of_code l))

let string_of_macro = function
  | Fetch (sym, d) -> Printf.sprintf "fetch_asm %s %s" (str sym) (r d)
  | Setbounds (d, s, n, t1, t2) -> Printf.sprintf "setbounds_asm %s %s %s %s %s" (r d) (r s) (z n) (r t1) (r t2)

(* Number of instructions of a macro (its words: macros define no symbol). *)
let macro_words = function Fetch _ -> 2 | Setbounds _ -> 3
