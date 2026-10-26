From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters machine_parameters_instance
  griotte_opsem assembler switcher.
From griotte Require Import image firmware firmware_ok print.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

#[local] Open Scope string_scope.

(** * The JSON printer of firmware predicates

    [print_initial_state_json "cs" constr:(@name_annot)] prints the
    annotated predicate [name_annot] of the case study [cs] as a JSON
    document, for the predicate viewer (tools/predicate-viewer/). It follows
    the walk of [print_initial_state] (print.v): the document keeps the tree
    of the predicate (sections, conjuncts, existentials, equations, lists,
    unions), with the words it recognises structured and everything else as
    the one-line text of [pp]. The code constants of the memory come with
    their words, and their instructions and labels when they have some. *)

(** ** JSON values *)

Ltac2 Type rec json := [
  JStr (string)
| JLit (string)                  (* a number, a boolean: printed as is *)
| JArr (json list)
| JObj ((string * json) list)
].

Ltac2 chr (c : int) : string := String.make 1 (Char.of_int c).

Ltac2 hex_digit (d : int) : string :=
  if Int.lt d 10 then chr (Int.add 48 d) else chr (Int.add 87 d).

(** A JSON string literal: quotes, backslashes and control characters
    escaped, UTF-8 kept as is. *)
Ltac2 json_quote (s : string) : string :=
  let n := String.length s in
  let rec go i acc :=
    if Int.equal i n then String.concat "" (List.rev acc)
    else
      let c := Char.to_int (String.get s i) in
      let e :=
        if Int.equal c 34 then String.app (chr 92) (chr 34)
        else if Int.equal c 92 then String.app (chr 92) (chr 92)
        else if Int.equal c 10 then String.app (chr 92) "n"
        else if Int.equal c 9 then String.app (chr 92) "t"
        else if Int.equal c 13 then String.app (chr 92) "r"
        else if Int.lt c 32 then
          String.concat "" [chr 92; "u00"; hex_digit (Int.div c 16); hex_digit (Int.mod c 16)]
        else chr c in
      go (Int.add i 1) (e :: acc) in
  String.concat "" [chr 34; go 0 []; chr 34].

Ltac2 rec json_compact (j : json) : string :=
  match j with
  | JStr s => json_quote s
  | JLit s => s
  | JArr xs => String.concat "" ["["; String.concat ", " (List.map json_compact xs); "]"]
  | JObj kvs =>
      String.concat ""
        ["{"; String.concat ", " (List.map (fun kv => let (k, v) := kv in
                                    String.concat "" [json_quote k; ": "; json_compact v]) kvs); "}"]
  end.

Ltac2 json_width (_ : unit) : int := 110.

(** The lines of [j] at the indentation [ind], after [pre] (a key) and
    before [post] (a comma): on one line if it fits, otherwise one element
    per line. *)
Ltac2 rec json_lines (ind : string) (pre : string) (j : json) (post : string) : string list :=
  let one := String.concat "" [ind; pre; json_compact j; post] in
  let fits := Int.le (width one) (json_width ()) in
  let elems open close items :=
    let n := List.length items in
    let ind' := String.app ind "  " in
    List.append
      (String.concat "" [ind; pre; open] ::
       List.flat_map (fun x => x)
         (List.mapi (fun i it =>
                       let (k, v) := it in
                       json_lines ind' k v (if Int.equal i (Int.sub n 1) then "" else ",")) items))
      [String.concat "" [ind; close; post]] in
  if fits then [one] else
  match j with
  | JArr xs => match xs with [] => [one] | _ => elems "[" "]" (List.map (fun x => ("", x)) xs) end
  | JObj kvs =>
      match kvs with
      | [] => [one]
      | _ => elems "{" "}" (List.map (fun kv => let (k, v) := kv in (String.app (json_quote k) ": ", v)) kvs)
      end
  | _ => [one]
  end.

(** ** Printing helpers *)

(** Identities whose argument is printed in [Z] or [nat] scope: [pp] of a
    numeral alone prints it with its delimiter ([3%Z]), [pp] of [pz 3] gives
    [pz 3]. *)
Definition pz (z : Z) : Z := z.
Arguments pz z%_Z_scope.
Definition pnat (n : nat) : nat := n.
Arguments pnat n%_nat_scope.

(** [s] without its first [k] characters. *)
Ltac2 drop (k : int) (s : string) : string :=
  let n := String.length s in
  if Int.le n k then "" else String.sub s k (Int.sub n k).

(** The printing of [f x] without [f], for [f] [pz], [pnat] or [WInt]. *)
Ltac2 pp_arg (f : constr) (fname : string) (x : constr) : string :=
  let s := pp (Constr.Unsafe.make (Constr.Unsafe.App f (Array.of_list [x]))) in
  let k := Int.add (String.length fname) 1 in
  if sub_is s 0 (String.app fname " ") then strip_parens (drop k s) else pp x.

Ltac2 ppz (z : constr) : string := pp_arg constr:(pz) "pz" z.
Ltac2 ppn (n : constr) : string := pp_arg constr:(pnat) "pnat" n.

Ltac2 is_var (c : constr) : bool :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Var _ => true | _ => false end.

Ltac2 has_type (c : constr) (t : constr) : bool :=
  Control.plus (fun () => Constr.equal (Constr.type c) t) (fun _ => false).

Ltac2 with_comment (c : string option) (j : json) : json :=
  match c with
  | None => j
  | Some c =>
      match j with
      | JObj kvs =>
          JObj (List.append (List.filter (fun kv => let (k, _) := kv in Bool.neg (String.equal k "comment")) kvs)
                  [("comment", JStr c)])
      | _ => j
      end
  end.

(** ** Words *)

(** An address: [finz.incr_default base off] with its base and offset, a
    subtraction with a negative offset, an offset at a label of the
    switcher with its label. *)
Ltac2 addr_j (a : constr) : json :=
  Control.plus (fun () =>
    lazy_match! a with
    | finz.incr_default ?b
        (assembler.Asm_Griotte.label_offset_from (concat switcher_asm) ".Lswitch_csp_check" ?s) =>
        let s := str s in
        JObj [("text", JStr (String.concat "" [pp b; " ^+ label "; quote s]));
              ("base", JStr (pp b)); ("label", JStr s)]
    | finz.incr_default ?b (Z.opp ?o) =>
        let o := ppz o in
        let o := if contains o " " then String.concat "" ["("; o; ")"] else o in
        JObj [("text", JStr (pp a)); ("base", JStr (pp b)); ("off", JStr (String.app "-" o))]
    | finz.incr_default ?b ?o =>
        JObj [("text", JStr (pp a)); ("base", JStr (pp b)); ("off", JStr (ppz o))]
    end) (fun _ => JObj [("text", JStr (pp a))]).

Ltac2 term_word (w : constr) : json := JObj [("w", JStr "term"); ("text", JStr (pp w))].

Ltac2 seal_perm (x : constr) (y : constr) : string :=
  lazy_match! constr:(($x, $y)) with
  | (true, true) => "SU"
  | (true, false) => "S"
  | (false, true) => "U"
  | (false, false) => "O"
  end.

Ltac2 bounds (b : constr) (e : constr) (a : constr) : (string * json) list :=
  [("b", addr_j b); ("e", addr_j e); ("a", addr_j a)].

Ltac2 rec sealable_j (sb : constr) : json :=
  Control.plus (fun () =>
    lazy_match! sb with
    | SCap true ?p ?g ?b ?e ?a =>
        JObj (List.append [("w", JStr "cap"); ("p", JStr (pp p)); ("g", JStr (pp g))] (bounds b e a))
    | SSealRange true (?x, ?y) ?g ?b ?e ?a =>
        JObj (List.append [("w", JStr "sealrange"); ("perm", JStr (seal_perm x y)); ("g", JStr (pp g))]
                (bounds b e a))
    end) (fun _ => term_word constr:(WSealable $sb)).

(** A word: tagged capabilities, sentries and sealing ranges, sealed words,
    export entries and integers structured, anything else as a term. *)
Ltac2 word_j (w : constr) : json :=
  Control.plus (fun () =>
    lazy_match! w with
    | WInt (encode_entry_point ?m (Z.of_nat ?n) (Z.of_nat ?s) (Z.of_nat ?o)) =>
        JObj [("w", JStr "entry"); ("mie", JStr (pp m)); ("args", JStr (ppn n));
              ("stack", JStr (ppn s)); ("off", JStr (ppn o))]
    | WInt ?z => JObj [("w", JStr "int"); ("text", JStr (pp_arg constr:(WInt) "WInt" z))]
    | WSealable ?sb => sealable_j sb
    | WSentry ?k true ?p ?g ?b ?e ?a =>
        JObj (List.append [("w", JStr "sentry"); ("kind", JStr (pp k)); ("p", JStr (pp p)); ("g", JStr (pp g))]
                (bounds b e a))
    | WSealed ?o ?sb => JObj [("w", JStr "sealed"); ("ot", addr_j o); ("inner", sealable_j sb)]
    end) (fun _ => term_word w).

(** A list element, with the comment of its [note]. *)
Ltac2 item_j (e : constr) : json :=
  lazy_match! e with
  | note ?c ?w => with_comment (Some (str c)) (word_j w)
  | _ => word_j e
  end.

(** ** Code constants *)

(** [Some (map canon_instr l)] when the words [ws] are the encodings of
    the instructions [l]. *)
Definition code_instrs `{MachineParameters} (ws : list Word) : option (list instr) :=
  let l := map decodeInstrW ws in
  match ws with
  | [] => None
  | _ => if bool_decide (encodeInstrsW l = ws) then Some (map canon_instr l) else None
  end.

(** The blocks [lo] to [hi] (excluded) of the program by blocks [P] whose
    assembly gives the words [ws]: all the blocks, or, when [any], the
    first range of consecutive blocks that does. [None] when [P] does not
    assemble. *)
Definition asm_range `{MachineParameters} (P : list (list assembler.Asm_Griotte.asm_code))
  (ws : list Word) (any : bool) : option (nat * nat) :=
  let bs := map encodeInstrsW (assembler.Asm_Griotte.assemble_block P) in
  let n := length bs in
  let ws_of lo hi := concat (take (hi - lo) (drop lo bs)) in
  if bool_decide (n = length P ∧ ws ≠ []) then
    if bool_decide (ws_of 0 n = ws) then Some (0, n)
    else if any then
      List.find (λ c, bool_decide (ws_of (fst c) (snd c) = ws))
        (flat_map (λ lo, map (λ k, (lo, lo + S k)) (seq 0 (n - lo))) (seq 0 n))
    else None
  else None.

(** The labels of an assembler program at its outer level, with their
    offset in its instructions: symbols are data, outside the code. *)
Fixpoint asm_labels_aux (l : list assembler.Asm_Griotte.asm_code) (n : nat) : list (nat * string) :=
  match l with
  | [] => []
  | assembler.Asm_Griotte.ASM_Label s :: l => (n, s) :: asm_labels_aux l n
  | assembler.Asm_Griotte.ASM_Symbol _ :: l => asm_labels_aux l n
  | assembler.Asm_Griotte.ASM_Instr _ :: l => asm_labels_aux l (S n)
  | (assembler.Asm_Griotte.ASM_Local _ as c) :: l =>
      asm_labels_aux l (n + assembler.Asm_Griotte.asm_code_words c)
  end.

(** The labels of [l] and the number of its instructions. *)
Definition asm_labels (l : list assembler.Asm_Griotte.asm_code) : list (nat * string) * nat :=
  (asm_labels_aux l 0, length (assembler.Asm_Griotte.assemble l)).

Definition asm_block_labels (l : list (list assembler.Asm_Griotte.asm_code)) : list (nat * string) * nat :=
  (asm_labels_aux (concat l) 0, length (concat (assembler.Asm_Griotte.assemble_block l))).

(** Fixes the immediates of an instruction: [$(3%Z)] is [$3]. *)
Ltac2 fix_imm (s : string) : string :=
  let n := String.length s in
  let rec go i acc :=
    if Int.ge i n then String.concat "" (List.rev acc)
    else if sub_is s i "%Z" then go (Int.add i 2) acc
    else if sub_is s i "$(" then
      let rec close j := if Int.ge j n then n else if Int.equal (Char.to_int (String.get s j)) 41 then j
                         else close (Int.add j 1) in
      let j := close (Int.add i 2) in
      let inner := String.sub s (Int.add i 2) (Int.sub j (Int.add i 2)) in
      let inner := if sub_is inner (Int.sub (String.length inner) 2) "%Z"
                   then String.sub inner 0 (Int.sub (String.length inner) 2) else inner in
      if contains inner " " then go (Int.add i 1) ("$" :: acc)
      else go (Int.add j 1) (String.app "$" inner :: acc)
    else go (Int.add i 1) (String.make 1 (String.get s i) :: acc) in
  go 0 [].

(** The constant [cst] and its arguments, when it takes only the machine
    parameters. *)
Ltac2 code_const (c : constr) : (constant * constr) option :=
  let only_mp args := Array.for_all (fun a => has_type a constr:(MachineParameters)) args in
  let inst f args :=
    Constr.Unsafe.make (Constr.Unsafe.App f (Array.map (fun _ => constr:(machine_parameters_instance)) args)) in
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant cst _ => Some (cst, c)
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant cst _ => if only_mp args then Some (cst, inst f args) else None
      | _ => None
      end
  | _ => None
  end.

(** The labels of the code constant [cst], from the assembler program
    [<p>_asm] of a constant [<p>_instrs], when it assembles to [n] words. *)
Ltac2 code_labels (cst : constant) (n : int) : json option :=
  Control.plus (fun () =>
    let path := Env.path (Std.ConstRef cst) in
    let name := Ident.to_string (List.last path) in
    let k := String.length name in
    if Bool.and (Int.gt k 7) (String.equal (drop (Int.sub k 7) name) "_instrs") then
      match Ident.of_string (String.app (String.sub name 0 (Int.sub k 7)) "_asm") with
      | Some x =>
          match Env.get (List.append (List.removelast path) [x]) with
          | Some r =>
              let p := Env.instantiate r in
              (* a program of a section with the machine parameters *)
              let p := if has_type p constr:(MachineParameters -> list (list assembler.Asm_Griotte.asm_code))
                       then constr:($p machine_parameters_instance)
                       else if has_type p constr:(MachineParameters -> list assembler.Asm_Griotte.asm_code)
                       then constr:($p machine_parameters_instance) else p in
              let res :=
                if has_type p constr:(list (list assembler.Asm_Griotte.asm_code))
                then Std.eval_vm None constr:(asm_block_labels $p)
                else if has_type p constr:(list assembler.Asm_Griotte.asm_code)
                then Std.eval_vm None constr:(asm_labels $p)
                else Control.zero Not_found in
              lazy_match! res with
              | (?ls, ?m) =>
                  if Int.equal (leading_int (ppn m)) n then
                    let ls := List.map (fun l => lazy_match! l with (?i, ?s) => (leading_int (ppn i), str s) end)
                                (list_of ls) in
                    let ls := List.filter (fun l => let (i, _) := l in Int.lt i n) ls in
                    (* the labels at one index, joined *)
                    let rec merge ls :=
                      match ls with
                      | [] => []
                      | l :: rest =>
                          let (i, s) := l in
                          match merge rest with
                          | [] => [(i, s)]
                          | m :: ms =>
                              let (j, t) := m in
                              if Int.equal i j then (i, String.concat ", " [s; t]) :: ms else (i, s) :: m :: ms
                          end
                      end in
                    Some (JObj (List.map (fun l => let (i, s) := l in (int_str i, JStr s)) (merge ls)))
                  else None
              end
          | None => None
          end
      | None => None
      end
    else None) (fun _ => None).

(** ** Assembler sources *)

(** An operand: parenthesised when it has spaces or a sign. *)
Ltac2 operand (s : string) : string :=
  if Bool.or (contains s " ") (sub_is s 0 "-") then String.concat "" ["("; s; ")"] else s.

(** An assembler expression, its labels as written. *)
Ltac2 rec asm_expr_s (e : constr) : string :=
  lazy_match! Std.eval_hnf e with
  | assembler.Asm_Griotte.Asm_lbl ?s => str s
  | assembler.Asm_Griotte.Asm_z (Z.of_nat ?n) => ppn n
  | assembler.Asm_Griotte.Asm_z ?z => ppz z
  | assembler.Asm_Griotte.Asm_plus ?a ?b => String.concat "" [asm_operand a; " + "; asm_operand b]
  | assembler.Asm_Griotte.Asm_minus ?a ?b => String.concat "" [asm_operand a; " - "; asm_operand b]
  end
with asm_operand (e : constr) : string := operand (asm_expr_s e).

Ltac2 asm_arg_s (a : constr) : string :=
  lazy_match! Std.eval_hnf a with
  | inl ?e => asm_operand e
  | inr ?r => pp r
  end.

Ltac2 is_zero_expr (e : constr) : bool :=
  Control.plus (fun () =>
    lazy_match! Std.eval_hnf e with
    | assembler.Asm_Griotte.Asm_z ?z => String.equal (ppz z) "0"
    end) (fun _ => false).

Ltac2 is_zero_arg (a : constr) : bool :=
  Control.plus (fun () =>
    lazy_match! Std.eval_hnf a with
    | inl ?e => is_zero_expr e
    end) (fun _ => false).

(** The register of an operand, when it is one. *)
Ltac2 arg_reg (a : constr) : string option :=
  Control.plus (fun () =>
    lazy_match! Std.eval_hnf a with
    | inr ?r => Some (pp r)
    end) (fun _ => None).

(** An assembler instruction in the syntax of the asm sources: the smart
    constructors of [Asm_Griotte] ([mov], [load], [jnez], [ret], …). *)
Ltac2 asm_instr_s (i : constr) : string :=
  let f m xs := String.concat " " (m :: xs) in
  let r := pp in
  let a := asm_arg_s in
  let e := asm_operand in
  let cond m mz o x y :=
    match arg_reg x with
    | Some rx => if is_zero_arg y then f mz [a o; rx] else f m [a o; a x; a y]
    | None => f m [a o; a x; a y]
    end in
  lazy_match! Std.eval_hnf i with
  | assembler.Asm_Griotte.Jmp ?x => f "jmp" [a x]
  | assembler.Asm_Griotte.Jeq ?o ?x ?y => cond "jeq" "jeqz" o x y
  | assembler.Asm_Griotte.Jne ?o ?x ?y => cond "jne" "jnez" o x y
  | assembler.Asm_Griotte.Jlt ?o ?x ?y => f "jlt" [a o; a x; a y]
  | assembler.Asm_Griotte.Jle ?o ?x ?y => f "jle" [a o; a x; a y]
  | assembler.Asm_Griotte.Jalr ?d ?s =>
      if Bool.and (String.equal (r d) "cnull") (String.equal (r s) "cra") then "ret"
      else f "jalr" [r d; r s]
  | assembler.Asm_Griotte.Mov ?d ?s => f "mov" [r d; a s]
  | assembler.Asm_Griotte.CLoad ?d ?s ?x =>
      if is_zero_expr x then f "load" [r d; r s] else f "load_imm" [r d; r s; e x]
  | assembler.Asm_Griotte.Store ?d ?s ?x =>
      if is_zero_expr x then f "store" [r d; a s] else f "store_imm" [r d; a s; e x]
  | assembler.Asm_Griotte.Lt ?d ?x ?y => f "lt" [r d; a x; a y]
  | assembler.Asm_Griotte.Le ?d ?x ?y => f "le" [r d; a x; a y]
  | assembler.Asm_Griotte.Add ?d ?x ?y => f "add" [r d; a x; a y]
  | assembler.Asm_Griotte.Sub ?d ?x ?y => f "sub" [r d; a x; a y]
  | assembler.Asm_Griotte.Mul ?d ?x ?y => f "mul" [r d; a x; a y]
  | assembler.Asm_Griotte.LAnd ?d ?x ?y => f "land" [r d; a x; a y]
  | assembler.Asm_Griotte.LOr ?d ?x ?y => f "lor" [r d; a x; a y]
  | assembler.Asm_Griotte.LShiftL ?d ?x ?y => f "lshiftl" [r d; a x; a y]
  | assembler.Asm_Griotte.LShiftR ?d ?x ?y => f "lshiftr" [r d; a x; a y]
  | assembler.Asm_Griotte.Lea ?d ?s ?x => f "lea" [r d; r s; a x]
  | assembler.Asm_Griotte.SetA ?d ?s ?x => f "seta" [r d; r s; a x]
  | assembler.Asm_Griotte.Restrict ?d ?s ?x => f "restrict" [r d; r s; a x]
  | assembler.Asm_Griotte.Subseg ?d ?s ?x ?y => f "subseg" [r d; r s; a x; a y]
  | assembler.Asm_Griotte.GetB ?d ?s => f "getb" [r d; r s]
  | assembler.Asm_Griotte.GetE ?d ?s => f "gete" [r d; r s]
  | assembler.Asm_Griotte.GetLen ?d ?s => f "getlen" [r d; r s]
  | assembler.Asm_Griotte.GetA ?d ?s => f "geta" [r d; r s]
  | assembler.Asm_Griotte.GetP ?d ?s => f "getp" [r d; r s]
  | assembler.Asm_Griotte.GetL ?d ?s => f "getl" [r d; r s]
  | assembler.Asm_Griotte.GetWType ?d ?s => f "getwtype" [r d; r s]
  | assembler.Asm_Griotte.GetOType ?d ?s => f "getotype" [r d; r s]
  | assembler.Asm_Griotte.Seal ?d ?x ?y => f "seal" [r d; r x; r y]
  | assembler.Asm_Griotte.UnSeal ?d ?x ?y => f "unseal" [r d; r x; r y]
  | assembler.Asm_Griotte.SpecialRW ?d ?sr ?x =>
      let src_null := match arg_reg x with Some s => String.equal s "cnull" | None => false end in
      if src_null then f "csrr" [r d; r sr]
      else if String.equal (r d) "cnull" then f "csrw" [r sr; a x]
      else f "specialrw" [r d; r sr; a x]
  | assembler.Asm_Griotte.SetMIE ?b => f "setmie" [r b]
  | assembler.Asm_Griotte.CsrMIE InterruptEnabled ?sr ?m => f "csrsi" [r sr; e m]
  | assembler.Asm_Griotte.CsrMIE InterruptDisabled ?sr ?m => f "csrci" [r sr; e m]
  | assembler.Asm_Griotte.Mret => "mret"
  | assembler.Asm_Griotte.Fail => "fail"
  | assembler.Asm_Griotte.Halt => "halt"
  | assembler.Asm_Griotte.GetTag ?d ?s => f "gettag" [r d; r s]
  | assembler.Asm_Griotte.ClearTag ?d ?s => f "cleartag" [r d; r s]
  | assembler.Asm_Griotte.Auipcc ?d ?x => f "auipcc" [r d; e x]
  end.

(** A line of an assembler source: a label, or a symbol or an instruction
    with its word offset in the program. *)
Ltac2 Type asm_line := [ ALabel (string) | ASym (string, int) | AInstr (string, int) ].

(** The lines of the code [l] of the block [bi] at the nesting [d], in
    reverse order in [acc], from the word offset [off]. *)
Ltac2 rec asm_walk (acc : (int * int * asm_line) list ref) (off : int ref) (bi : int) (d : int)
  (l : constr) : unit :=
  lazy_match! Std.eval_hnf l with
  | nil => ()
  | cons ?c ?rest =>
      let push x := acc.(contents) := (bi, d, x) :: acc.(contents) in
      let o := off.(contents) in
      (lazy_match! Std.eval_hnf c with
       | assembler.Asm_Griotte.ASM_Label ?s => push (ALabel (str s))
       | assembler.Asm_Griotte.ASM_Symbol ?s => push (ASym (str s) o); off.(contents) := Int.add o 1
       | assembler.Asm_Griotte.ASM_Instr ?i => push (AInstr (asm_instr_s i) o); off.(contents) := Int.add o 1
       | assembler.Asm_Griotte.ASM_Local ?l' => asm_walk acc off bi (Int.add d 1) l'
       end);
      asm_walk acc off bi d rest
  end.

(** The [asm] lines of the blocks [lo] to [hi] (excluded) of the program
    [p], by blocks when [blocks]. The index of a word is its offset from
    the first instruction of the block [lo]: the symbols of the data prefix
    have negative indices. *)
Ltac2 asm_lines (p : constr) (blocks : bool) (lo : int) (hi : int) : json list :=
  let acc := { contents := [] } in
  let off := { contents := 0 } in
  (if blocks then
     let rec go bi l :=
       lazy_match! Std.eval_hnf l with
       | nil => ()
       | cons ?b ?rest => asm_walk acc off bi 0 b; go (Int.add bi 1) rest
       end in
     go 0 p
   else asm_walk acc off 0 0 p);
  let lines := List.rev (acc.(contents)) in
  let first_instr :=
    List.fold_right (fun l r => match l with (_, _, AInstr _ o) => o | _ => r end) lines (off.(contents)) in
  let prefix := List.length (List.filter (fun l => match l with
                                                   | (_, _, ASym _ o) => Int.lt o first_instr
                                                   | _ => false
                                                   end) lines) in
  let base := List.length (List.filter (fun l => match l with
                                                 | (bi, _, AInstr _ _) => Int.lt bi lo
                                                 | _ => false
                                                 end) lines) in
  let idx o := JLit (int_str (Int.sub (Int.sub o prefix) base)) in
  let line_j l :=
    match l with
    | (_, d, ALabel s) => JObj [("label", JStr s); ("depth", JLit (int_str d))]
    | (_, d, ASym s o) => JObj [("symbol", JStr s); ("index", idx o); ("depth", JLit (int_str d))]
    | (_, d, AInstr s o) => JObj [("instr", JStr s); ("index", idx o); ("depth", JLit (int_str d))]
    end in
  let rec from bi :=
    if Int.ge bi hi then [] else
    let here := List.map line_j (List.filter (fun l => match l with (b, _, _) => Int.equal b bi end) lines) in
    List.append (if blocks then JObj [("block", JLit (int_str bi))] :: here else here) (from (Int.add bi 1)) in
  from lo.

(** The assembler programs that do not follow the naming convention
    [<p>_code] or [<p>_instrs] beside [<p>_asm]: the code constant, its
    program (a constant of the same module) and the program's arguments
    other than the machine parameters. The words of the constant may be a
    range of the blocks of the program. *)
Section asm_table_args.
  #[local] Existing Instance machine_parameters_instance.
  (** The encodings of the capabilities of [droe] and [dle], abstract in
      their programs. *)
  Definition asm_arg_droe : Z := encodePermPair (RO_DRO, Global).
  Definition asm_arg_dle : Z := encodePermPair (RW_DL, Local).
End asm_table_args.

Ltac2 asm_table (_ : unit) : (string * string * constr list) list :=
  let body c := Std.eval_unfold [(c, Std.AllOccurrences)] (Env.instantiate c) in
  [("droe_main_code", "droe_main_asm", [body reference:(asm_arg_droe)]);
   ("dle_main_code", "dle_main_asm", [body reference:(asm_arg_dle)]);
   ("switcher_call_instrs", "switcher_asm", [])].

(** [p] applied to the machine parameters and to [args], in the order of
    its binders. *)
Ltac2 rec apply_asm (p : constr) (args : constr list) : constr :=
  let app x := Constr.Unsafe.make (Constr.Unsafe.App p (Array.of_list [x])) in
  match Constr.Unsafe.kind (Constr.type p) with
  | Constr.Unsafe.Prod b _ =>
      if Constr.equal (Constr.Binder.type b) constr:(MachineParameters)
      then apply_asm (app constr:(machine_parameters_instance)) args
      else match args with
           | x :: rest => apply_asm (app x) rest
           | [] => p
           end
  | _ => p
  end.

(** The [asm_source] and [asm] fields of the code constant [cst] whose
    words are [ws]: its program by the table, or by name, when assembling
    it gives [ws]. *)
Ltac2 code_asm (cst : constant) (ws : constr) : (string * json) list :=
  let path := Env.path (Std.ConstRef cst) in
  let name := Ident.to_string (List.last path) in
  let k := String.length name in
  let ends sfx := let m := String.length sfx in
                  Bool.and (Int.gt k m) (String.equal (drop (Int.sub k m) name) sfx) in
  let by_name :=
    let p := if ends "_code" then Some (String.sub name 0 (Int.sub k 5))
             else if ends "_instrs" then Some (String.sub name 0 (Int.sub k 7)) else None in
    match p with Some p => [(String.app p "_asm", [], false)] | None => [] end in
  let by_table :=
    List.flat_map (fun e => let (c, a, args) := e in if String.equal c name then [(a, args, true)] else [])
      (asm_table ()) in
  let try_one cand :=
    let (a, args, any) := cand in
    Control.plus (fun () =>
      match Ident.of_string a with
      | Some x =>
          match Env.get (List.append (List.removelast path) [x]) with
          | Some r =>
              let p := apply_asm (Env.instantiate r) args in
              let (blocks, pb) :=
                if has_type p constr:(list (list assembler.Asm_Griotte.asm_code)) then (true, p)
                else if has_type p constr:(list assembler.Asm_Griotte.asm_code) then (false, constr:([$p]))
                else Control.zero Not_found in
              let any := if any then constr:(true) else constr:(false) in
              lazy_match! Std.eval_vm None constr:(@asm_range machine_parameters_instance $pb $ws $any) with
              | Some (?lo, ?hi) =>
                  let lo := leading_int (ppn lo) in
                  let hi := leading_int (ppn hi) in
                  Some [("asm_source", JStr (pp p)); ("asm", JArr (asm_lines p blocks lo hi))]
              | None => None
              end
          | None => None
          end
      | None => None
      end) (fun _ => None) in
  let rec first cs :=
    match cs with
    | [] => []
    | c :: rest => match try_one c with Some r => r | None => first rest end
    end in
  first (List.append by_table by_name).

(** The entry of the code constant [c] in the [code] table, when it
    computes to a closed list of words, or of instructions (their
    encodings). The words are computed with the concrete machine parameters
    [machine_parameters_instance]. *)
Ltac2 code_entry (c : constr) : (string * json) option :=
  match code_const c with
  | Some cc =>
      let (cst, ci) := cc in
      let ci := if has_type ci constr:(list instr)
                then constr:(@encodeInstrsW machine_parameters_instance $ci) else ci in
      Control.plus (fun () =>
        if has_type ci constr:(list Word) then
          let ws := list_of (Std.eval_vm None ci) in
          let words := ("words", JArr (List.map word_j ws)) in
          let n := List.length ws in
          let instrs :=
            lazy_match! (Std.eval_vm None constr:(@code_instrs machine_parameters_instance $ci)) with
            | Some ?l => [("instrs", JArr (List.map (fun i => JStr (fix_imm (pp i))) (list_of l)))]
            | None => []
            end in
          let labels := match code_labels cst n with Some l => [("labels", l)] | None => [] end in
          let asm := code_asm cst ci in
          Some (pp c, JObj (List.append (words :: instrs) (List.append labels asm)))
        else None) (fun _ => None)
  | None => None
  end.

(** ** The walk *)

Ltac2 stmt (k : string) (fields : (string * json) list) : json := JObj (("k", JStr k) :: fields).

Ltac2 prop_j (p : constr) : json := stmt "prop" [("text", JStr (pp p))].

Ltac2 set_comment_j (c : string) (js : json list) : json list :=
  match js with
  | [] => []
  | j :: rest => with_comment (Some c) j :: rest
  end.

Ltac2 binders_j (hs : (ident * constr) list) : json :=
  JArr (List.map (fun g => let (xs, t) := g in
                   JObj [("names", JArr (List.map (fun x => JStr x) xs)); ("type", JStr (pp_type t))])
          (group_binders (List.map (fun h => let (x, t) := h in (x, None, t)) hs))).

(** The kind of a left-hand side the viewer recognises. *)
Ltac2 lhs_kind (l : constr) : json option :=
  let field c :=
    Some (JObj [("kind", JStr "field"); ("field", JStr (first_word (pp l))); ("of", JStr (pp c))]) in
  Control.plus (fun () =>
    lazy_match! l with
    | pcc _ => Some (JObj [("kind", JStr "reg"); ("bank", JStr "pc")])
    | mem _ => Some (JObj [("kind", JStr "mem")])
    | shadowtbl _ => Some (JObj [("kind", JStr "shadow")])
    | reg _ !! ?r => Some (JObj [("kind", JStr "reg"); ("bank", JStr "gpr"); ("name", JStr (pp r))])
    | sreg _ !! ?r => Some (JObj [("kind", JStr "reg"); ("bank", JStr "sreg"); ("name", JStr (pp r))])
    | _ =>
        match Constr.Unsafe.kind l with
        | Constr.Unsafe.Proj _ _ c => if is_var c then field c else None
        | Constr.Unsafe.App f args =>
            let n := Array.length args in
            let head_ok :=
              match Constr.Unsafe.kind f with
              | Constr.Unsafe.Constant _ _ => true
              | Constr.Unsafe.Proj _ _ _ => true
              | _ => false
              end in
            if Bool.and head_ok (Array.for_all is_var args) then field (Array.get args (Int.sub n 1)) else None
        | _ => None
        end
    end) (fun _ => None).

(** The head constant and the arguments of an application, the types and
    the machine parameters excepted. *)
Ltac2 app_head_args (c : constr) : (string * json) list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      match Constr.Unsafe.kind f with
      | Constr.Unsafe.Constant cst _ =>
          let is_type a :=
            Control.plus (fun () => match Constr.Unsafe.kind (Constr.type a) with
                                    | Constr.Unsafe.Sort _ => true
                                    | _ => false
                                    end) (fun _ => false) in
          let args := List.filter (fun a => Bool.neg (Bool.or (is_type a) (has_type a constr:(MachineParameters))))
                        (Array.to_list args) in
          match args with
          | [] => []
          | _ =>
              [("head", JStr (Ident.to_string (List.last (Env.path (Std.ConstRef cst)))));
               ("args", JArr (List.map (fun a => if has_type a constr:(Word) then word_j a
                                                 else term_word a) args))]
          end
      | _ => []
      end
  | _ => []
  end.

(** The [unfolded] field of an application of a constant (but [replicate])
    that is a literal list once its head is unfolded and beta-reduced. *)
Ltac2 unfolded_j (c : constr) : (string * json) list :=
  Control.plus (fun () =>
    match Constr.Unsafe.kind c with
    | Constr.Unsafe.App f _ =>
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Constant cst _ =>
            if String.equal (Ident.to_string (List.last (Env.path (Std.ConstRef cst)))) "replicate"
            then []
            else
              let u := Std.eval_cbv
                { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
                  Std.rZeta := false; Std.rDelta := false; Std.rConst := [Std.ConstRef cst];
                  Std.rStrength := Std.Norm } c in
              match list_of u with
              | [] => []
              | xs => [("unfolded", JArr (List.map item_j xs))]
              end
        | _ => []
        end
    | _ => []
    end) (fun _ => []).

(** The lists [c] of the subterms [length c] of [t]. *)
Ltac2 rec lengths_of (t : constr) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      let here := lazy_match! t with
                  | length ?c => [c]
                  | _ => []
                  end in
      List.append here (List.append (lengths_of f) (List.flat_map lengths_of (Array.to_list args)))
  | _ => []
  end.

Ltac2 rec conses (ws : constr) : constr list * constr :=
  lazy_match! ws with
  | cons ?w ?t => let (xs, r) := conses t in (w :: xs, r)
  | _ => ([], ws)
  end.

(** The pieces of the contents of a region, split on [++] and [::]. *)
Ltac2 rec pieces (cands : constr list ref) (ws : constr) : json list :=
  lazy_match! ws with
  | app ?a ?b => List.append (pieces cands a) (pieces cands b)
  | nil => []
  | cons _ _ =>
      let (xs, rest) := conses ws in
      JObj [("words", JArr (List.map item_j xs))] :: pieces cands rest
  | _ =>
      cands.(contents) := ws :: cands.(contents);
      [JObj (("term", JStr (pp ws)) :: List.append (app_head_args ws) (unfolded_j ws))]
  end.

Ltac2 part_j (cands : constr list ref) (e : constr) : json :=
  let (m, c) := lazy_match! e with
                | note ?c ?m => (m, Some (str c))
                | _ => (e, None)
                end in
  with_comment c
    (lazy_match! m with
     | mem_region ?b ?ws =>
         JObj [("region", JLit "true"); ("base", addr_j b); ("content", JArr (pieces cands ws))]
     | _ => JObj [("region", JLit "false"); ("text", JStr (pp m))]
     end).

Ltac2 range_j (e : constr) : json :=
  let range b x := JObj [("b", addr_j b); ("e", addr_j x)] in
  lazy_match! e with
  | note ?c (?b, ?x) => with_comment (Some (str c)) (range b x)
  | (?b, ?x) => range b x
  | _ => JObj [("text", JStr (pp e))]
  end.

Ltac2 rhs_j (cands : constr list ref) (r : constr) : json :=
  let word some w :=
    JObj (List.append [("r", JStr "word")]
            (List.append (if some then [("some", JLit "true")] else []) [("word", word_j w)])) in
  let term () :=
    (cands.(contents) := r :: cands.(contents));
    JObj [("r", JStr "term"); ("text", JStr (pp r))] in
  lazy_match! r with
  | cons _ _ => JObj [("r", JStr "list"); ("items", JArr (List.map item_j (list_of r)))]
  | @union _ _ _ _ => JObj [("r", JStr "union"); ("parts", JArr (List.map (part_j cands) (unions r)))]
  | Some ?w => if has_type w constr:(Word) then word true w else term ()
  | _ => if has_type r constr:(Word) then word false r else term ()
  end.

Ltac2 eq_j (cands : constr list ref) (p : constr) (l : constr) (r : constr) : json :=
  (* a layout equation [a + n = Some b] *)
  let layout :=
    Control.plus (fun () =>
      lazy_match! constr:(($l, $r)) with
      | (finz.incr ?a ?n, Some ?b) =>
          cands.(contents) := List.append (List.rev (lengths_of n)) (cands.(contents));
          Some (JObj [("kind", JStr "incr"); ("base", addr_j a); ("off", JStr (ppz n))],
                JObj [("r", JStr "addr"); ("some", JLit "true"); ("addr", addr_j b)])
      end) (fun _ => None) in
  match layout with
  | Some (k, rhs) => stmt "eq" [("lhs", JStr (pp l)); ("lhs_kind", k); ("rhs", rhs)]
  | None =>
  let kind := match lhs_kind l with Some k => [("lhs_kind", k)] | None => [] end in
  (* the comment that [label_eq] gives the exception entry *)
  let c := match label_eq "" p with
           | Some pl => match pl with PEq _ _ _ c => c | _ => None end
           | None => None
           end in
  with_comment c (stmt "eq" (List.append (("lhs", JStr (pp l)) :: kind) [("rhs", rhs_j cands r)]))
  end.

(** The elements of a set [{[x; …; z]}]. *)
Ltac2 rec set_elems (s : constr) : constr list :=
  lazy_match! s with
  | @union _ _ ?a ?b => List.append (set_elems a) (set_elems b)
  | @singleton _ _ _ ?x => [x]
  | @empty _ _ => []
  end.

(** The statement [∀ r : RegName, r ∉ {[…]} → reg σ !! r = Some w] (or on
    [sreg σ]). *)
Ltac2 regs_except_j (p : constr) : json option :=
  Control.plus (fun () =>
    match Constr.Unsafe.kind p with
    | Constr.Unsafe.Prod b body =>
        if Constr.equal (Constr.Binder.type b) constr:(RegName) then
          let x := Fresh.in_goal @r in
          let vx := Constr.Unsafe.make (Constr.Unsafe.Var x) in
          let bd := Constr.Unsafe.substnl [vx] 0 body in
          let (a, s, bank, v, rhs) :=
            lazy_match! bd with
            | ?a ∉ ?s -> reg _ !! ?v = ?rhs => (a, s, "gpr", v, rhs)
            | ?a ∉ ?s -> sreg _ !! ?v = ?rhs => (a, s, "sreg", v, rhs)
            end in
          if Bool.and (Constr.equal a vx) (Constr.equal v vx) then
            let (some, w) := lazy_match! rhs with
                             | Some ?w => (true, w)
                             | _ => (false, rhs)
                             end in
            let all :=
              if String.equal bank "gpr" then
                List.map (fun r => JStr (pp r))
                  (list_of (Std.eval_cbv
                     { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
                       Std.rZeta := false; Std.rDelta := false; Std.rConst := [reference:(all_registers)];
                       Std.rStrength := Std.Norm } constr:(all_registers)))
              else [] in
            Some (stmt "regs_except"
                    [("bank", JStr bank); ("except", JArr (List.map (fun e => JStr (pp e)) (set_elems s)));
                     ("all", JArr all); ("value", word_j w); ("some", JLit (if some then "true" else "false"));
                     ("text", JStr (pp p))])
          else None
        else None
    | _ => None
    end) (fun _ => None).

(** The walk of [walk] (print.v): the statements of [p]. *)
Ltac2 rec walk_j (cands : constr list ref) (p : constr) : json list :=
  match ex_head [] p with
  | Some _ => Control.plus (fun () => walk_ex_j cands [] p) (fun _ => [prop_j p])
  | None =>
  lazy_match! p with
  | section ?t ?q => [stmt "section" [("title", JStr (str t)); ("body", JArr (walk_j cands q))]]
  | ?a ∧ ?b => List.append (walk_j cands a) (walk_j cands b)
  | note ?c ?q => set_comment_j (str c) (walk_j cands q)
  | ranges_disjoint ?l => [stmt "disjoint" [("ranges", JArr (List.map range_j (list_of l)))]]
  | ?l = ?r => [eq_j cands p l r]
  | _ => match regs_except_j p with Some j => [j] | None => [prop_j p] end
  end
  end
(** The existential [p] under the binders [acc], in reverse order. *)
with walk_ex_j (cands : constr list ref) (acc : (ident * constr) list) (p : constr) : json list :=
  match ex_head [] p with
  | Some h =>
      let (x, t, bd) := h in
      let r := { contents := [] } in
      let _ := Constr.in_context x t (fun () =>
                 r.(contents) :=
                   walk_ex_j cands ((x, t) :: acc)
                     (Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var x)] 0 bd)) in
      r.(contents)
  | None => [stmt "exists" [("binders", binders_j (List.rev acc)); ("body", JArr (walk_j cands p))]]
  end.

(** The entries of the code table, from the candidates in reverse order,
    each name once. *)
Ltac2 code_table (cands : constr list) : (string * json) list :=
  let seen := { contents := [] } in
  List.fold_left (fun acc c =>
    let s := pp c in
    if List.exist (String.equal s) (seen.(contents)) then acc
    else
      (seen.(contents) := s :: seen.(contents);
       match code_entry c with Some e => List.append acc [e] | None => acc end))
    [] (List.rev cands).

(** The JSON document of the annotated predicate [c] of the case study
    [cs]: its body, with the existentials of the offsets in place (renamed
    as in the [.txt], not hoisted). *)
Ltac2 initial_state_json (cs : string) (c : constr) : json :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant cst _ =>
      let name := strip_annot (Ident.to_string (List.last (Env.path (Std.ConstRef cst)))) in
      let body := Std.eval_cbv
        { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
          Std.rZeta := false; Std.rDelta := false; Std.rConst := [Std.ConstRef cst];
          Std.rStrength := Std.Norm } c in
      let r := { contents := JObj [] } in
      with_goal (fun () => under_binders [] [] body (fun hs es p =>
        let hs := List.filter (fun h => let (_, t) := h in
                                Bool.neg (Constr.equal t constr:(MachineParameters))) hs in
        let (p, _) := rename_offsets p in
        let cands := { contents := [] } in
        let stmts := walk_j cands p in
        let body := match es with
                    | [] => stmts
                    | _ => [stmt "exists" [("binders", binders_j es); ("body", JArr stmts)]]
                    end in
        let code := code_table (cands.(contents)) in
        r.(contents) :=
          JObj [("schema", JLit "1"); ("case_study", JStr cs); ("predicate", JStr name);
                ("params", binders_j hs); ("body", JArr body); ("code", JObj code)]));
      r.(contents)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "print_initial_state_json: not a constant")))
  end.

(** Prints the annotated predicate [c] of the case study [cs], given as
    [constr:(@name_annot)], as one JSON document. *)
Ltac2 print_initial_state_json (cs : string) (c : constr) : unit :=
  print_lines (json_lines "" "" (initial_state_json cs c) "").
