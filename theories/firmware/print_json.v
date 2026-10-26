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
          Some (pp c, JObj (List.append (words :: instrs) labels))
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
      [JObj (("term", JStr (pp ws)) :: app_head_args ws)]
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
  | _ => [prop_j p]
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
