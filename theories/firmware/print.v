From Stdlib Require Import Ascii.
From stdpp Require Import gmap strings.
From griotte Require Import machine_base machine_parameters switcher.
From griotte Require Import image firmware firmware_ok.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Set Mangle Names.

#[local] Open Scope string_scope.

(** * Printers for firmware predicates and concrete images

    [print_initial_state constr:(@name_annot)] prints a predicate with
    [section] and [note] markers, with headings, indexed lists and
    right-hand comments. [print_memory_map img] prints a concrete image as
    a table of its regions. Both are reading aids only: [Print] of the
    erased predicate is the reference. *)

(** ** Printing notations

    Imported by the files that print. *)
Module FwPrintNotations.
  (** Capabilities as tuples: a memory capability [(p, g, b, e, a)], a
      sentry [(E-k p, g, b, e, a)], a sealing range [[sp, g, b, e, a]] with
      the seal permissions [S] (seal only), [U] (unseal only), [SU] (both)
      or [O] (none), and a sealed word [{ o, sb }]. *)
  Notation "( p , g , b , e , a )" := (SCap true p g b e a)
    (only printing, format "( p ,  g ,  b ,  e ,  a )").
  Notation "[ 'SU' , g , b , e , a ]" := (SSealRange true (true, true) g b e a)
    (only printing, format "[ 'SU' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'S' , g , b , e , a ]" := (SSealRange true (true, false) g b e a)
    (only printing, format "[ 'S' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'U' , g , b , e , a ]" := (SSealRange true (false, true) g b e a)
    (only printing, format "[ 'U' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'O' , g , b , e , a ]" := (SSealRange true (false, false) g b e a)
    (only printing, format "[ 'O' ,  g ,  b ,  e ,  a ]").
  Notation "sb" := (WSealable sb) (only printing, at level 0, sb at level 0).
  (* The abbreviations [WCap] and [WSealRange] take precedence over the
     notation above: the same notations on whole words. *)
  Notation "( p , g , b , e , a )" := (WSealable (SCap true p g b e a))
    (only printing, format "( p ,  g ,  b ,  e ,  a )").
  Notation "[ 'SU' , g , b , e , a ]" := (WSealable (SSealRange true (true, true) g b e a))
    (only printing, format "[ 'SU' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'S' , g , b , e , a ]" := (WSealable (SSealRange true (true, false) g b e a))
    (only printing, format "[ 'S' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'U' , g , b , e , a ]" := (WSealable (SSealRange true (false, true) g b e a))
    (only printing, format "[ 'U' ,  g ,  b ,  e ,  a ]").
  Notation "[ 'O' , g , b , e , a ]" := (WSealable (SSealRange true (false, false) g b e a))
    (only printing, format "[ 'O' ,  g ,  b ,  e ,  a ]").
  Notation "( 'E-' k p , g , b , e , a )" := (WSentry k true p g b e a)
    (only printing, k at level 0, p at level 0,
     format "( 'E-' k  p ,  g ,  b ,  e ,  a )").
  Notation "{ o , sb }" := (WSealed o sb)
    (only printing, format "{  o ,  sb  }").
  Notation "'entry' m n off" := (WInt (encode_entry_point m (Z.of_nat n) (Z.of_nat off)))
    (only printing, at level 10, m at level 0, n at level 0, off at level 0).
End FwPrintNotations.

(** Notations for the leaves of a concrete memory map: canonical
    registers, literal addresses and otypes, integers. *)
Module FwMapNotations.
  Export FwPrintNotations.
  Notation "'cnull'" := (registers.R 0 eq_refl) (only printing).
  Notation "'cra'" := (registers.R 1 eq_refl) (only printing).
  Notation "'csp'" := (registers.R 2 eq_refl) (only printing).
  Notation "'cgp'" := (registers.R 3 eq_refl) (only printing).
  Notation "'ctp'" := (registers.R 4 eq_refl) (only printing).
  Notation "'ct0'" := (registers.R 5 eq_refl) (only printing).
  Notation "'ct1'" := (registers.R 6 eq_refl) (only printing).
  Notation "'ct2'" := (registers.R 7 eq_refl) (only printing).
  Notation "'cs0'" := (registers.R 8 eq_refl) (only printing).
  Notation "'cs1'" := (registers.R 9 eq_refl) (only printing).
  Notation "'ca0'" := (registers.R 10 eq_refl) (only printing).
  Notation "'ca1'" := (registers.R 11 eq_refl) (only printing).
  Notation "'ca2'" := (registers.R 12 eq_refl) (only printing).
  Notation "'ca3'" := (registers.R 13 eq_refl) (only printing).
  Notation "'ca4'" := (registers.R 14 eq_refl) (only printing).
  Notation "'ca5'" := (registers.R 15 eq_refl) (only printing).
  Notation "'$' z" := (@inl Z RegName z)
    (only printing, at level 1, z at level 0, format "'$' z").
  Notation "r" := (@inr Z RegName r) (only printing, at level 0, r at level 0).
  Notation "z" := (@finz.FinZ MemNum z eq_refl eq_refl)
    (only printing, at level 0, z at level 0).
  Notation "'OT' z" := (@finz.FinZ ONum z eq_refl eq_refl)
    (only printing, at level 1, z at level 0).
  Notation "z" := (WInt z) (only printing, at level 0, z at level 0).
End FwMapNotations.

(** ** Ltac2 utilities *)

Ltac2 rec flat_aux (s : string) (i : int) (n : int) (sp : bool) (acc : string list) :=
  if Int.equal i n then List.rev acc else
  let c := Char.to_int (String.get s i) in
  if Int.equal c 34 then flat_aux s (Int.add i 1) n sp acc
  else if Int.le c 32 then
    if sp then flat_aux s (Int.add i 1) n true acc
    else flat_aux s (Int.add i 1) n true (" " :: acc)
  else flat_aux s (Int.add i 1) n false (String.make 1 (Char.of_int c) :: acc).

(** One line, without string quotes nor surrounding spaces. *)
Ltac2 rec trim_end (s : string) : string :=
  let n := String.length s in
  if Int.ge n 1 then
    if Int.equal (Char.to_int (String.get s (Int.sub n 1))) 32 then trim_end (String.sub s 0 (Int.sub n 1))
    else s
  else s.

Ltac2 rec trim_start (s : string) : string :=
  let n := String.length s in
  if Int.ge n 1 then
    if Int.equal (Char.to_int (String.get s 0)) 32 then trim_start (String.sub s 1 (Int.sub n 1))
    else s
  else s.

Ltac2 flat (s : string) : string :=
  trim_start (trim_end (String.concat "" (flat_aux s 0 (String.length s) false []))).

(** [Message.of_constr] parenthesises applications: strip one pair of outer
    parentheses when it encloses the whole string and is not a tuple's. A
    half-open range [[b, e)] counts as a pair. *)
Ltac2 strip_parens (s : string) : string :=
  let n := String.length s in
  let ch i := Char.to_int (String.get s i) in
  (* a binder ([∀], [∃], UTF-8 lead byte 226) right after the parenthesis:
     its comma is not a tuple's *)
  let binder := if Int.ge n 2 then Int.equal (ch 1) 226 else false in
  let rec closes_at_end i depth :=
    if Int.equal i n then Int.equal depth 0
    else
      let c := ch i in
      let d := if Int.equal c 40 then Int.add depth 1
               else if Int.equal c 91 then Int.add depth 1
               else if Int.equal c 41 then Int.sub depth 1
               else if Int.equal c 93 then Int.sub depth 1 else depth in
      if Int.equal d 0 then Int.equal i (Int.sub n 1)
      else if Int.equal c 44 then
        (* a comma at the outer level: the parentheses are a tuple's *)
        if Int.equal d 1 then (if binder then closes_at_end (Int.add i 1) d else false)
        else closes_at_end (Int.add i 1) d
      else closes_at_end (Int.add i 1) d in
  if Int.ge n 2 then
    if Int.equal (ch 0) 40 then
      if closes_at_end 0 0 then String.sub s 1 (Int.sub n 2) else s
    else s
  else s.

Ltac2 pp (c : constr) : string :=
  strip_parens (flat (Message.to_string (Message.of_constr c))).

(** A Gallina string literal, read independently of the open scopes. *)
Ltac2 bit (b : constr) : int :=
  lazy_match! b with
  | true => 1
  | false => 0
  end.

Ltac2 rec string_of_constr (c : constr) : string :=
  lazy_match! c with
  | EmptyString => ""
  | String (Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7) ?s =>
      let n := List.fold_left (fun acc b => Int.add (Int.mul acc 2) (bit b)) 0
                 [b7; b6; b5; b4; b3; b2; b1; b0] in
      String.app (String.make 1 (Char.of_int n)) (string_of_constr s)
  end.

(** The text of a string, or the printing of the term if it is not a
    literal. *)
Ltac2 str (c : constr) : string :=
  Control.plus (fun () => string_of_constr (Std.eval_vm None c)) (fun _ => pp c).

(** The display width of a string: its UTF-8 characters. *)
Ltac2 width (s : string) : int :=
  let n := String.length s in
  let rec go i acc :=
    if Int.equal i n then acc
    else
      let c := Char.to_int (String.get s i) in
      go (Int.add i 1)
        (if Int.ge c 128 then (if Int.lt c 192 then acc else Int.add acc 1) else Int.add acc 1) in
  go 0 0.

Ltac2 spaces (k : int) : string :=
  if Int.le k 0 then "" else String.make k (Char.of_int 32).

Ltac2 pad (s : string) (n : int) : string := String.app s (spaces (Int.sub n (width s))).

Ltac2 rec rule (k : int) : string :=
  if Int.le k 0 then "" else String.app "─" (rule (Int.sub k 1)).

Ltac2 rec list_of (c : constr) : constr list :=
  lazy_match! c with
  | nil => []
  | cons ?x ?xs => x :: list_of xs
  end.

Ltac2 print_lines (ls : string list) : unit :=
  List.iter (fun l => Message.print (Message.of_string l)) ls.

(** ** The predicate printer

    The walk produces logical lines: headings, equations (aligned on [=]
    within a block of consecutive ones) and other lines, each with an
    optional comment. [layout] then lays out each section: it breaks lines
    longer than [max_width] and aligns the comments of the section on one
    column. *)

Ltac2 Type pline := [
  PHead (string)
| PEq (string, string, string, string option)  (* prefix, left, right, comment *)
| PText (string, string, string option)        (* prefix, code, comment *)
].

Ltac2 max_width (_ : unit) : int := 112.
Ltac2 comment_cap (_ : unit) : int := 88.

Ltac2 heading (t : constr) : string :=
  let s := str t in
  String.concat "" ["── "; s; " "; rule (Int.sub 72 (width s))].

Ltac2 elem (e : constr) : string * string option :=
  lazy_match! e with
  | note ?c ?w => (pp w, Some (str c))
  | _ => (pp e, None)
  end.

Ltac2 range_elem (e : constr) : string * string option :=
  lazy_match! e with
  | note ?c (?b, ?x) => (String.concat "" ["["; pp b; ", "; pp x; ")"], Some (str c))
  | (?b, ?x) => (String.concat "" ["["; pp b; ", "; pp x; ")"], None)
  | _ => elem e
  end.

Ltac2 int_str (i : int) : string := Message.to_string (Message.of_int i).

(** Indices padded with zeros to the width of the largest one. *)
Ltac2 idx (w : int) (i : int) : string :=
  let s := int_str i in
  String.app (String.make (Int.sub w (String.length s)) (Char.of_int 48)) s.

Ltac2 indexed (ind : string) (f : constr -> string * string option) (es : constr list) : pline list :=
  let n := List.length es in
  let w := if Int.le n 1 then 1 else String.length (int_str (Int.sub n 1)) in
  List.mapi (fun i e =>
               let (code, c) := f e in
               PText (String.concat "" [ind; "    ["; idx w i; "]  "]) code c) es.

Ltac2 rec unions (m : constr) : constr list :=
  lazy_match! m with
  | @union _ _ ?a ?b => List.append (unions a) (unions b)
  | _ => [m]
  end.

Ltac2 set_comment (c : string) (ls : pline list) : pline list :=
  match ls with
  | [] => []
  | l :: rest =>
      match l with
      | PEq i a b _ => PEq i a b (Some c) :: rest
      | PText i x _ => PText i x (Some c) :: rest
      | PHead _ => l :: rest
      end
  end.

Ltac2 rec walk (ind : string) (p : constr) : pline list :=
  lazy_match! p with
  | section ?t ?q => PHead (heading t) :: walk "  " q
  | ?a ∧ ?b => List.append (walk ind a) (walk ind b)
  | note ?c ?q => set_comment (str c) (walk ind q)
  | ranges_disjoint ?l => PText ind "ranges_disjoint" None :: indexed ind range_elem (list_of l)
  | ?l = ?r =>
      lazy_match! r with
      | cons _ _ => PText ind (String.app (pp l) " =") None :: indexed ind elem (list_of r)
      | @union _ _ _ _ =>
          PText ind (String.app (pp l) " =") None ::
          List.mapi (fun i e =>
                       let (code, c) := elem e in
                       PText (String.app ind (if Int.equal i 0 then "      " else "    ∪ ")) code c)
            (unions r)
      | _ => [PEq ind (pp l) (pp r) None]
      end
  | _ => [PText ind (pp p) None]
  end.

(** *** Layout *)

Ltac2 sub_is (s : string) (i : int) (t : string) : bool :=
  let m := String.length t in
  if Int.gt (Int.add i m) (String.length s) then false
  else String.equal (String.sub s i m) t.

Ltac2 is_open (c : int) : bool :=
  Bool.or (Int.equal c 40) (Bool.or (Int.equal c 91) (Int.equal c 123)).
Ltac2 is_close (c : int) : bool :=
  Bool.or (Int.equal c 41) (Bool.or (Int.equal c 93) (Int.equal c 125)).

(** The last space at the outer level before a parenthesis or a bracket,
    not after [=]: where the last argument of an application starts. *)
Ltac2 last_arg (s : string) : int :=
  let n := String.length s in
  let rec go i depth last :=
    if Int.equal i n then last
    else
      let c := Char.to_int (String.get s i) in
      if is_open c then go (Int.add i 1) (Int.add depth 1) last
      else if is_close c then go (Int.add i 1) (Int.sub depth 1) last
      else if Int.equal c 32 then
        if Int.equal depth 0 then
          if Bool.and
               (Bool.or (sub_is s (Int.add i 1) "(") (sub_is s (Int.add i 1) "["))
               (Bool.neg (Bool.and (Int.ge i 1) (sub_is s (Int.sub i 1) "=")))
          then go (Int.add i 1) depth i
          else go (Int.add i 1) depth last
        else go (Int.add i 1) depth last
      else go (Int.add i 1) depth last in
  go 0 0 (Int.neg 1).

(** Breaks [prefix ^ s] when it is longer than [limit]: before the
    last argument, after [", "] and around [::], [++] (at the outer two
    levels) and [∧] (at the outer level). A continuation line is indented
    under its innermost open bracket, or by two after the prefix. *)
Ltac2 wrap (limit : int) (prefix : string) (s : string) : string list :=
  if Int.le (Int.add (width prefix) (width s)) limit then [String.app prefix s] else
  let n := String.length s in
  let base := width prefix in
  let la := last_arg s in
  let rec go i start stack col ind acc :=
    if Int.equal i n then List.rev ((ind, String.sub s start (Int.sub n start)) :: acc)
    else
      let depth := List.length stack in
      let cut :=
        if Int.equal i la then Some (i, Int.add i 1)
        else if Int.le depth 1 then
          if sub_is s i ", " then Some (Int.add i 1, Int.add i 2)
          else if sub_is s i " :: " then Some (Int.add i 3, Int.add i 4)
          else if sub_is s i " ++ " then Some (Int.add i 3, Int.add i 4)
          else if Int.equal depth 0 then
            (if sub_is s i " ∧ " then Some (Int.add i 4, Int.add i 5) else None)
          else None
        else None in
      match cut with
      | Some (e, next) =>
          let line := (ind, String.sub s start (Int.sub e start)) in
          let k :=
            match stack with
            | [] => Int.add base 2
            | top :: _ => let (oc, ch) := top in if Int.equal ch 123 then Int.add oc 2 else Int.add oc 1
            end in
          go next next stack k (spaces k) (line :: acc)
      | None =>
          let c := Char.to_int (String.get s i) in
          let stack :=
            if is_open c then (col, c) :: stack
            else if is_close c then (match stack with [] => [] | _ :: st => st end)
            else stack in
          let col := if Int.ge c 128 then (if Int.lt c 192 then col else Int.add col 1) else Int.add col 1 in
          go (Int.add i 1) start stack col ind acc
      end in
  List.map (fun l => let (i, t) := l in String.app i t) (go 0 0 [] base prefix []).

Ltac2 rec take_eqs (ls : pline list) : pline list * pline list :=
  match ls with
  | [] => ([], [])
  | l :: rest =>
      match l with
      | PEq _ _ _ _ => let (b, r) := take_eqs rest in (l :: b, r)
      | _ => ([], ls)
      end
  end.

(** Equations of a block of consecutive ones, aligned on [=] as far as
    the lines fit. *)
Ltac2 rec align_eqs (ls : pline list) : pline list :=
  match ls with
  | [] => []
  | l :: rest =>
      match l with
      | PEq _ _ _ _ =>
          let (blk, rest) := take_eqs ls in
          let w := List.fold_left (fun m l =>
                     match l with
                     | PEq i a _ _ => let k := Int.add (width i) (width a) in if Int.lt m k then k else m
                     | _ => m
                     end) 0 blk in
          List.append
            (List.map (fun l =>
                         match l with
                         | PEq i a b c =>
                             (* pad as far as the line fits *)
                             let room := Int.sub (Int.sub (max_width ()) 3) (width b) in
                             let w' := if Int.lt room w then room else w in
                             PText i (String.concat "" [pad a (Int.sub w' (width i)); " = "; b]) c
                         | _ => l
                         end) blk)
            (align_eqs rest)
      | _ => l :: align_eqs rest
      end
  end.

(** A section: equations aligned, long lines broken (earlier when they
    carry a comment), comments on one column; a comment whose line is
    still longer than the column goes on the next line, at the column. *)
Ltac2 layout_section (ls : pline list) : string list :=
  (* a line with a comment is broken earlier, to leave room for it *)
  let limit c := match c with None => max_width () | Some _ => comment_cap () end in
  let items := List.map (fun l =>
                 match l with
                 | PText i x c => (wrap (limit c) i x, c)
                 | PEq i a b c => (wrap (limit c) i (String.concat "" [a; " = "; b]), c)
                 | PHead h => ([h], None)
                 end) (align_eqs ls) in
  let col := List.fold_left (fun m it =>
               let (lines, c) := it in
               match c with
               | None => m
               | Some _ =>
                   match lines with
                   | [] => m
                   | l :: _ =>
                       let k := width l in
                       if Int.le k (comment_cap ()) then (if Int.lt m k then k else m) else m
                   end
               end) 0 items in
  let col := Int.add col 2 in
  List.flat_map (fun it =>
    let (lines, c) := it in
    match c with
    | None => lines
    | Some c =>
        match lines with
        | [] => []
        | l :: rest =>
            if Int.le (Int.add (width l) 2) col then String.concat "" [pad l col; "-- "; c] :: rest
            else List.append lines [String.concat "" [spaces col; "-- "; c]]
        end
    end) items.

Ltac2 rec split_sections (ls : pline list) (cur : pline list) (acc : pline list list) : pline list list :=
  match ls with
  | [] => List.rev (List.rev cur :: acc)
  | l :: rest =>
      match l with
      | PHead _ => split_sections rest [l] (List.rev cur :: acc)
      | _ => split_sections rest (l :: cur) acc
      end
  end.

Ltac2 layout (ls : pline list) : string list :=
  List.flat_map layout_section (split_sections ls [] []).

(** Types, with the names of the address and otype abbreviations. *)
Ltac2 pp_type (t : constr) : string :=
  if Constr.equal t constr:(OType) then "OType"
  else if Constr.equal t constr:(Addr) then "Addr"
  else pp t.

(** The existential binders of the predicate, outside the words, with the
    section they appear in. *)
Ltac2 rec exists_of (sec : string) (p : constr) : pline list :=
  lazy_match! p with
  | section ?t ?q => exists_of (str t) q
  | ?a ∧ ?b => List.append (exists_of sec a) (exists_of sec b)
  | note _ ?q => exists_of sec q
  | @ex ?a ?f =>
      let x :=
        match Constr.Unsafe.kind f with
        | Constr.Unsafe.Lambda b _ =>
            match Constr.Binder.name b with
            | Some x => Ident.to_string x
            | None => "_"
            end
        | _ => "_"
        end in
      [PText "  " (String.concat "" ["∃ "; x; " : "; pp_type a]) (Some (String.app "in " sec))]
  | _ => []
  end.

Ltac2 rec group_binders (hs : (ident * constr option * constr) list) : (string list * constr) list :=
  match hs with
  | [] => []
  | h :: rest =>
      let (x, _, t) := h in
      match group_binders rest with
      | [] => [([Ident.to_string x], t)]
      | g :: gs =>
          let (xs, t') := g in
          if Constr.equal t t' then (Ident.to_string x :: xs, t') :: gs
          else ([Ident.to_string x], t) :: g :: gs
      end
  end.

(** Binder groups [(x y : T)], as many per line as fit: the first line
    starts with [first], the next ones with [cont], the last one ends with
    [last]. *)
Ltac2 fill_binders (first : string) (cont : string) (last : string)
    (hs : (ident * constr) list) : string list :=
  let args := List.map (fun g => let (xs, t) := g in
                          String.concat "" ["("; String.concat " " xs; " : "; pp_type t; ")"])
                (group_binders (List.map (fun h => let (x, t) := h in (x, None, t)) hs)) in
  let rec fill line fresh args acc :=
    match args with
    | [] => List.rev (String.app line last :: acc)
    | a :: rest =>
        if fresh then fill (String.app line a) false rest acc
        else if Int.le (Int.add (Int.add (width line) (width a)) 4) (max_width ())
        then fill (String.concat "" [line; " "; a]) false rest acc
        else fill (String.app cont a) false rest (line :: acc)
    end in
  fill first true args [].

(** The header: the predicate [name] applied to its binders [hs] (the
    machine parameters excepted), its leading existential binders [es], and
    the existential binders of its body [p]. *)
Ltac2 header (name : string) (hs : (ident * constr) list) (es : (ident * constr) list)
    (p : constr) : pline list :=
  let hs := List.filter (fun h => let (_, t) := h in
                          Bool.neg (Constr.equal t constr:(MachineParameters))) hs in
  let lines :=
    List.append
      (fill_binders (String.app name " ") "    " " :=" hs)
      (match es with
       | [] => []
       | _ => fill_binders "  ∃ " "      " "," es
       end) in
  List.append (List.map (fun l => PText "" l None) lines) (exists_of "" p).

(** Runs [k] on the binders of the λ-abstractions heading [body], on the
    binders of the existentials heading their body, and on the body of
    these, each binder brought into the context under its name. *)
Ltac2 rec under_binders (hs : (ident * constr) list) (es : (ident * constr) list)
    (body : constr)
    (k : (ident * constr) list -> (ident * constr) list -> constr -> unit) : unit :=
  let enter b bd (next : ident * constr -> constr -> unit) :=
    let x := match Constr.Binder.name b with Some x => x | None => @x end in
    let t := Constr.Binder.type b in
    let _ := Constr.in_context x t (fun () =>
               next (x, t) (Constr.Unsafe.substnl [Constr.Unsafe.make (Constr.Unsafe.Var x)] 0 bd)) in
    () in
  match Constr.Unsafe.kind body with
  | Constr.Unsafe.Lambda b bd =>
      match es with
      | [] => enter b bd (fun h bd => under_binders (h :: hs) [] bd k)
      | _ => k (List.rev hs) (List.rev es) body
      end
  | _ =>
      lazy_match! body with
      | @ex _ ?f =>
          match Constr.Unsafe.kind f with
          | Constr.Unsafe.Lambda b bd => enter b bd (fun e bd => under_binders hs (e :: es) bd k)
          | _ => k (List.rev hs) (List.rev es) body
          end
      | _ => k (List.rev hs) (List.rev es) body
      end
  end.

(** Runs [tac] on a fresh goal: [Constr.in_context] needs one, and a
    top-level command has none. *)
Ltac2 with_goal (tac : unit -> unit) : unit :=
  let no_evar () := Control.throw (Invalid_argument None) in
  match Constr.Unsafe.kind open_constr:(_ : True) with
  | Constr.Unsafe.Cast e _ _ =>
      match Constr.Unsafe.kind e with
      | Constr.Unsafe.Evar ev _ => Control.new_goal ev; Control.focus 1 1 tac
      | _ => no_evar ()
      end
  | _ => no_evar ()
  end.

Ltac2 strip_annot (s : string) : string :=
  let n := String.length s in
  if Int.ge n 6 then
    if String.equal (String.sub s (Int.sub n 6) 6) "_annot" then String.sub s 0 (Int.sub n 6) else s
  else s.

(** The lines of the annotated predicate [c], a constant: its body, headed
    by its name without the suffix [_annot] applied to its binders. *)
Ltac2 initial_state_lines (c : constr) : string list :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant cst _ =>
      let name := strip_annot (Ident.to_string (List.last (Env.path (Std.ConstRef cst)))) in
      let body := Std.eval_cbv
        { Std.rBeta := true; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
          Std.rZeta := false; Std.rDelta := false; Std.rConst := [Std.ConstRef cst];
          Std.rStrength := Std.Norm } c in
      let r := { contents := [] } in
      with_goal (fun () => under_binders [] [] body (fun hs es p =>
        r.(contents) := List.append (layout (header name hs es p)) (layout (walk "  " p))));
      r.(contents)
  | _ => Control.throw (Invalid_argument (Some (Message.of_string "print_initial_state: not a constant")))
  end.

(** Prints the annotated predicate [c], given as [constr:(@name_annot)]. *)
Ltac2 print_initial_state (c : constr) : unit :=
  print_lines (initial_state_lines c).

Ltac2 rec take_lines (n : int) (l : string list) : string list :=
  if Int.le n 0 then [] else
  match l with [] => [] | x :: xs => x :: take_lines (Int.sub n 1) xs end.

Ltac2 rec drop_lines (n : int) (l : string list) : string list :=
  if Int.le n 0 then l else
  match l with [] => [] | _ :: xs => drop_lines (Int.sub n 1) xs end.

(** Prints [n] lines from line [from] only. *)
Ltac2 print_initial_state_part (c : constr) (from : int) (n : int) : unit :=
  print_lines (take_lines n (drop_lines from (initial_state_lines c))).

(** ** The memory-map printer *)

(** Decoding goes through [Countable RegName], whose decoder leaves opaque
    proofs of [n <=? RegNum = true] in the register. [canon_reg] rebuilds the
    register with an [eq_refl] proof, so that the printing notations match
    after [vm_compute]. *)
Definition canon_reg (r : RegName) : RegName :=
  match r with
  | registers.R n _ =>
      match (n <=? RegNum)%nat as b return ((n <=? RegNum)%nat = b → RegName) with
      | true => λ H, registers.R n H
      | false => λ _, r
      end eq_refl
  end.

Definition canon_arg (a : Z + RegName) : Z + RegName :=
  match a with inl z => inl z | inr r => inr (canon_reg r) end.

Definition canon_instr (i : instr) : instr :=
  let c := canon_reg in
  let ca := canon_arg in
  match i with
  | Jmp a => Jmp (ca a)
  | Jnz a r => Jnz (ca a) (c r)
  | Jalr r1 r2 => Jalr (c r1) (c r2)
  | Mov r a => Mov (c r) (ca a)
  | CLoad r1 r2 z => CLoad (c r1) (c r2) z
  | Store r a z => Store (c r) (ca a) z
  | Lt r a1 a2 => Lt (c r) (ca a1) (ca a2)
  | Add r a1 a2 => Add (c r) (ca a1) (ca a2)
  | Sub r a1 a2 => Sub (c r) (ca a1) (ca a2)
  | Mul r a1 a2 => Mul (c r) (ca a1) (ca a2)
  | LAnd r a1 a2 => LAnd (c r) (ca a1) (ca a2)
  | LOr r a1 a2 => LOr (c r) (ca a1) (ca a2)
  | LShiftL r a1 a2 => LShiftL (c r) (ca a1) (ca a2)
  | LShiftR r a1 a2 => LShiftR (c r) (ca a1) (ca a2)
  | Lea r a => Lea (c r) (ca a)
  | Restrict r a => Restrict (c r) (ca a)
  | Subseg r a1 a2 => Subseg (c r) (ca a1) (ca a2)
  | GetB r1 r2 => GetB (c r1) (c r2)
  | GetE r1 r2 => GetE (c r1) (c r2)
  | GetA r1 r2 => GetA (c r1) (c r2)
  | GetP r1 r2 => GetP (c r1) (c r2)
  | GetL r1 r2 => GetL (c r1) (c r2)
  | GetWType r1 r2 => GetWType (c r1) (c r2)
  | GetOType r1 r2 => GetOType (c r1) (c r2)
  | Seal r1 r2 r3 => Seal (c r1) (c r2) (c r3)
  | UnSeal r1 r2 r3 => UnSeal (c r1) (c r2) (c r3)
  | SpecialRW r sr a => SpecialRW (c r) sr (ca a)
  | GetTag r1 r2 => GetTag (c r1) (c r2)
  | ClearTag r1 r2 => ClearTag (c r1) (c r2)
  | Auipcc r z => Auipcc (c r) z
  | SetMIE _ | Mret | Fail | Halt => i
  end.

Inductive cell : Type :=
| CWord (w : Word)
| CInstr (i : instr)
| CRun (n : Z) (w : Word)
| CText (s : string).

Record map_row : Type := MkRow {
  row_b : Z;
  row_e : Z;
  row_range : string;
  row_region : string;
  row_owner : string;
  row_cells : list cell;
}.

Definition emit_run (w : Word) (n : nat) : cell :=
  if (n =? 1)%nat then CWord w else CRun (Z.of_nat n) w.

(** Run-length compression; word equality computes since [word_eq_dec] is
    transparent. *)
Fixpoint rle_aux (cur : Word) (n : nat) (ws : list Word) : list cell :=
  match ws with
  | [] => [emit_run cur n]
  | w :: ws' =>
      if bool_decide (w = cur) then rle_aux cur (S n) ws'
      else emit_run cur n :: rle_aux w 1 ws'
  end.

Definition rle (ws : list Word) : list cell :=
  match ws with [] => [] | w :: ws' => rle_aux w 1 ws' end.

(** *** Capabilities as cheriot-rtos's debug output prints them

    [<address> (v:<tag> <base>-<top> l:<length> o:<otype> p: G RWcgml Xa SU0)],
    in hexadecimal. Griotte has no load/store-capability permission: [c]
    is shown whenever the capability can read or write. Loads keep the
    global bit unless [DL] ([g]) and the write permission unless [DRO]
    ([m]); [l] is [WL], [X] is [X] or [XSR], [a] is [XSR]. A sentry has the
    otype of its kind (1 to 5, as cheriot-sail's sentry otypes), a sealing
    range shows its seal permissions ([S], [U]) and no memory permission;
    [0] (the user permission) never appears. *)

Definition hex_digit (d : Z) : string := String.substring (Z.to_nat d) 1 "0123456789abcdef".

Fixpoint hex_aux (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S f =>
      let acc' := String.append (hex_digit (z mod 16)%Z) acc in
      if (z <? 16)%Z then acc' else hex_aux f (z / 16)%Z acc'
  end.

Definition hex (z : Z) : string := String.append "0x" (hex_aux 16 z "").

Fixpoint dec_aux (fuel : nat) (z : Z) (acc : string) : string :=
  match fuel with
  | 0 => acc
  | S f =>
      let acc' := String.append (hex_digit (z mod 10)%Z) acc in
      if (z <? 10)%Z then acc' else dec_aux f (z / 10)%Z acc'
  end.

Definition dec (z : Z) : string :=
  if (z <? 0)%Z then String.append "-" (dec_aux 20 (- z)%Z "") else dec_aux 20 z "".

Definition strs (l : list string) : string := foldr String.append "" l.

Definition flag (b : bool) (c : string) : string := if b then c else "-".

Definition seal_letters (sp : SealPerms) : string :=
  strs [flag sp.1 "S"; flag sp.2 "U"; "-"].

Definition global_letter (g : Locality) : string :=
  flag (match g with Global => true | Local => false end) "G".

Definition perm_letters (p : Perm) (g : Locality) : string :=
  match p with
  | BPerm rx w dl dro =>
      let rd := match rx with Orx => false | _ => true end in
      let wr := match w with Ow => false | _ => true end in
      strs [global_letter g; " ";
            flag rd "R"; flag wr "W"; flag (rd || wr) "c";
            flag (match dl with LG => true | DL => false end) "g";
            flag (match dro with LM => true | DRO => false end) "m";
            flag (match w with WL => true | _ => false end) "l"; " ";
            flag (match rx with X | XSR => true | _ => false end) "X";
            flag (match rx with XSR => true | _ => false end) "a"; " ";
            seal_letters (false, false)]
  end.

Definition range_perm_letters (g : Locality) (sp : SealPerms) : string :=
  strs [global_letter g; " ------ -- "; seal_letters sp].

Definition sentry_otype (k : SentryKind) : Z :=
  match k with
  | Inherit => 1 | FwdDisable => 2 | FwdEnable => 3 | RetDisable => 4 | RetEnable => 5
  end.

Definition cheriot_cap (t : bool) (b e a o : Z) (ps : string) : string :=
  strs [hex a; " (v:"; if t then "1" else "0"; " "; hex b; "-"; hex e;
        " l:"; hex (e - b)%Z; " o:"; hex o; " p: "; ps; ")"].

Definition sealable_text (o : Z) (sb : Sealable) : string :=
  match sb with
  | SCap t p g b e a => cheriot_cap t b e a o (perm_letters p g)
  | SSealRange t sp g b e a => cheriot_cap t b e a o (range_perm_letters g sp)
  end.

(** The text of a capability; [None] for an integer. *)
Definition word_text (w : Word) : option string :=
  match w with
  | WInt _ => None
  | WSealable sb => Some (sealable_text 0 sb)
  | WSentry k t p g b e a => Some (cheriot_cap t b e a (sentry_otype k) (perm_letters p g))
  | WSealed o sb => Some (sealable_text o sb)
  end.

(** An export entry, decoded as in the predicate: posture, number of
    arguments, offset. *)
Definition entry_text (z : Z) : string :=
  strs ["entry ";
        if (Z.land z 16 =? 16)%Z then "InterruptDisabled" else "InterruptEnabled"; " ";
        dec (Z.land z 7); " "; dec (Z.shiftr z 5)].

Definition entry_cell (w : Word) : cell :=
  match w with WInt z => CText (entry_text z) | _ => CWord w end.

Definition word_cell (w : Word) : cell :=
  match word_text w with Some s => CText s | None => CWord w end.

Definition text_cell (c : cell) : cell :=
  match c with CWord w => word_cell w | _ => c end.

Section memory_map.
  Context `{MP : MachineParameters}.

  Definition words_cells (ws : list Word) : list cell := map word_cell ws.
  Definition code_cells : list Word → list cell :=
    map (λ w, CInstr (canon_instr (decodeInstrW w))).

  Definition row (b : Addr) (n : nat) (region owner : string) (cells : list cell) : map_row :=
    MkRow b (b + Z.of_nat n)%Z (strs ["["; hex b; ", "; hex (b + Z.of_nat n)%Z; ")"])
      region owner cells.

  Definition cmpt_rows (nc : string * img_cmpt) : list map_row :=
    let '(n, c) := nc in
    [row (cmpt_b_pcc c) (length (cmpt_imports c)) "imports" n (words_cells (cmpt_imports c));
     row (cmpt_a_code c) (length (cmpt_code c)) "code" n (code_cells (cmpt_code c));
     row (cmpt_b_cgp c) (length (cmpt_data c)) "globals" n (map text_cell (rle (cmpt_data c)));
     row (cmpt_b_static_sealed c) (length (cmpt_static_sealed c)) "static sealed" n
       (words_cells (cmpt_static_sealed c));
     row (cmpt_exp_tbl_pcc c) (2 + length (cmpt_exp_tbl_entries c)) "export table" n
       (app
          (words_cells
             [WCap true RX Global (cmpt_b_pcc c) (cmpt_e_pcc c) (cmpt_b_pcc c);
              WCap true RW Global (cmpt_b_cgp c) (cmpt_e_cgp c) (cmpt_b_cgp c)])
          (map entry_cell (cmpt_exp_tbl_entries c)))].

  Definition thread_rows (i : nat) (t : img_thread) : list map_row :=
    [row (b_trusted_stack t) (Z.to_nat (e_trusted_stack t - b_trusted_stack t)%Z)
       "trusted stack" (String.append "thread " (nat_str i)) [];
     row (b_stack t) (Z.to_nat (e_stack t - b_stack t)%Z) "stack" (String.append "thread " (nat_str i)) []].

  Fixpoint insert_row (r : map_row) (rs : list map_row) : list map_row :=
    match rs with
    | [] => [r]
    | r' :: rs' => if (row_b r <=? row_b r')%Z then r :: rs else r' :: insert_row r rs'
    end.

  Definition sort_rows (rs : list map_row) : list map_row := foldr insert_row [] rs.

  (** The rows of an image, sorted by address. *)
  Definition img_rows (img : fw_image) : list map_row :=
    let sw := img_sw img in
    let asrt := img_asrt img in
    sort_rows
      (app
        [row (b_switcher sw) (Z.to_nat (e_switcher sw - b_switcher sw)%Z) "code" "switcher"
           [CText "sealing key, switcher_instrs"];
         row (b_assert asrt) (Z.to_nat (e_assert asrt - b_assert asrt)%Z) "code" "assert"
           [CText "assert_subroutine_instrs, flag capability"];
         row (flag_assert asrt) 1 "flag" "assert" []]
        (app (concat (map cmpt_rows (img_cmpts img)))
           (concat (imap thread_rows (img_threads img))))).
End memory_map.

Ltac2 cell_str (c : constr) : string :=
  lazy_match! c with
  | CWord ?w => pp w
  | CInstr ?i => pp i
  | CRun ?n ?w => String.concat "" [pp n; " × "; pp w]
  | CText ?s => str s
  end.

Ltac2 row_strs (r : constr) : string * string * string * string list :=
  lazy_match! r with
  | MkRow _ _ ?rng ?reg ?own ?cells =>
      (str rng,
       str reg, str own,
       List.map cell_str (list_of cells))
  end.

Ltac2 max_len (ss : string list) : int :=
  List.fold_left (fun m s => if Int.lt m (String.length s) then String.length s else m) 0 ss.

(** The lines of the memory map of [img], computed by [vm_compute]. *)
Ltac2 memory_map_lines (img : constr) : string list :=
  let rows := List.map row_strs (list_of (Std.eval_vm None constr:(img_rows $img))) in
  let hdr := ("[b, e)", "region", "owner", ["contents"]) in
  let all := hdr :: rows in
  let w1 := max_len (List.map (fun (a, _, _, _) => a) all) in
  let w2 := max_len (List.map (fun (_, b, _, _) => b) all) in
  let w3 := max_len (List.map (fun (_, _, c, _) => c) all) in
  let indent := String.make (Int.add (Int.add w1 w2) (Int.add w3 6)) (Char.of_int 32) in
  let lines_of (r : string * string * string * string list) :=
    let (a, b, c, cells) := r in
    let lead := String.concat "  " [pad a w1; pad b w2; pad c w3; ""] in
    match cells with
    | [] => [lead]
    | x :: xs => String.app lead x :: List.map (String.app indent) xs
    end in
  List.flat_map lines_of all.

(** Prints the memory map of [img]. *)
Ltac2 print_memory_map (img : constr) : unit := print_lines (memory_map_lines img).

(** Prints [n] lines of the memory map of [img] from line [from]. *)
Ltac2 print_memory_map_part (img : constr) (from : int) (n : int) : unit :=
  print_lines (take_lines n (drop_lines from (memory_map_lines img))).
