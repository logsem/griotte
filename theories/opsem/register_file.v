(* From Stdlib Require Import ssreflect Eqdep_dec. *)
(* From stdpp Require Import gmap fin_maps list countable. *)
(* From griotte Require Export registers. *)
From griotte Require Import registers addresses machine_word.

(* Convenient coercion when writing instructions *)
Definition regn : RegName → (Z+RegName)%type := inr.
Definition cst : Z → (Z+RegName)%type := inl.
Coercion regn : RegName >-> sum.
Coercion cst : Z >-> sum.

Definition Reg := gmap RegName Word.
Definition SReg := gmap SRegName Word.


Definition writeAllowed_a_in_regs (r : Reg) (a : Addr) :=
  ∃ reg (w : Word), r !! reg = Some w ∧ writeAllowedWord w ∧ hasValidAddress w a.

Definition readAllowed_a_in_regs (r : Reg) (a : Addr) :=
  ∃ reg (w : Word), r !! reg = Some w ∧ readAllowedWord w ∧ hasValidAddress w a.

Global Instance writeAllowed_a_in_regs_Decidable
  (r : Reg) (a : Addr) :
  Decision (writeAllowed_a_in_regs r a).
Proof.
  eapply finite.exists_dec.
  intros x. destruct (r !! x) as [w|] eqn:Hsome
  ; first (destruct (decide (writeAllowedWord w)), (decide (hasValidAddress w a)))
  ; try ( (right; intros [w1 (Heq & ? & ?)]; inversion Heq; congruence ) ).
  left; eexists _; auto.
Qed.

Global Instance readAllowed_a_in_regs_Decidable
  (r : Reg) (a : Addr) :
  Decision (readAllowed_a_in_regs r a).
Proof.
  eapply finite.exists_dec.
  intros x. destruct (r !! x) as [w|] eqn:Hsome
  ; first (destruct (decide (readAllowedWord w)), (decide (hasValidAddress w a)))
  ; try ( (right; intros [w1 (Heq & ? & ?)]; inversion Heq; congruence ) ).
  left; eexists _; auto.
Qed.

Lemma regmap_full_dom (r: Reg):
  (∀ x, is_Some (r !! x)) →
  dom r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm subseteq); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite elem_of_dom. apply Hfull.
Qed.


(** Register file: CNULL always contains 0 *)

Definition lookup_reg (r : RegName) (regs : Reg) : option Word :=
  w ← (regs !! r);
  Some (if (decide (r = cnull)) then (WInt 0) else w).
Definition insert_reg (r : RegName) (w : Word) (regs : Reg) : Reg :=
  let w' := if (decide (r = cnull)) then (WInt 0) else w in
  <[r:=w']>regs.

Notation "m !!ᵣ i" := (lookup_reg i m) (at level 20) : stdpp_scope.
Notation "(!!ᵣ)" := lookup_reg (only parsing) : stdpp_scope.
Notation "( m !!ᵣ.)" := (λ i, m !!ᵣ i) (only parsing) : stdpp_scope.
Notation "(.!!ᵣ i )" := (lookup_reg i) (only parsing) : stdpp_scope.
Notation "<[ k := a ]ᵣ>" := (insert_reg k a)
  (at level 5, right associativity, format "<[ k := a ]ᵣ>") : stdpp_scope.

Lemma is_Some_lookup_reg (regs : Reg) ( r : RegName ) :
  (is_Some (regs !!ᵣ r)) <-> (is_Some (regs !! r)).
Proof.
  rewrite /lookup_reg.
  destruct (regs !! r); cbn; done.
Qed.
Lemma lookup_reg_not_cnull (regs : Reg) (r : RegName) :
  r ≠ cnull -> regs !!ᵣ r = regs !! r.
Proof.
  intros Hr.
  rewrite /lookup_reg.
  destruct (regs !! r) ; cbn ; last done.
  destruct (decide (r = cnull)) eqn:Hdec; cbn in *; try done.
Qed.

Lemma elem_of_dom_reg (regs : Reg) (r : RegName) :
  r ∈ dom regs ↔ is_Some (regs !!ᵣ r).
Proof.
  split; rewrite /lookup_reg; intros Hr.
  + rewrite elem_of_dom in Hr; destruct Hr as [w Hr].
    rewrite Hr; cbn; done.
  + rewrite elem_of_dom.
    destruct (regs !! r) eqn:Hr'; rewrite Hr'; cbn in *; first done.
    by apply is_Some_None in Hr.
Qed.

Lemma lookup_reg_weaken (regs1 regs2 : Reg) (r : RegName) (w : Word) :
  regs1 !!ᵣ r = Some w → regs1 ⊆ regs2 → regs2 !!ᵣ r = Some w.
Proof.
  intros Hr1 Hincl.
  rewrite /lookup_reg in Hr1.
  rewrite /lookup_reg.
  destruct (regs1 !! r) eqn:Hr; cbn in *; last done.
  eapply lookup_weaken in Hr; eauto.
  rewrite Hr; cbn.
  done.
Qed.

Lemma insert_reg_insert r w1 w2 regs :
  <[ r := w1 ]ᵣ> (<[ r := w2 ]> regs) = <[ r := w1 ]ᵣ> regs.
Proof.
  destruct (decide (r = cnull)) eqn:Hdec; simplify_eq; rewrite /insert_reg
  ; rewrite Hdec; by rewrite insert_insert_eq.
Qed.

Lemma insert_insert_reg r w1 w2 regs :
  <[ r := w1 ]> (<[ r := w2 ]ᵣ> regs) = <[ r := w1 ]> regs.
Proof.
  destruct (decide (r = cnull)) eqn:Hdec; simplify_eq; rewrite /insert_reg
  ; rewrite Hdec; by rewrite insert_insert_eq.
Qed.

Lemma insert_reg_insert_commute r1 r2 w1 w2 regs :
  r1 ≠ r2 -> <[ r1 := w1 ]ᵣ> (<[ r2 := w2 ]> regs) = <[ r2 := w2
    ]> (<[ r1 := w1 ]ᵣ> regs).
Proof.
  intros Hneq. rewrite insert_insert_ne; auto.
Qed.

Lemma lookup_reg_singleton_None r1 r2 w :
  ({[r1 := w]} : Reg) !!ᵣ r2 = None ↔ r1 ≠ r2.
Proof.
  rewrite /lookup_reg.
  split; intros H.
  - intros ->; rewrite lookup_singleton_eq in H; done.
  - eapply lookup_singleton_None in H; rewrite H; auto.
    Unshelve. 1: exact Word. 1: auto.
Qed.

Lemma lookup_reg_empty r :
  (∅ : Reg) !!ᵣ r = None.
Proof.
  rewrite /lookup_reg.
  rewrite lookup_empty; done.
Qed.

Lemma lookup_insert_reg regs r w :
  <[r:=w]ᵣ> regs !! r = Some (if (decide (r = cnull)) then WInt 0 else w).
Proof.
  destruct (decide (r = cnull)) eqn:Hdec; simplify_eq; rewrite /insert_reg
  ; rewrite Hdec; by rewrite lookup_insert_eq.
Qed.
Lemma lookup_insert_reg_ne regs r1 r2 w :
  r1 ≠ r2 -> <[r1:=w]ᵣ> regs !! r2 = regs !! r2.
Proof.
  intros Hneq.
  rewrite /lookup_reg.
  rewrite lookup_insert_ne; auto.
Qed.

Lemma lookup_reg_insert regs r w :
  (<[r:=w]> regs) !!ᵣ r = Some (if (decide (r = cnull)) then WInt 0 else w).
Proof.
  destruct (decide (r = cnull)) eqn:Hdec; simplify_eq; rewrite /lookup_reg
  ; rewrite Hdec; by rewrite lookup_insert_eq.
Qed.

Lemma lookup_reg_insert_ne regs r1 r2 w :
  r1 ≠ r2 -> (<[r1:=w]> regs) !!ᵣ r2 = regs !!ᵣ r2.
Proof.
  intros Hneq.
  rewrite /lookup_reg.
  rewrite lookup_insert_ne; auto.
Qed.

Lemma lookup_reg_insert_reg regs r w :
  <[r:=w]ᵣ> regs !!ᵣ r = Some (if (decide (r = cnull)) then WInt 0 else w).
Proof.
  destruct (decide (r = cnull)) eqn:Hdec; simplify_eq; rewrite /lookup_reg /insert_reg
  ; rewrite Hdec; by rewrite lookup_insert_eq.
Qed.

Lemma lookup_reg_insert_reg_ne regs r1 r2 w :
  r1 ≠ r2 -> <[r1:=w]ᵣ> regs !!ᵣ r2 = regs !!ᵣ r2.
Proof.
  intros Hneq.
  rewrite /lookup_reg.
  rewrite lookup_insert_ne; auto.
Qed.

Lemma lookup_reg_delete regs r :
  delete r regs !!ᵣ r = None.
Proof.
  rewrite /lookup_reg.
  by rewrite lookup_delete_eq.
Qed.
Lemma lookup_reg_delete_ne regs r1 r2 :
  r1 ≠ r2 -> delete r1 regs !!ᵣ r2 = regs !!ᵣ r2.
Proof.
  intros Hneq.
  rewrite /lookup_reg.
  rewrite lookup_delete_ne; auto.
Qed.
Lemma lookup_reg_singleton r w :
  ({[r := w]} : Reg) !!ᵣ r = Some (if (decide (r = cnull)) then WInt 0 else w).
Proof.
  rewrite /lookup_reg.
  rewrite lookup_singleton_eq; auto; cbn.
Qed.
Lemma lookup_reg_singleton_ne r1 r2 w :
  r1 ≠ r2 -> ({[r1 := w]} : Reg) !!ᵣ r2 = None.
Proof.
  intros Hneq.
  rewrite /lookup_reg.
  rewrite lookup_singleton_ne; auto.
Qed.

Lemma lookup_reg_singleton_Some r1 r2 w1 w2 :
  ({[r1 := w1]} : Reg) !!ᵣ r2 = Some w2 ↔ r1 = r2 ∧ (if (decide (r2 = cnull)) then WInt 0 else w1)
  = w2.
Proof.
  split; rewrite /lookup_reg; intros H.
  - destruct ({[r1 := w1]} !! r2) eqn:Hr2; cbn in *; last done.
    apply lookup_singleton_Some in Hr2 as [-> ->].
    split; simplify_eq; done.
  - destruct H as [-> <-].
    by rewrite lookup_singleton_eq; cbn.
Qed.

Lemma lookup_reg_weaken_inv (regs1 regs2 : Reg) (r : RegName) (w1 w2 : Word) :
  regs1 !!ᵣ r = Some w1 → regs1 ⊆ regs2 → regs2 !!ᵣ r = Some w2 -> w1 = w2.
Proof.
  intros Hr1 Hincl Hr2.
  rewrite /lookup_reg in Hr1.
  rewrite /lookup_reg in Hr2.
  destruct (regs1 !! r) eqn:Hr; cbn in *; last done.
  simplify_eq.
  eapply lookup_weaken in Hr; eauto.
  rewrite Hr in Hr2; cbn in *.
  simplify_eq.
  done.
Qed.

Lemma insert_reg_not_cnull (regs : Reg) (r : RegName) (w : Word) :
  r ≠ cnull -> <[r := w]ᵣ> regs = <[r := w]> regs.
Proof.
  intros Hr.
  rewrite /insert_reg.
  destruct (decide (r = cnull)); done.
Qed.

Lemma insert_reg_cnull (regs : Reg) (w : Word) :
  <[cnull := w]ᵣ> regs = <[cnull := WInt 0]> regs.
Proof.
  rewrite /insert_reg.
  destruct (decide (cnull = cnull)); done.
Qed.
Lemma lookup_reg_cnull (regs : Reg) :
  regs !!ᵣ cnull = (fun _ => WInt 0) <$> (regs !! cnull).
Proof.
  rewrite /lookup_reg.
  destruct (regs !! cnull) eqn:Hcnull; auto.
Qed.


Tactic Notation "simpl_map_regs" "by" tactic3(tac) :=
  repeat (match goal with
          | H : context [ _ !!ᵣ ?r ] |- _ =>
              rewrite lookup_reg_not_cnull in H; [|by tac]
          | H : context [ _ !!ᵣ cnull ] |- _ =>
              rewrite lookup_reg_cnull in H
          | H : context [ <[ _ := _]ᵣ> _ ] |- _ =>
              rewrite insert_reg_not_cnull in H; [|by tac]
          | H : context [ <[ cnull := _]ᵣ> _ ] |- _ =>
              rewrite insert_reg_cnull in H
          | |- context [ _ !!ᵣ ?r ] =>
              rewrite lookup_reg_not_cnull; [|by tac]
          | |- context [ _ !!ᵣ cnull ] =>
              rewrite lookup_reg_cnull
          | |- context [ <[ _ := _]ᵣ> _ ] =>
              rewrite insert_reg_not_cnull; [|by tac]
          | |- context [ <[ cnull := _]ᵣ> _ ] =>
              rewrite insert_reg_cnull
          end).

Tactic Notation "simpl_map" "by" tactic3(tac) :=
  repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ ∅ !!ᵣ _ ] |- _ => rewrite lookup_reg_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert_eq in H || (rewrite lookup_insert_ne in H; [| by tac])
  | H : context[ (<[_:=_]ᵣ>_) !! _ ] |- _ =>
    rewrite lookup_insert_reg in H || (rewrite lookup_insert_reg_ne in H; [| by tac])
  | H : context[ (<[_:=_]>_) !!ᵣ _ ] |- _ =>
    rewrite lookup_reg_insert in H || (rewrite lookup_reg_insert_ne in H; [| by tac])
  | H : context[ (<[_:=_]ᵣ>_) !!ᵣ _ ] |- _ =>
    rewrite lookup_reg_insert_reg in H || (rewrite lookup_reg_insert_reg_ne in H; [| by tac])
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter_eq in H || (rewrite lookup_alter_ne in H; [| by tac])
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete_eq in H || (rewrite lookup_delete_ne in H; [| by tac])
  | H : context[ (delete _ _) !!ᵣ _] |- _ =>
    rewrite lookup_reg_delete in H || (rewrite lookup_reg_delete_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton_eq in H || (rewrite lookup_singleton_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !!ᵣ _ ] |- _ =>
    rewrite lookup_reg_singleton in H || (rewrite lookup_reg_singleton_ne in H; [| by tac])
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ ∅ !!ᵣ _ ] => rewrite lookup_reg_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert_eq || (rewrite lookup_insert_ne; [| by tac])
  | |- context[ (<[_:=_]ᵣ>_) !!ᵣ _ ] =>
    rewrite lookup_reg_insert_reg || (rewrite lookup_reg_insert_reg_ne; [| by tac])
  | |- context[ (<[_:=_]ᵣ>_) !! _ ] =>
    rewrite lookup_insert_reg || (rewrite lookup_insert_reg_ne; [| by tac])
  | |- context[ (<[_:=_]>_) !!ᵣ _ ] =>
    rewrite lookup_reg_insert || (rewrite lookup_reg_insert_ne; [| by tac])
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter_eq || (rewrite lookup_alter_ne; [| by tac])
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete_eq || (rewrite lookup_delete_ne; [| by tac])
  | |- context[ (delete _ _) !!ᵣ _ ] =>
    rewrite lookup_reg_delete || (rewrite lookup_reg_delete_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton_eq || (rewrite lookup_singleton_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !!ᵣ _ ] =>
    rewrite lookup_reg_singleton || (rewrite lookup_reg_singleton_ne; [| by tac])
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.


Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map_regs by tac
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !!ᵣ _ = None |- _ => rewrite lookup_reg_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H : {[ _ := _ ]} !!ᵣ _ = Some _ |- _ =>
    rewrite lookup_reg_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !!ᵣ ?i = Some ?x, H2 : ?m2 !!ᵣ ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof (lookup_reg_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
    (*----- *)
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H1 : ?m1 !!ᵣ ?i = Some ?x, H2 : ?m2 !!ᵣ ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_reg_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.

