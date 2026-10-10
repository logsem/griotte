From stdpp Require Import countable.
From stdpp Require Export ssreflect.
From stdpp Require Export base gmap list.

Local Coercion Z.of_nat : nat >-> Z.

Global Instance divide_dec : forall p1 p2, Decision (Pos.divide p1 p2).
Proof.
  intros p1 p2.
  destruct (Znumtheory.Zdivide_dec (Z.pos p1) (Z.pos p2)).
  - left. by apply Pos2Z.inj_divide.
  - right. intros Hcontr. apply Pos2Z.inj_divide in Hcontr. done.
Qed.

Lemma zip_nil_r {A B : Type} (l : list A) : zip l ([] : list B) = [].
Proof. destruct l ; done. Qed.

Lemma dom_list_to_map_singleton {K V: Type} `{EqDecision K, Countable K} (x:K) (y:V):
  dom (list_to_map [(x, y)] : gmap K V) = list_to_set [x].
Proof. rewrite dom_insert_L /= dom_empty_L. set_solver. Qed.

Lemma list_to_set_disj_1 {A} `{Countable A, EqDecision A} (l1 l2: list A) :
  l1 ## l2 → (list_to_set l1: gset A) ## list_to_set l2.
Proof.
  intros * HH. rewrite elem_of_disjoint. intros x.
  rewrite !elem_of_list_to_set. rewrite elem_of_disjoint in HH |- *. eauto.
Qed.

Lemma list_to_set_disj_2 {A} `{Countable A, EqDecision A} (l1 l2: list A) :
  (list_to_set l1: gset A) ## list_to_set l2 -> l1 ## l2.
Proof.
  intros * HH. rewrite elem_of_disjoint. intros x.
  rewrite elem_of_disjoint in HH |- *.
  specialize (HH x).
  by rewrite !elem_of_list_to_set in HH.
Qed.

Lemma list_to_set_disj {A} `{Countable A, EqDecision A} (l1 l2: list A) :
  l1 ## l2 <-> (list_to_set l1: gset A) ## list_to_set l2.
Proof.
  split; [apply list_to_set_disj_1 | apply list_to_set_disj_2].
Qed.

Lemma map_to_list_fst {A B : Type} `{EqDecision A, Countable A} (m : gmap A B) i :
  i ∈ (map_to_list m).*1 ↔ (∃ x, (i,x) ∈ (map_to_list m)).
Proof.
  split.
  - intros Hi.
    destruct (m !! i) as [b|] eqn:Hsome.
    + exists b. by apply elem_of_map_to_list.
    + rewrite -(list_to_map_to_list m) in Hsome.
      eapply not_elem_of_list_to_map in Hsome. done.
  - intros [x Hix].
    apply list_elem_of_fmap.
    exists (i,x). auto.
Qed.


Lemma disjoint_nil_l {A : Type} `{EqDecision A} (l2 : list A) :
  [] ## l2.
Proof.
  apply elem_of_disjoint. intros x Hcontr. inversion Hcontr.
Qed.

Lemma disjoint_nil_r {A : Type} `{EqDecision A} (l2 : list A) :
  l2 ## [].
Proof.
  apply elem_of_disjoint. intros x Hl Hcontr. inversion Hcontr.
Qed.

Lemma disjoint_cons {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a :: l1 ## l2 → a ∉ l2.
Proof.
  rewrite elem_of_disjoint =>Ha.
  assert (a ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
  specialize (Ha a Hs). done.
Qed.

Lemma disjoint_swap {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a ∉ l1 →
  a :: l1 ## l2 -> l1 ## a :: l2.
Proof.
  rewrite elem_of_disjoint =>Hnin Ha a' Hl1 Hl2.
  destruct (decide (a' = a)).
  - subst. contradiction.
  - apply Ha with a'.
    + apply elem_of_cons; by right.
    + by apply elem_of_cons in Hl2 as [Hcontr | Hl2]; [contradiction|].
Qed.

Lemma disjoint_weak {A : Type} `{EqDecision A} (a : A) (l1 l2 : list A) :
  a :: l1 ## l2 → l1 ## l2.
Proof.
  rewrite elem_of_disjoint =>Ha a' Hl1 Hl2.
  assert (a' ∈ a :: l1) as Hs; [apply elem_of_cons;auto;apply elem_of_nil|].
  specialize (Ha a' Hs Hl2). done.
Qed.

Lemma drop_S':
    forall A l n (a: A) l',
      drop n l = a::l' ->
      drop (S n) l = l'.
Proof.
  intros A l n a l'.
  revert l' n a.
  induction l as [|x l IHl]; intros l' n a HH.
  - rewrite drop_nil in HH. inversion HH.
  - simpl. destruct n.
    + rewrite drop_0 in HH. inversion HH.
      reflexivity.
    + simpl in HH. eapply IHl; eauto.
Qed.

(* delete_list: delete a list of keys in a map *)

Fixpoint delete_list {K V : Type} `{Countable K, EqDecision K}
           (ks : list K) (m : gmap K V) : gmap K V :=
  match ks with
  | k :: ks' => delete k (delete_list ks' m)
  | [] => m
  end.

Lemma delete_list_insert {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) (v : V) :
  l ∉ ks →
  delete_list ks (<[l:=v]> m) = <[l:=v]> (delete_list ks m).
Proof.
  intros Hnin.
  induction ks as [|k ks IHks]; auto.
  simpl.
  apply not_elem_of_cons in Hnin as [Hneq Hnin].
  rewrite -delete_insert_ne; auto.
  f_equal. by apply IHks.
Qed.

Lemma delete_list_delete {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) :
  l ∉ ks →
  delete_list ks (delete l m) = delete l (delete_list ks m).
Proof.
  intros Hnin.
  induction ks as [|k ks IHks]; auto.
  simpl.
  apply not_elem_of_cons in Hnin as [Hneq Hnin].
  rewrite -delete_delete; auto.
  f_equal. by apply IHks.
Qed.

Lemma lookup_delete_list_notin {K V : Type} `{Countable K, EqDecision K}
      (ks : list K) (m : gmap K V) (l : K) :
  l ∉ ks →
  (delete_list ks m) !! l = m !! l.
Proof.
  intros HH; induction ks; simpl; auto.
  eapply not_elem_of_cons in HH. destruct HH.
  rewrite lookup_delete_ne; auto.
Qed.

Lemma delete_list_permutation {A B} `{Countable A, EqDecision A}
      (l1 l2: list A) (m: gmap A B):
  l1 ≡ₚ l2 → delete_list l1 m = delete_list l2 m.
Proof.
  induction 1 as
    [
    | a la la' Hperm IHPermutation
    | a a' la
    | a0 a1 a2 Ha0_1 IHPermutation1 Ha1_2 IHPermutation2
    ].
  { reflexivity. }
  { cbn; rewrite IHPermutation //. }
  { cbn; rewrite delete_delete //. }
  { rewrite IHPermutation1 //. }
Qed.

(* Map difference for heterogeneous maps, and lemmas relating it to delete_list *)

Definition map_difference_het
  {A B C} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m1: gmap A B) (m2: gmap A C): gmap A B
:=
  filter (fun '(k, v) => m2 !! k = None) m1.

Notation "m1 ∖∖ m2" := (map_difference_het m1 m2) (at level 40, left associativity).

Lemma map_eq' {A B} `{Countable A, EqDecision A, Countable B, EqDecision B}
  (m1 m2: gmap A B):
  m1 = m2 ↔ (forall k v, m1 !! k = Some v ↔ m2 !! k = Some v).
Proof.
  split; first (intros ->; done).
  intros Heq. apply map_eq. intro k. destruct (m2 !! k) eqn:HH.
  { by apply Heq. }
  { destruct (m1 !! k) eqn:HHH; auto. apply Heq in HHH. congruence. }
Qed.

(* rtc *)

Lemma rtc_or_intro {A : Type} (R Q : A → A → Prop) (x y : A) :
  rtc (λ a b, R a b) x y →
  rtc (λ a b, R a b ∨ Q a b) x y.
Proof.
  intros HR. induction HR as [H | x y z HR H H'].
  - done.
  - apply rtc_trans with y; auto.
    apply rtc_once. by left.
Qed.

(* creates a gmap with domain from the list, all pointing to a default value *)
Fixpoint create_gmap_default {K V : Type} `{Countable K}
         (l : list K) (d : V) : gmap K V :=
  match l with
  | [] => ∅
  | k :: tl => <[k:=d]> (create_gmap_default tl d)
  end.

Lemma create_gmap_default_lookup {K V : Type} `{Countable K}
      (l : list K) (d : V) (k : K) :
  k ∈ l ↔ (create_gmap_default l d) !! k = Some d.
Proof.
  split.
  - intros Hk.
    induction l as [|a l IHl]; inversion Hk.
    + by rewrite lookup_insert_eq.
    + destruct (decide (a = k)); [subst; by rewrite lookup_insert_eq|].
      rewrite lookup_insert_ne; auto.
  - intros Hl.
    induction l as [|a l IHl]; inversion Hl.
    destruct (decide (a = k)); [subst;apply list_elem_of_here|].
    apply elem_of_cons. right.
    apply IHl. simplify_map_eq. auto.
Qed.

Lemma create_gmap_default_dom {K V} `{EqDecision K, Countable K} (l: list K) (d: V):
  dom (create_gmap_default l d) = list_to_set l.
Proof.
  induction l as [| a l IHl].
  - cbn. rewrite dom_empty_L //.
  - cbn [create_gmap_default list_to_set]. rewrite dom_insert_L // IHl //.
Qed.

Lemma create_gmap_default_lookup_None {K V : Type} `{Countable K}
  (l : list K) (d : V) (k : K) :
  k ∉ l →
  (create_gmap_default l d) !! k = None.
Proof.
  intros Hk.
  induction l as [|a l IHl];auto.
  simpl. apply not_elem_of_cons in Hk as [Hne Hk].
  rewrite lookup_insert_ne//. apply IHl. auto.
Qed.

Lemma create_gmap_default_permutation {K V : Type} `{Countable K}
  (l l' : list K) (d : V) :
  l ≡ₚ l' →
  (create_gmap_default l d) = (create_gmap_default l' d).
Proof.
  intros Hperm.
  apply map_eq. intros k.
  destruct (decide (k ∈ l)) as [e|n].
  - assert (k ∈ l') as e';[rewrite -Hperm;auto|].
    apply (create_gmap_default_lookup _ d) in e as ->.
    apply (create_gmap_default_lookup _ d) in e' as ->. auto.
  - assert (k ∉ l') as e';[rewrite -Hperm;auto|].
    apply (create_gmap_default_lookup_None _ d) in n as ->.
    apply (create_gmap_default_lookup_None _ d) in e' as ->. auto.
Qed.

Class DisjointList A := disjoint_list : list A → Prop.
#[export] Hint Mode DisjointList ! : typeclass_instances.
Instance: Params (@disjoint_list) 2 := {}.
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") : stdpp_scope.
Notation "##@{ A } Xs" :=
  (@disjoint_list A _ Xs) (at level 20, only parsing) : stdpp_scope.

Section disjoint_list.
  Variable A: Type.
  Context `{Disjoint A, Union A, Empty A}.
  Implicit Types X : A.

  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ##@{A} []
    | disjoint_cons_2 (X : A) (Xs : list A) : X ## ⋃ Xs → ## Xs → ## (X :: Xs).
  Global Existing Instance disjoint_list_default.

  Lemma disjoint_list_cons X Xs : ## (X :: Xs) ↔ X ## ⋃ Xs ∧ ## Xs.
  Proof.
    split; [inversion_clear 1; auto |].
    intros [??]. constructor; auto.
  Qed.
End disjoint_list.

Lemma disjoint_mono_l A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Y ## Z → X ## Z.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Lemma disjoint_mono_r A C `{ElemOf A C} (X Y Z: C) : X ⊆ Y → Z ## Y → Z ## X.
Proof. intros * HXY. rewrite !elem_of_disjoint. eauto. Qed.

Global Instance Empty_list {A}: Empty (list A). exact []. Defined.
Global Instance Union_list {A}: Union (list A). exact app. Defined.
Global Instance Singleton_list {A}: Singleton A (list A). exact (λ a, [a]). Defined.
Global Instance Semiset_list {A}: SemiSet A (list A) .
Proof. split; set_solver. Qed.

Lemma filter_complement_list {A : Type} (l : list A) (P : A -> Prop) {Hdec: ∀ x, Decision (P x)} :
  l ≡ₚ filter P l ∪ filter (λ x : A, ¬ P x) l.
Proof.
  induction l; cbn; first done.
  rewrite /union /Union_list.
  destruct ( decide (P a) ); destruct ( decide (¬ P a) ); try done.
  + rewrite -app_comm_cons {1}IHl; done.
  + rewrite -Permutation_middle {1}IHl; done.
Qed.

Definition prod_op {A B : Type} :=
  λ (o1 : option A) (o2 : option B),
    match o1 with
    | Some b =>
        match o2 with
        | Some c => Some (b,c)
        | None => None
        end
    | None => None
    end.

Definition prod_merge {A B C : Type} `{Countable A} : gmap A B → gmap A C → gmap A (B * C) :=
  λ m1 m2, merge prod_op m1 m2.

(** A typeclass for comparable *)
Class Ord A `{EqDecision A} : Type :=
  { le_a : relation A;
    le_a_decision : ∀ a1 a2, Decision (le_a a1 a2);
    le_a_preorder : PreOrder le_a }.

(* TODO: integrate into stdpp? *)
Lemma pair_eq_inv {A B} {y u : A} {z t : B} {x} :
    x = (y, z) -> x = (u, t) ->
    y = u ∧ z = t.
Proof. intros ->. inversion 1. auto. Qed.

Tactic Notation "simplify_pair_eq" :=
  repeat
    lazymatch goal with
    | H1 : ?x = (?y, ?z), H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 H2)); clear H2
    | H1 : (?y, ?z) = ?x, H2 : ?x = (?u, ?t) |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) H2)); clear H2
    | H1 : ?x = (?y, ?z), H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv H1 (eq_sym H2))); clear H2
    | H1 : (?y, ?z) = ?x, H2 : (?u, ?t) = ?x |- _ =>
      assert (y = u ∧ z = t) as [? ?] by (exact (pair_eq_inv (eq_sym H1) (eq_sym H2))); clear H2
    | |- _ => progress simplify_eq
    end.

(*----------------------- FIXME TEMPORARY ------------------------------------*)
(* This is a copy-paste from stdpp (fin_maps.v), plus a fix to avoid using
   "rewrite .. by .." that is not available when using ssreflect's rewrite. *)
(* TODO: upstream the fix into stdpp, and remove the code below whenever we
   upgrade to a version of stdpp that includes it *)

Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert_eq in H || (rewrite lookup_insert_ne in H; [| by tac])
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter_eq in H || (rewrite lookup_alter_ne in H; [| by tac])
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete_eq in H || (rewrite lookup_delete_ne in H; [| by tac])
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton_eq in H || (rewrite lookup_singleton_ne in H; [| by tac])
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert_eq || (rewrite lookup_insert_ne; [| by tac])
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter_eq || (rewrite lookup_alter_ne; [| by tac])
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete_eq || (rewrite lookup_delete_ne; [| by tac])
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton_eq || (rewrite lookup_singleton_ne; [| by tac])
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    opose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
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
