From iris.algebra Require Import auth agree excl gmap frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From iris.program_logic Require Import adequacy.
From Stdlib Require Import Eqdep_dec.
From griotte Require Import stdpp_extra iris_extra griotte_lang
     memory_region rules_base rules.
From griotte Require Import disjoint_regions_tactics.

Definition mkregion (r_start r_end: Addr) (contents: list Word): gmap Addr Word :=
  list_to_map (zip (finz.seq_between r_start r_end) contents).

Lemma list_to_map_app {A} `{EqDecision A, Countable A} {B} (l1 l2: list (A * B)) :
  (list_to_map (l1 ++ l2) : gmap A B) = list_to_map l1 ∪ list_to_map l2.
Proof.
  revert l2. induction l1.
  { intros l2. rewrite /= left_id_L //. }
  { intros l2. rewrite /= IHl1 insert_union_l //. }
Qed.



Lemma dom_mkregion_incl a e l:
  dom (mkregion a e l) ⊆ list_to_set (finz.seq_between a e).
Proof.
  rewrite /mkregion. generalize (finz.seq_between a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L. apply empty_subseteq. }
  { intros ll. destruct ll as [| x ll].
    - cbn. rewrite dom_empty_L. done.
    - cbn [list_to_set zip zip_with list_to_map foldr fst snd]. rewrite dom_insert_L.
      set_solver. }
Qed.

Lemma dom_mkregion_incl_rev a e l:
  (a + length l = Some e)%a →
  list_to_set (finz.seq_between a e) ⊆ dom (mkregion a e l).
Proof.
  rewrite /mkregion. intros Hl.
  assert (length (finz.seq_between a e) = length l) as Hl'.
  { rewrite finz_seq_between_length /finz.dist. solve_addr. }
  clear Hl. revert Hl'. generalize (finz.seq_between a e). induction l.
  { intros. rewrite zip_with_nil_r /=. rewrite dom_empty_L.
    destruct l; [| inversion Hl']. cbn. apply empty_subseteq. }
  { intros ll Hll. destruct ll as [| x ll]; [by inversion Hll|].
    cbn [list_to_set zip zip_with list_to_map foldr fst snd].
    rewrite dom_insert_L. cbn in Hll. apply Nat.succ_inj in Hll.
    specialize (IHl ll Hll). set_solver. }
Qed.

Lemma dom_mkregion_eq a e l:
  (a + length l = Some e)%a →
  dom (mkregion a e l) = list_to_set (finz.seq_between a e).
Proof.
  intros Hlen. apply (anti_symm subseteq).
  - apply dom_mkregion_incl.
  - by apply dom_mkregion_incl_rev.
Qed.




(* Note that this tactic can only be applied on the left of the disjointness condition *)
Ltac union_resolve_mkregion :=
  repeat (
      try lazymatch goal with
        | |- _ ∪ _ ⊆ _ =>
            etransitivity; [ eapply union_mono_l | eapply union_mono_r ]
        end;
      [ first [ apply dom_mkregion_incl | reflexivity ] |..]
    ).

(* overwrite `disjoint_map_to_list` ltac to also simplify list_to_map occurrences *)
Ltac disjoint_map_to_list :=
  rewrite (@map_disjoint_dom _ _ (gset Addr)) ?dom_union_L;
  eapply disjoint_mono_l;
  rewrite ?dom_list_to_map_singleton;
  union_resolve_mkregion;
  try match goal with |- _ ## dom (mkregion _ _ _) =>
                        eapply disjoint_mono_r; [ apply dom_mkregion_incl | ] end;
  try match goal with |- _ ## dom (list_to_map _ ) =>
                        rewrite dom_list_to_map_L end;
  rewrite -?list_to_set_app_L ?dom_list_to_map_singleton;
  apply stdpp_extra.list_to_set_disj.

Lemma mkregion_sepM_to_sepL2 `{Σ: gFunctors} (a e: Addr) l (φ: Addr → Word → iProp Σ) :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, φ k v) -∗ ([∗ list] k;v ∈ (finz.seq_between a e); l, φ k v).
Proof.
  rewrite /mkregion. revert a e. induction l as [| x l].
  { cbn. intros. rewrite zip_with_nil_r /=. assert (a = e) as -> by solve_addr.
    rewrite /finz.seq_between finz_dist_0. 2: solve_addr. cbn. eauto. }
  { cbn. intros a e Hlen. rewrite finz_seq_between_cons. 2: solve_addr.
    cbn. iIntros "H". iDestruct (big_sepM_insert with "H") as "[? H]".
    { rewrite -not_elem_of_list_to_map /=.
      intros [ [? ?] [-> [? ?]%elem_of_zip_l%elem_of_finz_seq_between] ]%list_elem_of_fmap.
      solve_addr. }
    iFrame. iApply (IHl with "H"). solve_addr. }
Qed.

Lemma mkregion_prepare `{ceriseG Σ} (a e: Addr) l :
  (a + length l)%a = Some e →
  ⊢ ([∗ map] k↦v ∈ mkregion a e l, k ↦ₐ v) ==∗ ([∗ list] k;v ∈ (finz.seq_between a e); l, k ↦ₐ v).
Proof.
  iIntros (?) "H". iDestruct (mkregion_sepM_to_sepL2 with "H") as "H"; auto.
Qed.
