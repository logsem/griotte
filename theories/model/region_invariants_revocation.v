From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra iris_extra region_invariants world_std_revocation.

(** * Revocation and restoration: the list-based interface

    The region maps revoke and restore sets of keys ([l_revoke],
    [l_restore_open], [l_restore_from], [l_restore_all] in
    [region_maps.v]); the interface of [world_ghost_theory.v] keeps lists
    ([close_list], [RevokedResources]). This file bridges the two. *)

Section bridge.
  Implicit Types W : WORLD.

  Lemma close_list_close_set W l : close_list l W = close_set (list_to_set l) W.
  Proof.
    destruct W as [Ws Wc]. rewrite /close_list /close_set /=. f_equal.
    apply (map_eq (M:=gmap LAddr) (A:=region_type)). intros k. rewrite map_lookup_imap.
    destruct (Ws !! k) as [ρ|] eqn:Hk; simpl.
    - destruct (decide (k ∈ (list_to_set l : gset LAddr))) as [Hin|Hnin].
      + apply elem_of_list_to_set in Hin. destruct ρ; simpl.
        * rewrite -close_list_std_sta_same_alt; rewrite Hk //.
        * rewrite close_list_std_sta_revoked //; rewrite Hk //.
      + rewrite -close_list_std_sta_same; [|by rewrite elem_of_list_to_set in Hnin]; rewrite Hk //.
    - rewrite Hk /=. apply eq_None_not_Some. intros Hs.
      apply (close_list_std_sta_is_Some Ws l k) in Hs. rewrite Hk in Hs. by destruct Hs.
  Qed.

  (** Restoring a key outside the domain changes nothing. *)
  Lemma close_set_dom W S : close_set S W = close_set (S ∩ dom (std W)) W.
  Proof.
    destruct W as [Ws Wc]. rewrite /close_set /=. f_equal.
    apply (map_eq (M:=gmap LAddr) (A:=region_type)). intros k. rewrite !map_lookup_imap.
    destruct (Ws !! k) as [ρ|] eqn:Hk; rewrite Hk /=; [|done].
    assert (k ∈ dom Ws) by (rewrite elem_of_dom; eauto).
    do 2 f_equal. apply decide_ext. set_solver.
  Qed.

End bridge.

Section revoked_resources.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Implicit Types t : Thread.

  Lemma RevokedRes_list t W C (l : list LAddr) :
    NoDup l →
    ([∗ list] k ∈ l, RevokedRes1 t W C k) ⊣⊢ RevokedRes t W C (list_to_set l).
  Proof. intros Hnd. by rewrite /RevokedRes big_sepS_list_to_set. Qed.

  Lemma RevokedRes_subseteq t W C S S' :
    S' ⊆ S → RevokedRes t W C S -∗ RevokedRes t W C S'.
  Proof.
    iIntros (HS) "HR". rewrite /RevokedRes.
    replace S with (S' ∪ S ∖ S') by (apply set_eq; intros k; destruct (decide (k ∈ S')); set_solver).
    rewrite big_sepS_union; [|set_solver]. by iDestruct "HR" as "[$ _]".
  Qed.

  Lemma RevokedRes_list_sub t W C (l : list LAddr) :
    ([∗ list] k ∈ l, RevokedRes1 t W C k) -∗ RevokedRes t W C (list_to_set l).
  Proof.
    induction l as [|k l IH]; simpl.
    - iIntros "_". by rewrite /RevokedRes big_sepS_empty.
    - iIntros "[Hk Hl]". iDestruct (IH with "Hl") as "Hl".
      destruct (decide (k ∈ (list_to_set l : gset LAddr))) as [Hin|Hnin].
      + by replace ({[k]} ∪ list_to_set l : gset LAddr) with (list_to_set l : gset LAddr) by set_solver.
      + rewrite /RevokedRes big_sepS_union; [|set_solver]. rewrite big_sepS_singleton. iFrame.
  Qed.

End revoked_resources.
