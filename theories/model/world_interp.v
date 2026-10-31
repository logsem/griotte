From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra rules_base.
From griotte Require Export sts world_std_sts heap_region region_maps.

  (*** Interpretation of the standard world *)

  (** This file defines the interpretation of the standard world over the two
      region maps of a compartment ([region_maps.v]): the map of Permanent
      regions, which mentions no world, and the local map of the thread, read
      off the local world [W].

      The keys of an open world are given as a list: a key Temporary in [W]
      is open in the local map, any other key in the map of Permanent
      regions.

      The lemmas that open and close the world interpretation are in
      [world_ghost_theory.v].
   *)

  (** * Disclaimer to the users of Griotte:

      All the lemmas and definitions in this file are internal to the Griotte model.
      To manipulate the world in the proofs, see [world_ghost_theory.v].

  *)

(** ** The open keys of each part *)

Section open_keys.
  Implicit Types W : WORLD.

  (** The keys of [S] open in the local map: the Temporary ones. *)
  Definition open_set_l W (S : gset LAddr) : gset LAddr :=
    filter (λ k, std W !! k = Some Temporary) S.
  (** The keys of [S] open in the map of Permanent regions: the others. *)
  Definition open_set_perm W (S : gset LAddr) : gset LAddr :=
    filter (λ k, std W !! k ≠ Some Temporary) S.

  Definition open_l W (l : list LAddr) : gset LAddr := open_set_l W (list_to_set l).
  Definition open_perm W (l : list LAddr) : gset LAddr := open_set_perm W (list_to_set l).

  Lemma open_l_nil W : open_l W [] = ∅.
  Proof. by rewrite /open_l /open_set_l /= filter_empty_L. Qed.
  Lemma open_perm_nil W : open_perm W [] = ∅.
  Proof. by rewrite /open_perm /open_set_perm /= filter_empty_L. Qed.

  Lemma elem_of_open_l W l k : k ∈ open_l W l ↔ k ∈ l ∧ std W !! k = Some Temporary.
  Proof. rewrite /open_l /open_set_l elem_of_filter elem_of_list_to_set. tauto. Qed.
  Lemma elem_of_open_perm W l k : k ∈ open_perm W l ↔ k ∈ l ∧ std W !! k ≠ Some Temporary.
  Proof. rewrite /open_perm /open_set_perm elem_of_filter elem_of_list_to_set. tauto. Qed.

  Lemma open_l_permutation W l1 l2 : (∀ k, k ∈ l1 ↔ k ∈ l2) → open_l W l1 = open_l W l2.
  Proof. intros Hl. apply set_eq. intros k. rewrite !elem_of_open_l Hl. done. Qed.
  Lemma open_perm_permutation W l1 l2 : (∀ k, k ∈ l1 ↔ k ∈ l2) → open_perm W l1 = open_perm W l2.
  Proof. intros Hl. apply set_eq. intros k. rewrite !elem_of_open_perm Hl. done. Qed.

  Lemma open_l_add_T W l k :
    std W !! k = Some Temporary → open_l W ({[k]} ∪ l) = {[k]} ∪ open_l W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite elem_of_union elem_of_singleton !elem_of_open_l. set_unfold. naive_solver.
  Qed.
  Lemma open_perm_add_T W l k :
    std W !! k = Some Temporary → open_perm W ({[k]} ∪ l) = open_perm W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite !elem_of_open_perm. set_unfold. naive_solver.
  Qed.
  Lemma open_l_add_nT W l k :
    std W !! k ≠ Some Temporary → open_l W ({[k]} ∪ l) = open_l W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite !elem_of_open_l. set_unfold. naive_solver.
  Qed.
  Lemma open_perm_add_nT W l k :
    std W !! k ≠ Some Temporary → open_perm W ({[k]} ∪ l) = {[k]} ∪ open_perm W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite elem_of_union elem_of_singleton !elem_of_open_perm. set_unfold. naive_solver.
  Qed.

  Lemma not_elem_of_open_l W l k : k ∉ l → k ∉ open_l W l.
  Proof. rewrite elem_of_open_l. tauto. Qed.
  Lemma not_elem_of_open_perm W l k : k ∉ l → k ∉ open_perm W l.
  Proof. rewrite elem_of_open_perm. tauto. Qed.

End open_keys.

Section standard_world_interp.

  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}
    {th : Thread}.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The world interpretation of the section's thread: the two maps of [C],
      with no key open. It owns the safety resources of every key of the
      world. *)
  Definition world_interp_def (W : WORLD) (C : CmptName) : iProp Σ :=
    perm_region_map C ∅ ∗ local_region_map th W C ∅.
  #[local] Definition world_interp_aux : seal (@world_interp_def). Proof. by eexists. Qed.
  Definition world_interp := world_interp_aux.(unseal).
  #[local] Definition world_interp_unseal : @world_interp = @world_interp_def :=
    world_interp_aux.(seal_eq).

  (** The same with the keys of [s] open: it does not own their safety
      resources. A key Temporary in [W] is open in the local map, any other
      key in the map of Permanent regions. *)
  Definition world_interp_open_def (W : WORLD) (C : CmptName) (s : list LAddr) : iProp Σ :=
    perm_region_map C (open_perm W s) ∗ local_region_map th W C (open_l W s).
  #[local] Definition world_interp_open_aux : seal (@world_interp_open_def). Proof. by eexists. Qed.
  Definition world_interp_open := world_interp_open_aux.(unseal).
  #[local] Definition world_interp_open_unseal : @world_interp_open = @world_interp_open_def :=
    world_interp_open_aux.(seal_eq).

  Lemma world_interp_eq W C :
    world_interp W C ⊣⊢ perm_region_map C ∅ ∗ local_region_map th W C ∅.
  Proof. by rewrite world_interp_unseal. Qed.

  Lemma world_interp_open_eq W C s :
    world_interp_open W C s ⊣⊢
    perm_region_map C (open_perm W s) ∗ local_region_map th W C (open_l W s).
  Proof. by rewrite world_interp_open_unseal. Qed.

  Lemma world_interp_open_permutation W C s1 s2 :
    (∀ k, k ∈ s1 ↔ k ∈ s2) →
    world_interp_open W C s1 ⊣⊢ world_interp_open W C s2.
  Proof.
    intros Hs. rewrite !world_interp_open_eq.
    by rewrite (open_l_permutation _ _ _ Hs) (open_perm_permutation _ _ _ Hs).
  Qed.

End standard_world_interp.
