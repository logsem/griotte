From iris.proofmode Require Import proofmode.
From griotte Require Export stdpp_extra rules_base.
From griotte Require Export sts world_std_sts world_ghost_resources heap_region region_maps.

  (*** Interpretation of the standard world *)

  (** This file defines the interpretation of the standard world over the two
      region maps of a compartment ([region_maps.v]): the map of Permanent
      regions, which mentions no world, and the local map of the thread, read
      off the local world [W].

      The keys of an open world are given as a list: a key Temporary in [W]
      is open in the local map, any other key in the map of Permanent
      regions.

      Finally, this file defines lemma to open / close the standard world.
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
  Definition open_set_g W (S : gset LAddr) : gset LAddr :=
    filter (λ k, std W !! k ≠ Some Temporary) S.

  Definition open_l W (l : list LAddr) : gset LAddr := open_set_l W (list_to_set l).
  Definition open_g W (l : list LAddr) : gset LAddr := open_set_g W (list_to_set l).

  Lemma open_l_nil W : open_l W [] = ∅.
  Proof. by rewrite /open_l /open_set_l /= filter_empty_L. Qed.
  Lemma open_g_nil W : open_g W [] = ∅.
  Proof. by rewrite /open_g /open_set_g /= filter_empty_L. Qed.

  Lemma elem_of_open_l W l k : k ∈ open_l W l ↔ k ∈ l ∧ std W !! k = Some Temporary.
  Proof. rewrite /open_l /open_set_l elem_of_filter elem_of_list_to_set. tauto. Qed.
  Lemma elem_of_open_g W l k : k ∈ open_g W l ↔ k ∈ l ∧ std W !! k ≠ Some Temporary.
  Proof. rewrite /open_g /open_set_g elem_of_filter elem_of_list_to_set. tauto. Qed.

  Lemma open_l_perm W l1 l2 : (∀ k, k ∈ l1 ↔ k ∈ l2) → open_l W l1 = open_l W l2.
  Proof. intros Hl. apply set_eq. intros k. rewrite !elem_of_open_l Hl. done. Qed.
  Lemma open_g_perm W l1 l2 : (∀ k, k ∈ l1 ↔ k ∈ l2) → open_g W l1 = open_g W l2.
  Proof. intros Hl. apply set_eq. intros k. rewrite !elem_of_open_g Hl. done. Qed.

  Lemma open_l_add_T W l k :
    std W !! k = Some Temporary → open_l W ({[k]} ∪ l) = {[k]} ∪ open_l W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite elem_of_union elem_of_singleton !elem_of_open_l. set_unfold. naive_solver.
  Qed.
  Lemma open_g_add_T W l k :
    std W !! k = Some Temporary → open_g W ({[k]} ∪ l) = open_g W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite !elem_of_open_g. set_unfold. naive_solver.
  Qed.
  Lemma open_l_add_nT W l k :
    std W !! k ≠ Some Temporary → open_l W ({[k]} ∪ l) = open_l W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite !elem_of_open_l. set_unfold. naive_solver.
  Qed.
  Lemma open_g_add_nT W l k :
    std W !! k ≠ Some Temporary → open_g W ({[k]} ∪ l) = {[k]} ∪ open_g W l.
  Proof.
    intros Hk. apply set_eq. intros k'.
    rewrite elem_of_union elem_of_singleton !elem_of_open_g. set_unfold. naive_solver.
  Qed.

  Lemma not_elem_of_open_l W l k : k ∉ l → k ∉ open_l W l.
  Proof. rewrite elem_of_open_l. tauto. Qed.
  Lemma not_elem_of_open_g W l k : k ∉ l → k ∉ open_g W l.
  Proof. rewrite elem_of_open_g. tauto. Qed.

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

  (** The standard world of the section's thread, with the keys of [l] open. *)
  Definition open_region_many_def (W : WORLD) (C : CmptName) (l : list LAddr) : iProp Σ :=
    world_interp_open_gl W C (open_g W l) (open_l W l).
  #[local] Definition open_region_many_aux : seal (@open_region_many_def). Proof. by eexists. Qed.
  Definition open_region_many := open_region_many_aux.(unseal).
  Definition open_region_many_eq : @open_region_many = @open_region_many_def :=
    open_region_many_aux.(seal_eq).

  Definition region (W : WORLD) (C : CmptName) : iProp Σ := open_region_many W C [].

  Lemma region_eq W C : region W C ⊣⊢ world_interp_open_gl W C ∅ ∅.
  Proof. by rewrite /region open_region_many_eq /open_region_many_def open_l_nil open_g_nil. Qed.

  Lemma open_region_many_permutation W C l1 l2 :
    (∀ k, k ∈ l1 ↔ k ∈ l2) →
    open_region_many W C l1 ⊣⊢ open_region_many W C l2.
  Proof.
    intros Hl. rewrite open_region_many_eq /open_region_many_def.
    by rewrite (open_l_perm _ _ _ Hl) (open_g_perm _ _ _ Hl).
  Qed.

  (** ** Opening and closing a Temporary key, in the local map *)

  Lemma region_open_temp W C l k p φ :
    k ∉ l → std W !! k = Some Temporary →
    open_region_many W C l -∗ rel_l th C k p φ -∗
    open_region_many W C ({[k]} ∪ l) ∗
    heap_key_resource k
      (∃ v, ⌜isO p = false⌝ ∗ k ↦ₖ v ∗ ▷ future_pub_mono C φ v ∗ ▷ φ (W, C, v)).
  Proof.
    iIntros (Hkl HT) "Hr Hrel".
    rewrite open_region_many_eq /open_region_many_def /world_interp_open_gl.
    rewrite open_l_add_T // open_g_add_T //.
    iDestruct "Hr" as "[$ Hl]".
    iApply (l_open_transport with "Hl Hrel"); [by apply not_elem_of_open_l|done].
  Qed.

  Lemma region_close_temp W C l k p φ :
    k ∉ l → std W !! k = Some Temporary → (∀ x, Persistent (φ x)) →
    open_region_many W C ({[k]} ∪ l) -∗ rel_l th C k p φ -∗ temp_res W C k p φ -∗
    open_region_many W C l.
  Proof.
    iIntros (Hkl HT Hp) "Hr Hrel Hb".
    rewrite open_region_many_eq /open_region_many_def /world_interp_open_gl.
    rewrite open_l_add_T // open_g_add_T //.
    iDestruct "Hr" as "[$ Hl]".
    iApply (l_close with "Hl Hrel Hb"); [by apply not_elem_of_open_l|done..].
  Qed.

  (** ** Opening and closing a key of the map of Permanent regions *)

  Lemma region_open_perm W C l k p φ :
    k ∉ l → std W !! k ≠ Some Temporary →
    open_region_many W C l -∗ rel_g C k p φ -∗
    open_region_many W C ({[k]} ∪ l) ∗ body_g C k p φ.
  Proof.
    iIntros (Hkl HT) "Hr Hrel".
    rewrite open_region_many_eq /open_region_many_def /world_interp_open_gl.
    rewrite open_l_add_nT // open_g_add_nT //.
    iDestruct "Hr" as "[Hg $]".
    iApply (g_open_transport with "Hg Hrel"). by apply not_elem_of_open_g.
  Qed.

  Lemma region_close_perm W C l k p φ :
    k ∉ l → std W !! k ≠ Some Temporary → (∀ x, Persistent (φ x)) →
    open_region_many W C ({[k]} ∪ l) -∗ rel_g C k p φ -∗ body_g C k p φ -∗
    open_region_many W C l.
  Proof.
    iIntros (Hkl HT Hp) "Hr Hrel Hb".
    rewrite open_region_many_eq /open_region_many_def /world_interp_open_gl.
    rewrite open_l_add_nT // open_g_add_nT //.
    iDestruct "Hr" as "[Hg $]".
    iApply (g_close with "Hg Hrel Hb"); [by apply not_elem_of_open_g|done..].
  Qed.

  (** ** Heap keys, closed with a tombstone *)

  Lemma region_close_temp_quarantined_heap W C l a ι p φ :
    LHeap a ι ∉ l → std W !! LHeap a ι = Some Temporary → (∀ x, Persistent (φ x)) →
    ι ⊒ AQuar -∗
    open_region_many W C ({[LHeap a ι]} ∪ l) -∗ rel_l th C (LHeap a ι) p φ -∗
    open_region_many W C l.
  Proof.
    iIntros (Hkl HT Hp) "#Hq Hr Hrel".
    iApply (region_close_temp with "Hr Hrel"); [done..|].
    rewrite /temp_res /=. by iRight.
  Qed.

  Lemma region_close_perm_quarantined_heap W C l a ι p φ :
    LHeap a ι ∉ l → std W !! LHeap a ι ≠ Some Temporary → (∀ x, Persistent (φ x)) →
    ι ⊒ AQuar -∗
    open_region_many W C ({[LHeap a ι]} ∪ l) -∗ rel_g C (LHeap a ι) p φ -∗
    open_region_many W C l.
  Proof.
    iIntros (Hkl HT Hp) "#Hq Hr Hrel".
    iApply (region_close_perm with "Hr Hrel"); [done..|].
    rewrite /body_g /=. by iRight.
  Qed.

End standard_world_interp.
