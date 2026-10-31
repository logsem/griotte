From iris.proofmode Require Import proofmode.
From griotte Require Export
  stdpp_extra iris_extra world_interp sts_multiple_updates.

Section region_alloc.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Implicit Types t : Thread.

  (** A cell refutes a closed body of the map of Permanent regions at its
      key: the body is the same cell or, for a heap key, a tombstone. *)
  Lemma body_g_cell_false C k p φ v :
    body_g C k p φ -∗ k ↦ₖ v -∗ False.
  Proof.
    iIntros "Hb Hv". rewrite /body_g. destruct k as [a|a ι]; simpl.
    - iDestruct "Hb" as (v') "(_ & Hv' & _)". iApply (addr_dupl_false with "Hv Hv'").
    - iDestruct "Hb" as "[(%v' & _ & Hv' & _)|Hq]".
      + iApply (key_pointsto_dupl_false (LHeap a ι) with "Hv Hv'").
      + iApply (heap_pointsto_quar_false with "Hv Hq").
  Qed.

  (** ** Extending the map of Permanent regions

      A new key enters the map of Permanent regions of [C] with no world
      step: its cell shows that it is fresh in the map. *)
  Lemma g_extend C O k v p (φ : CmptName * LWord → iProp Σ) :
    k ∉ O → isO p = false → (∀ x, Persistent (φ x)) →
    world_interp_g_open C O -∗ heap_key_known k -∗ k ↦ₖ v -∗ ▷ φ (C, v) ==∗
    world_interp_g_open C O ∗ rel_g C k p φ.
  Proof.
    iIntros (HkO HpO Hpers) "(%M & Hm) #Hkn Hv Hφ".
    destruct (M !! k) as [γp|] eqn:HMk.
    { iExFalso. iDestruct "Hm" as "(_ & _ & Hb)".
      iDestruct (big_sepM_lookup with "Hb") as "Hb"; [exact HMk|].
      rewrite decide_False //. iDestruct "Hb" as (φ') "(_ & _ & Hb)".
      iApply (body_g_cell_false with "Hb Hv"). }
    iMod (rmap_insert _ M _ O k p φ with "Hm Hkn [Hv Hφ]") as (γp) "[Hm Hr]".
    { by apply not_elem_of_dom. }
    { done. }
    { rewrite /body_g. destruct k; simpl; [|iLeft]; iExists v; by iFrame. }
    iModIntro. iSplitL "Hm"; [by iExists _|]. by rewrite rel_g_eq.
  Qed.

  (** ** Extending the local map

      A fresh key enters the local world in a local state, with its body in
      the new world; the other bodies move along the public step. *)
  Lemma l_extend t W C O k ρ p φ :
    k ∉ dom (std W) → k ∉ O → (∀ x, Persistent (φ x)) →
    world_interp_l_open t W C O -∗ heap_key_known k -∗ body_l (<s[k := ρ]s> W) C k p φ ==∗
    world_interp_l_open t (<s[k := ρ]s> W) C O ∗ rel_l t C k p φ.
  Proof.
    iIntros (Hk HkO Hpers) "(%M & Hw) #Hkn Hb". iNamed "Hw".
    assert (M !! k = None) as HMk.
    { apply not_elem_of_dom. by rewrite -Hdom. }
    assert (related_sts_pub_world W (<s[k := ρ]s> W)) as Hpub.
    { by apply related_sts_pub_world_fresh. }
    iDestruct (rmap_transform _ M _ (body_l (<s[k := ρ]s> W) C) O O (λ _, emp)%I (λ _, emp)%I
      with "[] [] Hm") as "[Hm _]".
    { iApply big_sepM_intro. by iIntros "!>" (???). }
    { iIntros "!>" (k' γp Hk') "_ _ Hb'". iSplitL; [|done].
      case_decide; [done|].
      iDestruct "Hb'" as (φ') "(%Hp & #Hsp & Hb')". iExists φ'. iFrame "#%".
      iApply (body_l_mono_pub with "Hb'"); [done|].
      assert (k' ≠ k) by (intros ->; congruence).
      rewrite /std_update /= lookup_insert_ne //. }
    iMod (rmap_insert _ M _ O k p φ with "Hm Hkn Hb") as (γp) "[Hm Hr]"; [by apply not_elem_of_dom|done|].
    iModIntro. iSplitR "Hr"; [|by rewrite rel_l_eq].
    iExists _. rewrite /wil_M. iFrame "Hm". iFrame "Hloc". iPureIntro.
    rewrite /std_update /= !dom_insert_L. set_solver.
  Qed.

  (** Global regions enter the map open: each cell shows that its key is
      fresh. *)
  Lemma g_insert_open_list C M O (ks : list LAddr) (lw : list LWord) p (φ : CmptName * LWord → iProp Σ) :
    NoDup ks → (∀ k, k ∈ ks → k ∉ O) →
    rmap (γrel_g C) M (body_g C) O -∗ ([∗ list] k;v ∈ ks;lw, k ↦ₖ v) ==∗
    ∃ M', rmap (γrel_g C) M' (body_g C) (list_to_set ks ∪ O) ∗
      ([∗ list] k ∈ ks, rel_g C k p φ) ∗ ([∗ list] k;v ∈ ks;lw, k ↦ₖ v).
  Proof.
    iInduction ks as [|k ks IH] "IH" forall (M O lw).
    { iIntros (_ _) "Hm Hl". iModIntro. iExists M. rewrite union_empty_l_L. by iFrame. }
    iIntros (Hnd HO) "Hm Hl".
    apply NoDup_cons in Hnd as [Hk Hnd].
    iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lw' ->) "[Hv Hl]".
    destruct (M !! k) as [γp|] eqn:HMk.
    { iExFalso. iDestruct "Hm" as "(_ & _ & Hb)".
      iDestruct (big_sepM_lookup with "Hb") as "Hb"; [exact HMk|].
      rewrite decide_False; [|apply HO; set_solver].
      iDestruct "Hb" as (φ') "(_ & _ & Hb)".
      iApply (body_g_cell_false with "Hb Hv"). }
    iDestruct (key_pointsto_known with "Hv") as "#Hkn".
    iMod (rmap_insert_open _ M _ O k p φ with "Hm Hkn") as (γp) "[Hm Hr]"; [by apply not_elem_of_dom|].
    iMod ("IH" $! _ ({[k]} ∪ O) lw' with "[] [] Hm Hl") as (M') "(Hm & Hrs & Hl)".
    { done. }
    { iPureIntro. intros k' Hk'. apply not_elem_of_union. split; [set_solver|]. apply HO. set_solver. }
    iModIntro. iExists M'.
    replace (list_to_set (k :: ks) ∪ O) with (list_to_set ks ∪ ({[k]} ∪ O)) by set_solver.
    iFrame "Hm Hrs Hl Hv". by rewrite rel_g_eq.
  Qed.

  (** Closing open Global regions, each with its cell and its predicate. *)
  Lemma g_close_list C M O (ks : list LAddr) (lw : list LWord) p (φ : CmptName * LWord → iProp Σ) :
    NoDup ks → (∀ k, k ∈ ks → k ∉ O) → isO p = false → (∀ x, Persistent (φ x)) →
    rmap (γrel_g C) M (body_g C) (list_to_set ks ∪ O) -∗
    ([∗ list] k;v ∈ ks;lw, k ↦ₖ v ∗ ▷ φ (C, v) ∗ rel_g C k p φ) -∗
    rmap (γrel_g C) M (body_g C) O.
  Proof.
    iInduction ks as [|k ks IH] "IH" forall (O lw).
    { iIntros (_ _ _ _) "Hm _". by rewrite union_empty_l_L. }
    iIntros (Hnd HO HpO Hpers) "Hm Hl".
    apply NoDup_cons in Hnd as [Hk Hnd].
    iDestruct (big_sepL2_cons_inv_l with "Hl") as (v lw' ->) "[(Hv & Hφ & Hr) Hl]".
    replace (list_to_set (k :: ks) ∪ O) with (list_to_set ks ∪ ({[k]} ∪ O)) by set_solver.
    iDestruct ("IH" $! ({[k]} ∪ O) lw' with "[] [] [] [] Hm Hl") as "Hm".
    { done. }
    { iPureIntro. intros k' Hk'. apply not_elem_of_union. split; [set_solver|]. apply HO. set_solver. }
    { done. }
    { done. }
    rewrite rel_g_eq.
    iApply (rmap_close with "Hm Hr"); [apply HO; set_solver|].
    rewrite /body_g. iApply heap_key_resource_intro. iExists v. by iFrame "∗%".
  Qed.

End region_alloc.
