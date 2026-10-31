From iris.base_logic.lib Require Import ghost_map saved_prop.
From iris.proofmode Require Import proofmode.
From griotte Require Import named_props_extra.
From griotte Require Import region_keys resources heap_region.
From griotte Require Import region_maps.

Section region_maps.
  Context {Σ : gFunctors} {Cname : CmptNameG}
    `{!allocRegistryG Σ, !gen_heapGS Addr LWord Σ}
    {stsg : STSG Σ} {relg : relGS Σ}.
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Implicit Types t : Thread.

  (** ** Tombstones *)

  Definition obj_keys (ι : AId) (b e : Addr) : gset LAddr :=
    set_map (λ a, LHeap a ι) (list_to_set (finz.seq_between b e) : gset Addr).

  Lemma obj_keys_heap ι b e k : k ∈ obj_keys ι b e → ∃ a, k = LHeap a ι.
  Proof. intros (a & -> & _)%elem_of_map. eauto. Qed.

  (** From one persistent [ι ⊒ AQuar], every opened key of [ι] closes with
      the tombstone, in either map. *)
  Lemma perm_close_all_tomb C M O S ι :
    S ## O → (∀ k, k ∈ S → ∃ a, k = LHeap a ι) →
    ι ⊒ AQuar -∗
    ([∗ set] k ∈ S, ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ rel_perm C k p φ) -∗
    perm_region_map_M C M (S ∪ O) -∗ perm_region_map_M C M O.
  Proof.
    iIntros (HSO HH) "#Hq HS Hm".
    iApply (rmap_close_all with "[] [HS] Hm"); [done| |].
    - iIntros "!>" (k p φ Hk). destruct (HH k Hk) as [a ->].
      rewrite /body_perm /heap_key_resource /=. by iRight.
    - iApply (big_sepS_mono with "HS"). iIntros (k _) "(%p & %φ & %Hp & Hr)".
      iExists p, φ. rewrite rel_perm_eq. iFrame "Hr %".
  Qed.

  Lemma l_close_all_tomb t W C M O S ι :
    S ## O → (∀ k, k ∈ S → ∃ a, k = LHeap a ι) →
    ι ⊒ AQuar -∗
    ([∗ set] k ∈ S, ∃ p φ, ⌜∀ x, Persistent (φ x)⌝ ∗ rel_l t C k p φ) -∗
    local_region_map_M t W C M (S ∪ O) -∗ local_region_map_M t W C M O.
  Proof.
    iIntros (HSO HH) "#Hq HS Hw". iNamed "Hw".
    iDestruct (rmap_close_all with "[] [HS] Hm") as "Hm"; [done| | |].
    - iIntros "!>" (k p φ Hk). destruct (HH k Hk) as [a ->]. rewrite /body_l.
      destruct (std W !! LHeap a ι) as [ [] | ];
        [rewrite /temp_res /heap_key_resource /=; by iRight|done..].
    - iApply (big_sepS_mono with "HS"). iIntros (k _) "(%p & %φ & %Hp & Hr)".
      iExists p, φ. rewrite rel_l_eq. iFrame "Hr %".
    - rewrite /local_region_map_M. by iFrame "∗%".
  Qed.

  (** Every key of a live object [ι] whose cells are held is open in the
      map of Permanent regions: a closed one would hold a cell, or a
      tombstone, which the cells' live shares refute. *)
  Lemma no_other_live_entry_perm C M O ι b e :
    alloc_obj ι b e -∗ ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗ perm_region_map_M C M O -∗
    ⌜∀ a, LHeap a ι ∈ dom M → LHeap a ι ∈ O⌝.
  Proof.
    iIntros "#Hobj Hc Hm". iIntros (a [γp Ha]%elem_of_dom).
    destruct (decide (LHeap a ι ∈ O)) as [|HO]; [done|]. iExFalso.
    iDestruct "Hm" as "(_ & #Hks & Hb)".
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hks") as "[_ (%b' & %e' & Hobj' & %Hin)]";
      [exact Ha|].
    iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[<- <-].
    assert (LHeap a ι ∈ obj_keys ι b e) as Hk.
    { apply elem_of_map. exists a. split; [done|].
      apply elem_of_list_to_set, elem_of_finz_seq_between. done. }
    iDestruct (big_sepS_elem_of with "Hc") as (v') "Hv'"; [exact Hk|].
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hb") as "Hb"; [exact Ha|].
    rewrite decide_False //. iDestruct "Hb" as (φ) "(_ & _ & [(%v & _ & Hv & _)|Hq])".
    - by iApply (heap_pointsto_valid_2 with "Hv Hv'").
    - by iApply (heap_pointsto_quar_false with "Hv' Hq").
  Qed.

  Lemma no_other_live_entry_l t W C M O ι b e :
    alloc_obj ι b e -∗ ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗ local_region_map_M t W C M O -∗
    ⌜∀ a, LHeap a ι ∈ dom M → LHeap a ι ∈ O ∨ std W !! LHeap a ι ≠ Some Temporary⌝.
  Proof.
    iIntros "#Hobj Hc Hw". iNamed "Hw". iIntros (a [γp Ha]%elem_of_dom).
    destruct (decide (LHeap a ι ∈ O)) as [|HO]; [by iLeft|].
    destruct (decide (std W !! LHeap a ι = Some Temporary)) as [HT|HT]; [|by iRight].
    iExFalso.
    iDestruct "Hm" as "(_ & #Hks & Hb)".
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hks") as "[_ (%b' & %e' & Hobj' & %Hin)]";
      [exact Ha|].
    iDestruct (alloc_obj_agree with "Hobj Hobj'") as %[<- <-].
    assert (LHeap a ι ∈ obj_keys ι b e) as Hk.
    { apply elem_of_map. exists a. split; [done|].
      apply elem_of_list_to_set, elem_of_finz_seq_between. done. }
    iDestruct (big_sepS_elem_of with "Hc") as (v') "Hv'"; [exact Hk|].
    iDestruct (big_sepM_lookup _ _ (LHeap a ι) with "Hb") as "Hb"; [exact Ha|].
    rewrite decide_False //. iDestruct "Hb" as (φ) "(_ & _ & Hb)". rewrite /body_l HT.
    iDestruct "Hb" as "[(%v & _ & Hv & _)|Hq]".
    - by iApply (heap_pointsto_valid_2 with "Hv Hv'").
    - by iApply (heap_pointsto_quar_false with "Hv' Hq").
  Qed.

  (** Case split over a set of bodies, each holding [P k] or the persistent
      [Q]. *)
  Lemma sepS_cases (S : gset LAddr) (E P : LAddr → iProp Σ) (Q : iProp Σ) `{!Persistent Q} :
    (∀ k, k ∈ S → E k ⊢ P k ∨ (Q ∗ E k)) → (∀ k, k ∈ S → P k ⊢ E k) →
    ([∗ set] k ∈ S, E k) ⊢ ([∗ set] k ∈ S, P k) ∨ (Q ∗ [∗ set] k ∈ S, E k).
  Proof.
    induction S as [|x S Hx IH] using set_ind_L; intros HE HP.
    - rewrite !big_sepS_empty. iIntros "_". by iLeft.
    - rewrite !big_sepS_insert //. iIntros "[Ex ES]".
      iDestruct (HE x ltac:(set_solver) with "Ex") as "[Px|[#HQ Ex] ]".
      + iDestruct (IH with "ES") as "[PS|[#HQ ES] ]".
        { intros k Hk. apply HE. set_solver. }
        { intros k Hk. apply HP. set_solver. }
        * iLeft. iFrame.
        * iRight. iFrame "HQ ES". iApply (HP x ltac:(set_solver) with "Px").
      + iRight. iFrame "HQ Ex ES".
  Qed.

  #[local] Definition perm_entry C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp, ⌜M !! k = Some γp⌝ ∗ rentry (body_perm C) k γp.
  #[local] Definition lentry W C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp, ⌜M !! k = Some γp⌝ ∗ rentry (body_l W C) k γp.
  #[local] Definition keep {A} `{!savedPredG Σ A} (M : gmap LAddr (gname * Perm))
      (k : LAddr) : iProp Σ :=
    ∃ γp (φ : A → iProp Σ), ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ.
  #[local] Definition perm_cell C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp φ, ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ ∗
      ∃ v, ⌜isO γp.2 = false⌝ ∗ k ↦ₖ v ∗ ▷ φ (C, v).
  #[local] Definition lcell W C (M : gmap LAddr (gname * Perm)) (k : LAddr) : iProp Σ :=
    ∃ γp φ, ⌜M !! k = Some γp⌝ ∗ ⌜∀ x, Persistent (φ x)⌝ ∗
      saved_pred_own γp.1 DfracDiscarded φ ∗
      ∃ v, ⌜isO γp.2 = false⌝ ∗ temp_body k v ∗ future_pub_mono C φ v ∗ ▷ φ (W, C, v).

  (** [free] in the owned maps, with keys open: the keys of [ι] (each in the
      map that holds it, [Sg] in the map of Permanent regions, [Sl] in the
      local map, where they are Temporary) are opened. Stale branch: some
      body is a tombstone, and every key closes again. Live branch: every
      body is a cell; the cells come out, and once [ι ⊒ AQuar] holds every
      opened key closes with the tombstone. *)
  Lemma free_owned C t W Mg Ml Og Ol ι b e (Sg Sl : gset LAddr) :
    Sg ⊆ dom Mg → Sl ⊆ dom Ml → Sg ## Sl → Sg ∪ Sl = obj_keys ι b e →
    Sg ## Og → Sl ## Ol →
    (∀ k, k ∈ Sl → std W !! k = Some Temporary) →
    perm_region_map_M C Mg Og -∗ local_region_map_M t W C Ml Ol -∗
    (ι ⊒ AQuar ∗ perm_region_map_M C Mg Og ∗ local_region_map_M t W C Ml Ol) ∨
    (([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) ∗
     perm_region_map_M C Mg (Sg ∪ Og) ∗ local_region_map_M t W C Ml (Sl ∪ Ol) ∗
     (ι ⊒ AQuar -∗ perm_region_map_M C Mg (Sg ∪ Og) -∗ local_region_map_M t W C Ml (Sl ∪ Ol) -∗
      perm_region_map_M C Mg Og ∗ local_region_map_M t W C Ml Ol)).
  Proof.
    iIntros (HSg HSl Hdisj Hobj HgO HlO HT) "Hg Hl". iNamed "Hl".
    assert (∀ k, k ∈ Sg → ∃ a, k = LHeap a ι) as HHg.
    { intros k Hk. apply (obj_keys_heap ι b e). set_solver. }
    assert (∀ k, k ∈ Sl → ∃ a, k = LHeap a ι) as HHl.
    { intros k Hk. apply (obj_keys_heap ι b e). set_solver. }
    rewrite /perm_region_map_M (rmap_split_set _ Mg _ Og Sg HSg HgO).
    rewrite (rmap_split_set _ Ml _ Ol Sl HSl HlO).
    iDestruct "Hg" as "[Hg HEg]". iDestruct "Hm" as "[Hm HEl]".
    iDestruct (sepS_cases Sg (perm_entry C Mg) (perm_cell C Mg) (ι ⊒ AQuar) with "HEg")
      as "[HPg|[#Hq HEg] ]".
    { intros k Hk. destruct (HHg k Hk) as [a ->].
      iIntros "(%γp & %HM & %φ & %Hp & #Hsp & [Hc|#Hq])".
      - iLeft. iExists γp, φ. by iFrame "∗#%".
      - iRight. iFrame "Hq". iExists γp. iSplit; [done|]. iExists φ. by iFrame "#%". }
    { intros k Hk. destruct (HHg k Hk) as [a ->].
      iIntros "(%γp & %φ & %HM & %Hp & #Hsp & Hc)". iExists γp. iSplit; [done|].
      iExists φ. iSplit; [done|]. iSplit; [done|]. by iLeft. }
    (* stale, from the map of Permanent regions *)
    2:{ iLeft. iFrame "Hq Hg". iSplitL "HEg"; [by rewrite /perm_entry|].
        rewrite /local_region_map_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). by iFrame. }
    iDestruct (sepS_cases Sl (lentry W C Ml) (lcell W C Ml) (ι ⊒ AQuar) with "HEl")
      as "[HPl|[#Hq HEl] ]".
    { intros k Hk. destruct (HHl k Hk) as [a ->].
      iIntros "(%γp & %HM & %φ & %Hp & #Hsp & Hb)". rewrite /body_l HT //.
      iDestruct "Hb" as "[Hc|#Hq]".
      - iLeft. iExists γp, φ. iSplit; [done|]. iSplit; [done|]. by iFrame "Hsp".
      - iRight. iFrame "Hq". iExists γp. iSplit; [done|]. iExists φ.
        iSplit; [done|]. iSplit; [done|]. rewrite /body_l HT //. by iRight. }
    { intros k Hk. destruct (HHl k Hk) as [a ->].
      iIntros "(%γp & %φ & %HM & %Hp & #Hsp & Hc)". iExists γp. iSplit; [done|].
      iExists φ. iSplit; [done|]. iSplit; [done|]. rewrite /body_l HT //. by iLeft. }
    (* stale, from the local map *)
    2:{ iLeft. iFrame "Hq Hg". iSplitL "HPg".
        - iApply (big_sepS_impl with "HPg").
          iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & Hc)".
          destruct (HHg k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
          iSplit; [done|]. iSplit; [done|]. by iLeft.
        - rewrite /local_region_map_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). iFrame "Hm Hloc".
          iSplit; [done|]. by rewrite /lentry. }
    (* live *)
    iRight.
    iAssert (([∗ set] k ∈ Sg, ∃ v, k ↦ₖ v) ∗ [∗ set] k ∈ Sg, keep (A:=CmptName * LWord) Mg k)%I
      with "[HPg]" as "[HCg #HKg]".
    { rewrite -big_sepS_sep. iApply (big_sepS_mono with "HPg").
      iIntros (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & %v & _ & Hv & _)".
      iSplitL "Hv"; [by iExists v|]. iExists γp, φ. iSplit; [done|]. by iSplit. }
    iAssert (([∗ set] k ∈ Sl, ∃ v, k ↦ₖ v) ∗
             [∗ set] k ∈ Sl, keep (A:=WORLD * CmptName * LWord) Ml k)%I
      with "[HPl]" as "[HCl #HKl]".
    { rewrite -big_sepS_sep. iApply (big_sepS_mono with "HPl").
      iIntros (k Hk) "(%γp & %φ & %HM & %Hp & #Hsp & %v & _ & Hv & _)".
      iSplitL "Hv"; [by iExists v|]. iExists γp, φ. iSplit; [done|]. by iSplit. }
    iSplitL "HCg HCl". { rewrite -Hobj big_sepS_union //. iFrame. }
    iFrame "Hg". iSplitL "Hm Hloc".
    { rewrite /local_region_map_M. iFrame "Hm Hloc". done. }
    iIntros "#Hq Hg Hl". iDestruct "Hl" as "(_ & Hm & Hloc)". iFrame "Hg".
    iSplitR.
    - iApply (big_sepS_impl with "HKg"). iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & Hsp)".
      destruct (HHg k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
      iSplit; [done|]. iFrame "Hsp". by iRight.
    - rewrite /local_region_map_M (rmap_split_set _ Ml _ Ol Sl HSl HlO). iFrame "Hm Hloc".
      iSplit; [done|].
      iApply (big_sepS_impl with "HKl"). iIntros "!>" (k Hk) "(%γp & %φ & %HM & %Hp & Hsp)".
      destruct (HHl k Hk) as [a ->]. iExists γp. iSplit; [done|]. iExists φ.
      iSplit; [done|]. iFrame "Hsp". rewrite /body_l HT //. by iRight.
  Qed.

  (** The full status of a live object from its cells' shares, the client's
      half and the allocator's share; the cells become plain points-tos. *)
  Lemma free_owned_status ι b e :
    alloc_obj ι b e -∗
    ([∗ set] k ∈ obj_keys ι b e, ∃ v, k ↦ₖ v) -∗
    ι ↦st{1/2} ALive -∗ ι ↦st{share (finz.dist b e)} ALive -∗
    ι ↦st{1} ALive ∗
    [∗ set] k ∈ obj_keys ι b e, ∃ v, laddr_addr k ↦ₐ v.
  Proof.
    assert (Inj eq eq (λ a, LHeap a ι)) as Hinj by (intros a1 a2 [= ->]; done).
    iIntros "#Hobj Hc Hhalf Hal".
    rewrite /obj_keys !big_opS_set_map big_sepS_list_to_set; [|apply finz_seq_between_NoDup].
    rewrite big_sepS_list_to_set; [|apply finz_seq_between_NoDup].
    iAssert ([∗ list] a ∈ finz.seq_between b e, a ↦ₐ - ∗ ι ↦st{share (finz.dist b e)} ALive)%I
      with "[Hc]" as "Hc".
    { iApply (big_sepL_impl with "Hc"). iIntros "!>" (i a Ha) "(%v & Hv)".
      iDestruct (heap_pointsto_split with "Hobj Hv") as "[Hv $]". by iExists v. }
    rewrite big_sepL_sep. iDestruct "Hc" as "[$ Hs]".
    rewrite (st_own_split_alloc ι (finz.seq_between b e)) finz_seq_between_length. iFrame.
  Qed.

  (** A Temporary heap key whose object is quarantined while it is open:
      it closes with the tombstone, the revoke extracts it, and the restore
      closes it from the tombstone alone (no cell, no content). *)
  Lemma heap_T_tombstone_cycle t W C O S a ι p φ :
    LHeap a ι ∉ O → (∀ x, Persistent (φ x)) →
    extract_T W O ({[LHeap a ι]} ∪ S) → LHeap a ι ∉ S →
    ι ⊒ AQuar -∗ rel_l t C (LHeap a ι) p φ -∗
    local_region_map t W C ({[LHeap a ι]} ∪ O) -∗
    local_region_map t (close_set {[LHeap a ι]} (revoke W)) C O ∗ RevokedRes t W C S.
  Proof.
    iIntros (HkO Hp HS HkS) "#Hq #Hr Hw".
    destruct (HS (LHeap a ι)) as [ [HT _] _]; [set_solver|].
    iDestruct (l_close _ W _ O (LHeap a ι) p φ HkO HT Hp with "Hw Hr []") as "Hw".
    { rewrite /temp_res /=. by iRight. }
    iDestruct (l_revoke with "Hw") as "[Hw HR]"; [exact HS|].
    rewrite /RevokedRes big_sepS_union; [|set_solver]. iDestruct "HR" as "[_ $]".
    iApply (l_restore_open _ _ _ O {[LHeap a ι]} with "Hw [ ]").
    { rewrite dom_revoke. apply elem_of_dom_std_2 in HT. set_solver. }
    replace ({[LHeap a ι]} ∖ O) with ({[LHeap a ι]} : gset LAddr) by set_solver.
    rewrite /RevokedRes big_sepS_singleton. iExists p, φ. iFrame "Hr %".
    rewrite /temp_res /=. by iRight.
  Qed.

End region_maps.
