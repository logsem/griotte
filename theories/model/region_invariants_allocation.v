From iris.proofmode Require Import proofmode.
From griotte Require Export
  stdpp_extra iris_extra region_invariants sealing_invariants sts_multiple_updates.

Section region_alloc.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {relg : relGS Σ}
    `{MP: MachineParameters}.

  Local Hint Rewrite std_update_multiple_heap std_update_keys_heap : heap.
  Local Hint Extern 2 (heap_key_live _ _) =>
    progress autorewrite with heap; assumption : core.
  Local Hint Extern 2 (Forall (heap_key_live _) _) =>
    progress autorewrite with heap; assumption : core.
  Local Hint Extern 2 (heap_std _ = heap_std _) =>
    progress autorewrite with heap; reflexivity : core.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma key_pointsto_dupl_false (k : LAddr) v1 v2 :
    k ↦ₖ v1 -∗ k ↦ₖ v2 -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (key_pointsto_eq with "H1") as "[H1 _]".
    iDestruct (key_pointsto_eq with "H2") as "[H2 _]".
    iApply (addr_dupl_false with "H1 H2").
  Qed.

  (** Lemmas for extending the region map.

      The core lemma adds a fresh key [k] in state [ρ], given the resources
      of its heap branch. *)
  Lemma extend_region_key E W C (k : LAddr) ρ p φ `{∀ Wv, Persistent (φ Wv)} :
    k ∉ dom (std W) →
    sts_full_world W C -∗
    region W C -∗
    heap_key_resource (heap_std W) k (region_std_interp (<s[k := ρ]s>W) C k p φ ρ)

    ={E}=∗

    region (<s[k := ρ]s>W) C ∗
    rel C k p φ ∗
    sts_full_world (<s[k := ρ]s>W) C.
  Proof.
    iIntros (Hnone) "Hfull Hreg Hk".
    iDestruct (heap_key_resource_known with "Hk") as %Hknown_k.
    rewrite region_eq rel_eq /region_def /rel_def.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    iDestruct "Hpreds" as "[%Hknown [Hheap Hpreds]]".
    destruct (M !! k) eqn:HRl.
    { (* The location is not in the map *)
      exfalso. apply Hnone. rewrite HMW elem_of_dom HRl. eauto. }
    (* if not, we need to allocate a new saved pred using φ,
       and extend R with k := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ k γpred p with "Hγrel") as "[HR Hγrel]"; auto.
    iMod (sts_alloc_std_i W C k ρ with "[] Hfull") as "(Hfull & Hstate)"; auto.
    assert (related_sts_pub_world W (<s[k := ρ]s>W)) as Hrelated
        by by apply related_sts_pub_world_fresh.
    assert (heap_keys_known (heap_std (<s[k := ρ]s>W)) (dom (std (<s[k := ρ]s>W))))
      as Hknown'.
    { rewrite /std_update /= dom_insert_L.
      apply heap_keys_known_insert_new; last done.
      destruct k as [a|a ι]; first done.
      destruct Hknown_k as (o & Ho & _). by apply elem_of_dom_2 in Ho. }
    iDestruct (region_map_monotone with "[Hpreds Hheap]") as "Hpreds'";
      [exact Hrelated|reflexivity|exact Hknown'|iFrame "%∗"|].
    iDestruct "Hpreds'" as "[_ [Hheap Hpreds']]".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[k := ρ]> Mρ); iSplitR; [|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iSplit; first done. iApply big_sepM_insert; auto.
      iSplitR "Hpreds'".
      { iExists ρ. iFrame. iSplitR; [iPureIntro; apply lookup_insert_eq|].
        iExists γpred. by iFrame "%#". }
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (k' x Hk') "Hρ".
      iDestruct "Hρ" as (ρ' Hρ') "[Hstate Hρ]".
      iExists ρ'.
      assert (k' ≠ k) as Hne by (intros ->; rewrite HRl in Hk'; done).
      rewrite lookup_insert_ne; auto. iSplitR; [auto|]. iFrame.
  Qed.

  Lemma extend_region_temp E W C k v p φ `{∀ Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    isO p = false ->
    k ∉ dom (std W) →
    (if isWL p then future_pub_mono C φ v else
       (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)) -∗
    sts_full_world W C -∗
    region W C -∗
    k ↦ₖ v -∗
    φ (W,C,v)

    ={E}=∗

    region (<s[k := Temporary ]s>W) C ∗
    rel C k p φ ∗
    sts_full_world (<s[k := Temporary ]s>W) C.
  Proof.
    iIntros (Hlive HnpO Hnone) "#HmonoV Hfull Hreg Hk Hφ".
    iApply (extend_region_key with "Hfull Hreg"); first done.
    iApply heap_key_resource_live_intro; first done.
    rewrite /region_std_interp. iExists v. iFrame "Hk HmonoV".
    iSplit; first done.
    assert (related_sts_pub_world W (<s[k := Temporary]s>W)) as Hrelated
        by by apply related_sts_pub_world_fresh.
    iNext.
    destruct (isWL p); [|destruct (isDL p)].
    all: iApply ("HmonoV" with "[] Hφ"); iPureIntro.
    1,2: done.
    by apply related_sts_pub_priv_world.
  Qed.

  Lemma extend_region_perm E W C k v p φ `{∀ Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    isO p = false ->
    k ∉ dom (std W) →
    future_priv_mono C φ v -∗
    sts_full_world W C -∗
    region W C -∗
    k ↦ₖ v -∗
    φ (W,C,v)

    ={E}=∗

    region (<s[k := Permanent ]s>W) C ∗
    rel C k p φ ∗
    sts_full_world (<s[k := Permanent ]s>W) C.
  Proof.
    iIntros (Hlive HnpO Hnone) "#HmonoV Hfull Hreg Hk Hφ".
    iApply (extend_region_key with "Hfull Hreg"); first done.
    iApply heap_key_resource_live_intro; first done.
    rewrite /region_std_interp. iExists v. iFrame "Hk HmonoV".
    iSplit; first done.
    iNext. iApply ("HmonoV" with "[] Hφ"); iPureIntro.
    by apply related_sts_pub_priv_world, related_sts_pub_world_fresh.
  Qed.

  (** Revoked entries require only the saved predicate and standard state. *)
  Lemma extend_region_revoked E W C k p φ `{∀ Wv, Persistent (φ Wv)} :
    heap_key_live (heap_std W) k ->
    k ∉ dom (std W) →
    sts_full_world W C -∗
    region W C

    ={E}=∗

    region (<s[k := Revoked ]s>W) C ∗
    rel C k p φ ∗
    sts_full_world (<s[k := Revoked ]s>W) C.
  Proof.
    iIntros (Hlive Hnone) "Hfull Hreg".
    iApply (extend_region_key with "Hfull Hreg"); first done.
    iApply heap_key_resource_emp. by eexists.
  Qed.

  (** Entries of a quarantined object hold no resources, whatever their state. *)
  Lemma extend_region_quarantined_heap E W C k p φ (ρ : region_type) `{∀ Wv, Persistent (φ Wv)} :
    heap_key_status (heap_std W) k = Some AllocObjectQuarantined ->
    k ∉ dom (std W) →
    sts_full_world W C -∗
    region W C

    ={E}=∗

    region (<s[k := ρ ]s>W) C ∗
    rel C k p φ ∗
    sts_full_world (<s[k := ρ ]s>W) C.
  Proof.
    iIntros (Hquar Hnone) "Hfull Hreg".
    iApply (extend_region_key with "Hfull Hreg"); first done.
    iApply (heap_key_resource_quarantined_irrel _ _ emp); first done.
    iApply heap_key_resource_emp. by eexists.
  Qed.

  (** Extensions by a list of keys. *)
  Lemma extend_region_revoked_keys E W C (l1 : list LAddr) p φ `{∀ Wv, Persistent (φ Wv)} :
    Forall (λ k, std W !! k = None) l1 →
    Forall (heap_key_live (heap_std W)) l1 →
    sts_full_world W C -∗
    region W C

    ={E}=∗

    region (std_update_keys W l1 Revoked) C ∗
    ([∗ list] k ∈ l1, rel C k p φ) ∗
    sts_full_world (std_update_keys W l1 Revoked) C.
  Proof.
    induction l1 as [|k l1 IH].
    - cbn. iIntros (_ _) "Hsts Hr". by iFrame.
    - intros [Hk Hl1]%Forall_cons_1 [Hlive_k Hlive_l1]%Forall_cons_1.
      iIntros "Hsts Hr".
      iMod (IH with "Hsts Hr") as "(Hr & #Hrels & Hsts)"; [done|done|].
      simpl. destruct (decide (k ∈ l1)) as [Hin|Hnin].
      + iDestruct (big_sepL_elem_of with "Hrels") as "Hk"; first exact Hin.
        rewrite (_ : <s[k:=Revoked]s>(std_update_keys W l1 Revoked)
                     = std_update_keys W l1 Revoked).
        { by iFrame "∗#". }
        rewrite /std_update insert_id; last by apply std_update_keys_lookup_in.
        by destruct (std_update_keys W l1 Revoked) as [ [ [] ] ].
      + assert (k ∉ dom (std (std_update_keys W l1 Revoked))) as Hnone.
        { rewrite not_elem_of_dom std_update_keys_lookup_same //. }
        assert (heap_key_live (heap_std (std_update_keys W l1 Revoked)) k) as Hlive.
        { by rewrite std_update_keys_heap. }
        iMod (extend_region_revoked _ _ _ k p φ Hlive Hnone with "Hsts Hr")
          as "(Hr & Hrel & Hsts)".
        by iFrame "∗#".
  Qed.

  Lemma extend_region_temp_keys E W C (l1 : list LAddr) l2 p φ `{∀ Wv, Persistent (φ Wv)} :
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    Forall (heap_key_live (heap_std W)) l1 →
    sts_full_world W C -∗
    region W C -∗
    ([∗ list] k;v ∈ l1;l2,
       k ↦ₖ v ∗
       φ (W, C, v) ∗
       (if isWL p then future_pub_mono C φ v else
          (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)))

    ={E}=∗

    region (std_update_keys W l1 Temporary) C ∗
    ([∗ list] k ∈ l1, rel C k p φ) ∗
    sts_full_world (std_update_keys W l1 Temporary) C.
  Proof.
    revert l2. induction l1 as [|k l1 IH].
    - cbn. iIntros (l2 _ _ _) "Hsts Hr _". by iFrame.
    - intros l2 HnpO [Hk Hl1]%Forall_cons_1 [Hlive_k Hlive_l1]%Forall_cons_1.
      iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hkl1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (key_pointsto_dupl_false with "H1 H2"). }
      destruct l2 as [|v l2]; [by inversion Hlen|].
      iDestruct (big_sepL2_cons with "Hl") as "[(Hk & Hφ & #Hf) Hl]".
      iMod (IH with "Hsts Hr Hl") as "(Hr & Hrels & Hsts)"; [done|done|done|].
      assert (related_sts_pub_world W (std_update_keys W l1 Temporary)) as Hrelated.
      { apply related_sts_pub_update_keys.
        eapply Forall_impl; first exact Hl1. intros. by rewrite not_elem_of_dom. }
      assert (k ∉ dom (std (std_update_keys W l1 Temporary))) as Hnone.
      { rewrite not_elem_of_dom std_update_keys_lookup_same //. }
      assert (heap_key_live (heap_std (std_update_keys W l1 Temporary)) k) as Hlive.
      { by rewrite std_update_keys_heap. }
      iMod (extend_region_temp _ _ _ k v p φ Hlive HnpO Hnone
             with "Hf Hsts Hr Hk [Hφ]") as "(Hr & Hrel & Hsts)".
      { destruct (isWL p); [|destruct (isDL p)].
        all: iApply ("Hf" with "[] Hφ"); iPureIntro.
        1,2: done.
        by apply related_sts_pub_priv_world. }
      iModIntro. cbn. iFrame.
  Qed.

  Lemma extend_region_perm_keys E W C (l1 : list LAddr) l2 p φ `{∀ Wv, Persistent (φ Wv)} :
    isO p = false ->
    Forall (λ k, std W !! k = None) l1 →
    Forall (heap_key_live (heap_std W)) l1 →
    sts_full_world W C -∗
    region W C -∗
    ([∗ list] k;v ∈ l1;l2,
       k ↦ₖ v ∗
       φ (W, C, v) ∗
       future_priv_mono C φ v)

    ={E}=∗

    region (std_update_keys W l1 Permanent) C ∗
    ([∗ list] k ∈ l1, rel C k p φ) ∗
    sts_full_world (std_update_keys W l1 Permanent) C.
  Proof.
    revert l2. induction l1 as [|k l1 IH].
    - cbn. iIntros (l2 _ _ _) "Hsts Hr _". by iFrame.
    - intros l2 HnpO [Hk Hl1]%Forall_cons_1 [Hlive_k Hlive_l1]%Forall_cons_1.
      iIntros "Hsts Hr Hl".
      iDestruct (big_sepL2_length with "Hl") as %Hlen.
      iDestruct (NoDup_of_sepL2_exclusive with "[] Hl") as %[Hkl1 ND]%NoDup_cons.
      { iIntros (? ? ?) "(H1 & ? & ?) (H2 & ? & ?)".
        iApply (key_pointsto_dupl_false with "H1 H2"). }
      destruct l2 as [|v l2]; [by inversion Hlen|].
      iDestruct (big_sepL2_cons with "Hl") as "[(Hk & Hφ & #Hf) Hl]".
      iMod (IH with "Hsts Hr Hl") as "(Hr & Hrels & Hsts)"; [done|done|done|].
      assert (related_sts_pub_world W (std_update_keys W l1 Permanent)) as Hrelated.
      { apply related_sts_pub_update_keys.
        eapply Forall_impl; first exact Hl1. intros. by rewrite not_elem_of_dom. }
      assert (k ∉ dom (std (std_update_keys W l1 Permanent))) as Hnone.
      { rewrite not_elem_of_dom std_update_keys_lookup_same //. }
      assert (heap_key_live (heap_std (std_update_keys W l1 Permanent)) k) as Hlive.
      { by rewrite std_update_keys_heap. }
      iMod (extend_region_perm _ _ _ k v p φ Hlive HnpO Hnone
             with "Hf Hsts Hr Hk [Hφ]") as "(Hr & Hrel & Hsts)".
      { iApply ("Hf" with "[] Hφ"); iPureIntro.
        by apply related_sts_pub_priv_world. }
      iModIntro. cbn. iFrame.
  Qed.

  (** Extensions by a list of non-heap addresses. *)
  Lemma extend_region_revoked_sepL2 E W C l1 p φ `{∀ Wv, Persistent (φ Wv)}:
    Forall (λ k, std W !! LNonHeap k = None) l1 →
    sts_full_world W C -∗
    region W C

    ={E}=∗

    region (std_update_multiple W l1 Revoked) C ∗
    ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ) ∗
    sts_full_world (std_update_multiple W l1 Revoked) C.
  Proof.
    iIntros (Hnone) "Hsts Hr".
    iMod (extend_region_revoked_keys _ W C (LNonHeap <$> l1) p φ with "Hsts Hr")
      as "(Hr & Hrels & Hsts)".
    { by apply Forall_fmap. }
    { apply Forall_fmap, Forall_true. intros. apply heap_key_live_nonheap. }
    rewrite !std_update_keys_nonheap. iEval (rewrite big_sepL_fmap) in "Hrels".
    by iFrame.
  Qed.

  Lemma extend_region_temp_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) l1 →
    sts_full_world W C -∗
    region W C -∗
    ([∗ list] k;v ∈ l1;l2,
       k ↦ₐ v ∗
       φ (W, C, v) ∗
       (if isWL p then future_pub_mono C φ v else
          (if isDL p then future_pub_mono C φ v else future_priv_mono C φ v)))

    ={E}=∗

    region (std_update_multiple W l1 Temporary) C ∗
    ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ) ∗
    sts_full_world (std_update_multiple W l1 Temporary) C.
  Proof.
    iIntros (HnpO Hnone) "Hsts Hr Hl".
    iMod (extend_region_temp_keys _ W C (LNonHeap <$> l1) l2 p φ with "Hsts Hr [Hl]")
      as "(Hr & Hrels & Hsts)".
    { done. }
    { by apply Forall_fmap. }
    { apply Forall_fmap, Forall_true. intros. apply heap_key_live_nonheap. }
    { rewrite big_sepL2_fmap_l. iExact "Hl". }
    rewrite !std_update_keys_nonheap. iEval (rewrite big_sepL_fmap) in "Hrels".
    by iFrame.
  Qed.

  Lemma extend_region_perm_sepL2 E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) l1 →
    sts_full_world W C -∗
    region W C -∗
    ([∗ list] k;v ∈ l1;l2,
       k ↦ₐ v ∗
       φ (W, C, v) ∗
       future_priv_mono C φ v)

    ={E}=∗

    region (std_update_multiple W l1 Permanent) C ∗
    ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ) ∗
    sts_full_world (std_update_multiple W l1 Permanent) C.
  Proof.
    iIntros (HnpO Hnone) "Hsts Hr Hl".
    iMod (extend_region_perm_keys _ W C (LNonHeap <$> l1) l2 p φ with "Hsts Hr [Hl]")
      as "(Hr & Hrels & Hsts)".
    { done. }
    { by apply Forall_fmap. }
    { apply Forall_fmap, Forall_true. intros. apply heap_key_live_nonheap. }
    { rewrite big_sepL2_fmap_l. iExact "Hl". }
    rewrite !std_update_keys_nonheap. iEval (rewrite big_sepL_fmap) in "Hrels".
    by iFrame.
  Qed.

  (** Extensions of an opened region by non-heap addresses. *)
  Lemma extend_region_perm_open E W C a w p la1 φ `{∀ Wv, Persistent (φ Wv)} :
    LNonHeap a ∉ dom (std W) →
    a ∉ la1 ->
    sts_full_world (std_update_multiple W la1 Permanent) C -∗
    open_region_many (std_update_multiple W la1 Permanent) C (LNonHeap <$> la1) -∗
    a ↦ₐ w
    ={E}=∗
    open_region_many (std_update_multiple W (a::la1) Permanent) C (LNonHeap <$> (a::la1))
    ∗ rel C a p φ
    ∗ a ↦ₐ w
    ∗ sts_state_std C (LNonHeap a) Permanent
    ∗ sts_full_world (std_update_multiple W (a::la1) Permanent) C.
  Proof.
    iIntros (Hnone ?) "Hfull Hreg Ha".
    assert (LNonHeap a ∉ dom (std (std_update_multiple W la1 Permanent))) as Hnone'.
    {
      rewrite not_elem_of_dom.
      rewrite std_sta_update_multiple_lookup_same_i; eauto.
      by rewrite -not_elem_of_dom.
    }
    rewrite open_region_many_eq /open_region_many_def ?fmap_cons.
    iDestruct "Hreg" as (M Mρ) "(Hγrel & %HMW & %HMρ & Hpreds)".
    iDestruct "Hpreds" as "[%Hknown [Hheap Hpreds]]".
    destruct (M !! LNonHeap a) eqn:HRl.
    { (* The location is not in the map *)
      assert ((delete_list (LNonHeap <$> la1)) M !! LNonHeap a = Some o) as HRl'.
      { rewrite lookup_delete_list_notin; auto. }
      iDestruct (big_sepM_delete _ _ _ _ HRl' with "Hpreds") as "[Hl' _]".
      iDestruct "Hl'" as (ρ' Hl) "[Hstate Hl']".
      iDestruct (sts_full_state_std with "Hfull Hstate") as %Hcontr.
      rewrite (not_elem_of_dom _ (LNonHeap a)) in Hnone'.
      by rewrite Hcontr in Hnone'.
    }
    rewrite /region_map_def.
    (* if not, we need to allocate a new saved pred using φ, *)
    (*      and extend R with l := pred *)
    iMod (saved_pred_alloc φ) as (γpred) "#Hφ'"; first apply dfrac_valid_discarded.
    iMod (update_RELS _ _ _ a γpred p with "Hγrel") as "[HR #Hγrel]"; auto.
    iAssert (rel C a p φ) as "Ha_rel".
    { rewrite rel_eq /rel_def; iFrame "#". }
    iMod (sts_alloc_std_i _ C (LNonHeap a) Permanent
           with "[] Hfull") as "(Hfull & Hstate)"; auto.
    apply (related_sts_pub_world_fresh (std_update_multiple W la1 Permanent) a Permanent)
      in Hnone' as Hrelated; auto.
    iDestruct (region_map_monotone with "[Hpreds Hheap]") as "Hpreds'";
      [apply Hrelated|reflexivity| |iFrame "%∗"|].
    { rewrite /std_update /= dom_insert_L. by apply heap_keys_known_insert_new. }
    iDestruct "Hpreds'" as "[%Hknown' [Hheap Hpreds']]".
    iModIntro. rewrite bi.sep_exist_r. iExists _.
    iFrame "HR ∗ #".
    iExists (<[LNonHeap a :=Permanent]> Mρ);iSplitR;[|iSplitR].
    - iPureIntro. rewrite /std_update in HMW |- *.
      repeat rewrite dom_insert_L; rewrite HMW; auto.
    - iPureIntro. repeat rewrite dom_insert_L. rewrite HMρ. auto.
    - iSplit; first done. cbn.
      rewrite -(delete_list_delete _ (<[LNonHeap a :=(γpred, p)]> M)); last done.
      rewrite delete_insert_id; last done.
      rewrite -(delete_list_delete _ (<[LNonHeap a :=_]> Mρ)); last done.
      rewrite delete_insert_id; last (rewrite -not_elem_of_dom HMρ not_elem_of_dom; done).
      iApply (big_sepM_mono with "Hpreds'").
      iIntros (a' x Ha) "Hρ".
      iDestruct "Hρ" as (ρ Hρ) "[Hstate Hρ]".
      iExists ρ.
      iFrame.
      done.
  Qed.

  Lemma extend_region_perm_sepL2_open_ind E W C la1 la2 lw2 p φ `{∀ Wv, Persistent (φ Wv)}:
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) la2 →
    NoDup la1 ->
    NoDup la2 ->
    la2 ## la1 ->
    sts_full_world (std_update_multiple W la1 Permanent) C -∗
    open_region_many (std_update_multiple W la1 Permanent) C (LNonHeap <$> la1) -∗
    ([∗ list] k;v ∈ la2;lw2, k ↦ₐ v)

    ={E}=∗

    open_region_many (std_update_multiple W (la1++la2) Permanent) C (LNonHeap <$> (la1++la2))
    ∗ ([∗ list] k;v ∈ la2;lw2,
          k ↦ₐ v
          ∗ sts_state_std C (LNonHeap k) Permanent)
    ∗ ([∗ list] k ∈ la2, rel C (LNonHeap k) p φ)
    ∗ sts_full_world (std_update_multiple W (la1++la2) Permanent) C.
  Proof.
    revert la1 lw2.
    induction la2.
    { cbn. intros. iIntros "? ? ?".
      rewrite app_nil_r. iFrame. iModIntro. done. }
    iIntros (la1 lw2 Hp HW Hnodup_l1 Hnodup_l2 Hdisj) "Hsts Hreg Hl2".
    apply NoDup_cons in Hnodup_l2 as [Hna Hnodup_l2].
    apply disjoint_cons in Hdisj as Hni'.
    apply disjoint_swap in Hdisj;auto.
    apply Forall_cons in HW as [HWa HW].
    iDestruct (big_sepL2_length with "Hl2") as "%Hlen_l2".
    destruct lw2 as [|w lw2]; simplify_eq.
    iDestruct "Hl2" as "[ Ha Hl2]".
    replace (std_update_multiple W (la1 ++ a :: la2) Permanent)
              with (std_update_multiple W ( a::(la1 ++ la2)) Permanent).
    2: { apply std_update_multiple_permutation.
         apply Permutation_middle.
    }
    iMod (extend_region_perm_open with "Hsts Hreg Ha") as "(Hreg & Hrel & Ha & Hsts_std & Hsts)"; auto.
    { by rewrite not_elem_of_dom. }
    iMod (IHla2 (a::la1) lw2 with "[Hsts] [Hreg] [Hl2]") as "(Hreg&?&?&?)"; auto.
    { apply NoDup_cons;auto. }
    iDestruct (open_region_many_permutation _ _ _ (LNonHeap <$> (la1 ++ a :: la2)) with "Hreg") as "Hreg".
    { apply fmap_Permutation. apply Permutation_middle. }
    iFrame "∗#".
    done.
  Qed.

  Lemma region_close_many E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)} :
    NoDup l1 ->
    isO p = false ->
    ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ) -∗
    open_region_many W C (LNonHeap <$> l1) -∗
    ([∗ list] k;v ∈ l1;l2, k ↦ₐ v ∗ sts_state_std C (LNonHeap k) Permanent) -∗
    ([∗ list] v ∈ l2, φ (W, C, v)) -∗
    ([∗ list] v ∈ l2, future_priv_mono C φ v)
    ={E}=∗ region W C.
  Proof.
    revert l2.
    induction l1; iIntros (l2 HNoDup Hp) "#Hrel Hreg Hl Hφ Hmono".
    {by rewrite region_open_nil. }
    iDestruct (big_sepL2_length with "Hl") as %Hlen.
    destruct l2; [ by inversion Hlen |]; simplify_eq.
    cbn.
    iDestruct "Hrel" as "[Ha_rel Hrel]".
    iDestruct "Hl" as "[(Ha & Ha_std) Hl]".
    iDestruct "Hφ" as "[Ha_φ Hφ]".
    iDestruct "Hmono" as "[Ha_mono Hmono]".
    apply NoDup_cons in HNoDup as [Ha_l1 HNoDup].
    iDestruct (region_close_next_perm with "[$Ha_std $Hreg $Ha $Ha_mono $Ha_φ $Ha_rel]")
      as "Hreg"; eauto.
    { apply heap_key_live_nonheap. }
    iMod (IHl1 with "Hrel Hreg Hl Hφ Hmono"); auto.
  Qed.

  Lemma extend_region_perm_sepL2_open E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)}:
    NoDup l1 ->
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) l1 →
    sts_full_world W C
    -∗ region W C
    -∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ v)
    -∗ (
         ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ)
         -∗ ([∗ list] v ∈ l2,
               (φ ((std_update_multiple W l1 Permanent), C, v)) ∗ future_priv_mono C φ v)
       )

    ={E}=∗

    region (std_update_multiple W l1 Permanent) C
    ∗ sts_full_world (std_update_multiple W l1 Permanent) C
    ∗ ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ)
    ∗ ([∗ list] v ∈ l2,
               (φ ((std_update_multiple W l1 Permanent), C, v)) ∗ future_priv_mono C φ v).
  Proof.
    iIntros (HNoDup Hp Hl1) "Hsts Hreg Hl".
    iMod (extend_region_perm_sepL2_open_ind E W C [] l1 l2 p φ with "[Hsts] [Hreg] [Hl]") as
    "(Hreg & Hl & #Hrel & Hsts)"; auto.
    { apply NoDup_nil. auto. }
    { eapply disjoint_nil_r. }
    { by rewrite -region_open_nil. }
    { cbn; iFrame "Hrel Hsts".
      iIntros "Hφ".
      iDestruct ("Hφ" with "Hrel") as "#Hφ".
      iFrame "#".
      iDestruct (big_sepL_sep with "Hφ") as "[Hφ' Hmono]".
      iMod (region_close_many with "Hrel Hreg Hl Hφ' Hmono"); eauto.
    }
  Qed.

  Lemma extend_region_perm_sepL2_open'
    {sealsg: sealStoreG Σ} E W C l1 l2 p φ `{∀ Wv, Persistent (φ Wv)} o ws ws_sealed:
    let W' := (<o[ o := ws ]o> (std_update_multiple W l1 Permanent)) in
    NoDup l1 ->
    isO p = false ->
    Forall (λ k, std W !! LNonHeap k = None) l1 →
    sts_full_world W C
    -∗ region W C
    -∗ sealing_map W C
    -∗ ([∗ list] k;v ∈ l1;l2, k ↦ₐ v)
    -∗ (
         ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ)
         ∗ sts_full_world (std_update_multiple W l1 Permanent) C
         ∗ sealing_map (std_update_multiple W l1 Permanent) C
         ∗ open_region_many (std_update_multiple W l1 Permanent) C (LNonHeap <$> l1)
         ==∗
         sts_full_world W' C ∗
         sealing_map W' C ∗
         open_region_many W' C (LNonHeap <$> l1) ∗
         ([∗ list] v ∈ l2, (φ (W', C, v)) ∗ future_priv_mono C φ v) ∗
         ([∗ set] v ∈ ws_sealed, (φ (W', C, v)))
       )

    ={E}=∗

    region W' C
    ∗ sts_full_world W' C
    ∗ sealing_map W' C
    ∗ ([∗ list] k ∈ l1, rel C (LNonHeap k) p φ)
    ∗ ([∗ list] v ∈ l2, (φ (W', C, v)) ∗ future_priv_mono C φ v)
    ∗ ([∗ set] v ∈ ws_sealed, (φ (W', C, v)))
.
  Proof.
    intros W'; subst W'.

    iIntros (HNoDup Hp Hl1) "Hsts Hreg Hseals Hl Hφ".
    iMod (extend_region_perm_sepL2_open_ind E W C [] l1 l2 p φ with "[Hsts] [Hreg] [Hl]") as
    "(Hreg & Hl & #Hrel & Hsts)"; auto.
    { apply NoDup_nil. auto. }
    { eapply disjoint_nil_r. }
    { by rewrite -region_open_nil. }

    iDestruct (sealing_map_monotone_pub _ _ (std_update_multiple W l1 Permanent) with "Hseals") as "Hseals".
    { by rewrite std_update_multiple_seals. }
    { apply related_sts_pub_update_multiple.
      eapply Forall_impl; first exact Hl1.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }
    iMod ("Hφ" with "[$Hrel $Hsts $Hseals $Hreg]") as "(Hsts & Hseals & Hreg & #Hφ & #Hφ')".
    cbn; iFrame "Hrel Hsts".
    iFrame "#".
    iDestruct (big_sepL_sep with "Hφ") as "[Hφ'' Hmono]".
    iDestruct (open_region_many_monotone _ _ (<o[o:=ws]o>(std_update_multiple W l1 Permanent)) with "Hreg") as "Hreg".
    { auto. }
    { apply related_sts_pub_refl_world. }
    { reflexivity. }
    iMod (region_close_many with "Hrel Hreg Hl Hφ'' Hmono") as "Hreg"; eauto.
    by iFrame.
  Qed.

End region_alloc.
