From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import switcher_spec_call heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import hts_spec_states.

(** * Ghost-only steps between the segments of [hts_main_asm] *)

Section HTS_World_Buffer.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .

  (** The adversary entry is not a heap capability, so its interpretation
      does not depend on the world. *)
  Lemma hts_interp_adv_world (C : CmptName) (C_f : Sealable) W W' :
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    interp W C (WSealed ot_switcher C_f) -∗
    interp W' C (WSealed ot_switcher C_f).
  Proof.
    iIntros (Hadv_nonheap) "#Hadv".
    destruct C_f as [t p g base endp off | t p g ob oe oa].
    - destruct t.
      + rewrite !fixpoint_interp1_eq /= /interp_sb.
        iDestruct "Hadv" as "[$ %Hvalid]".
        iPureIntro.
        rewrite /heap_cap_valid in Hvalid |- *.
        intros Hlt.
        specialize (Hvalid Hlt).
        rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
          in Hadv_nonheap.
        destruct (is_heap_address base) eqn:Hheap; first discriminate.
        exact Hvalid.
      + iApply interp_untagged. reflexivity.
    - destruct t.
      + rewrite !fixpoint_interp1_eq /= /interp_sb.
        iDestruct "Hadv" as "[$ _]".
      + iApply interp_untagged. reflexivity.
  Qed.

  Lemma hts_buffer_heap_address b :
    hts_buffer_bounds b -> is_heap_address b = true.
  Proof.
    intros Hbounds. apply withinBounds_true_iff.
    rewrite /hts_buffer_bounds in Hbounds. solve_addr.
  Qed.

  Lemma hts_Wshare_heap_lookup W_init_C ι b :
    heap_std (hts_Wshare W_init_C ι b) !! ι =
      Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive).
  Proof. by rewrite /hts_Wshare /heap_std_update /= /heap_allocate lookup_insert_eq. Qed.
End HTS_World_Buffer.

Section HTS_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .
  Context (C : CmptName).
  Context (csp_b csp_e : Addr).
  Context (C_f : Sealable) (W_init_C : WORLD).


  Lemma hts_Wshare_std ι b :
    std (hts_Wshare W_init_C ι b) !! LHeap b ι = Some Permanent.
  Proof. by rewrite /hts_Wshare lookup_insert_eq. Qed.

  Lemma hts_buffer_not_stack b :
    hts_buffer_bounds b ->
    disjoint_from_heap csp_b csp_e ->
    b ∉ finz.seq_between csp_b csp_e.
  Proof.
    intros Hbounds Hstk_heap Hb_stk.
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
    eapply (Hstk_heap b); first exact Hb_stk.
    apply elem_of_finz_seq_between.
    apply withinBounds_true_iff in Hb_heap. exact Hb_heap.
  Qed.

  (** Share [b] with the first adversary call: allocate [ι] in the revoked
      world, make [b] a [Permanent] cell holding [0], and transport what the
      switcher needs to [hts_Wshare ι b]. *)
  Lemma hts_world_share_buffer E ι b :
    heap_std W_init_C = ∅ ->
    hts_buffer_bounds b ->
    disjoint_from_heap csp_b csp_e ->
    revoked_addresses (revoke W_init_C) (finz.seq_between (csp_b ^+ 1)%a csp_e) ->
    alloc_obj ι b (b ^+ 1)%a -∗
    b ↦ₕ[ι] WInt 0 -∗
    world_interp (revoke W_init_C) C -∗
    StackRevokedResources W_init_C C (finz.seq_between (csp_b ^+ 1)%a csp_e)
    ={E}=∗
    world_interp (hts_Wshare W_init_C ι b) C ∗
    rel C (LHeap b ι) RW interp_in_memC ∗
    interp (hts_Wshare W_init_C ι b) C (hts_buffer b @@ ι) ∗
    StackRevokedResources (hts_Wshare W_init_C ι b) C
      (finz.seq_between (csp_b ^+ 1)%a csp_e) ∗
    ⌜revoked_addresses (hts_Wshare W_init_C ι b)
      (finz.seq_between (csp_b ^+ 1)%a csp_e)⌝.
  Proof.
    iIntros (Hheap_empty Hbounds Hstk_heap Hstack_revoked)
      "#Hobj Hb Hworld Hstack_revoked".
    set (stk_frame_addrs := finz.seq_between (csp_b ^+ 1)%a csp_e).
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    assert (heap_fresh ∅ ι b (b ^+ 1)%a) as Hfresh_buf.
    { split; [apply lookup_empty|solve_addr]. }
    assert (heap_std (revoke W_init_C) = ∅) as Hheap_revoke.
    { rewrite revoke_heap. exact Hheap_empty. }
    iDestruct (hts_world_empty_heap_fresh (revoke W_init_C) C b ι
      Hheap_revoke with "Hworld") as %Hb_fresh.
    iMod (hts_world_heap_allocate_empty (revoke W_init_C) C ι b (b ^+ 1)%a
      with "Hobj Hworld") as "Hworld".
    { exact Hheap_revoke. }
    { solve_addr. }
    set (Wbuf := heap_std_update (revoke W_init_C)
      (heap_allocate ∅ ι b (b ^+ 1)%a)).
    iDestruct (init_PermRes Wbuf C (LHeap b ι) RW interp_in_memC (WInt 0)
      with "[] Hb []") as "Hbuf_perm".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm Wbuf C (LHeap b ι) (WInt 0) RW interp_in_memC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
    { rewrite /heap_key_live.
      apply (heap_key_status_lookup (heap_allocate ∅ ι b (b ^+ 1)%a) b ι
        (MkAllocObject b (b ^+ 1)%a AllocObjectLive)).
      - by rewrite /heap_allocate lookup_insert_eq.
      - unfold alloc_object_contains; cbn. solve_addr. }
    { subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }
    iAssert (interp (hts_Wshare W_init_C ι b) C (hts_buffer b @@ ι)) as "#Hinterp_buf".
    { iEval (rewrite /hts_buffer fixpoint_interp1_eq /=).
      iSplitL.
      { rewrite /interp_cap_body.
        rewrite (finz_seq_between_cons b); last solve_addr.
        rewrite (finz_seq_between_empty _ (b ^+ 1)%a); last solve_addr.
        iApply big_sepL_singleton.
        iExists RW, (interp_in_mem RWL). iEval (cbn).
        iSplit; first done. iSplit.
        { iPureIntro; intros WCv; tc_solve. }
        iSplit; first iFrame "Hrel_b".
        iSplit; first iApply zcond_interp_in_mem.
        iSplit; first iApply rcond_interp_in_mem.
        iSplit; first iApply wcond_interp_in_mem.
        iSplit; first iApply monoReq_interp_in_mem.
        - rewrite hts_Wshare_std. reflexivity.
        - by intro.
        - iPureIntro. rewrite hts_Wshare_std. reflexivity. }
      iPureIntro. split.
      { split.
        { rewrite /disjoint_from_shadow elem_of_disjoint.
          intros a Ha Hsh.
          pose proof heap_shadow_disjoint as Hdisj.
          rewrite elem_of_disjoint in Hdisj.
          eapply Hdisj; last exact Hsh.
          apply elem_of_finz_seq_between.
          apply elem_of_finz_seq_between in Ha.
          solve_addr. }
        intros Hrev%elem_of_finz_seq_between.
        pose proof revoker_not_heap as Hrev_heap.
        apply not_true_iff_false in Hrev_heap.
        apply Hrev_heap, withinBounds_true_iff.
        solve_addr. }
      intros _. split; first exact Hb_heap.
      eexists. split; first apply hts_Wshare_heap_lookup.
      cbn. repeat split; done || solve_addr. }
    assert (related_sts_priv_world W_init_C (hts_Wshare W_init_C ι b))
      as Hrelated_init_share.
    { eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - eapply related_sts_pub_trans_world.
        + apply related_sts_pub_world_heap_update.
          rewrite revoke_heap Hheap_empty. apply heap_allocate_future.
          exact Hfresh_buf.
        + apply related_sts_pub_world_fresh.
          rewrite /heap_std_update /=. exact Hb_fresh. }
    iDestruct (StackRevokedResources_mono_priv W_init_C (hts_Wshare W_init_C ι b) C
      stk_frame_addrs Hrelated_init_share with "Hstack_revoked")
      as "Hstack_revoked_share".
    iModIntro. iFrame "∗#".
    iPureIntro.
    rewrite /revoked_addresses Forall_forall. intros a Ha.
    rewrite /hts_Wshare lookup_insert_ne; last done.
    cbn. rewrite /revoked_addresses Forall_forall in Hstack_revoked.
    apply Hstack_revoked. exact Ha.
  Qed.

  (** After the first adversary call, [ι] keeps its bounds in [Wret]: its
      status is the case split of the reload (D41). *)
  Lemma hts_Wret_heap_lookup ι b Wret :
    related_sts_pub_world
      (std_update_multiple (hts_Wshare W_init_C ι b)
        (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) Wret ->
    ∃ s, heap_std (revoke Wret) !! ι = Some (MkAllocObject b (b ^+ 1)%a s).
  Proof.
    intros Hrelated.
    assert (related_sts_heap_std (heap_std (hts_Wshare W_init_C ι b)) (heap_std Wret))
      as Hheap_future.
    { rewrite -(std_update_multiple_heap (hts_Wshare W_init_C ι b)
        (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary).
      exact (proj2 (proj2 (proj2 Hrelated))). }
    destruct (proj1 Hheap_future _ _ (hts_Wshare_heap_lookup W_init_C ι b))
      as ([b' e' s] & Hlookup & Hb' & He' & _).
    cbn in Hb', He'. subst b' e'.
    exists s. by rewrite revoke_heap.
  Qed.

  (** A quarantined [ι] in the world gives its quarantine witness. *)
  Lemma hts_world_quarantined_witness ι b Wret :
    heap_std (revoke Wret) !! ι =
      Some (MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined) ->
    world_interp (revoke Wret) C -∗
    world_interp (revoke Wret) C ∗ ι ⊒ AQuar.
  Proof.
    iIntros (Hι) "Hworld".
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    iDestruct (region_heap_provenance with "Hregion") as "[Hregion #Hprov]".
    iDestruct (heap_provenance_quarantined with "Hprov") as "$"; [exact Hι|done|].
    iFrame.
  Qed.

  (** After the first adversary call, with [ι] live in [revoke Wret]: [b]
      is [Permanent] in [revoke Wret]. Open its world entry to get its
      memory back. *)
  Lemma hts_world_reopen_live E ι b Wret :
    hts_buffer_bounds b ->
    related_sts_pub_world
      (std_update_multiple (hts_Wshare W_init_C ι b)
        (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) Wret ->
    heap_std (revoke Wret) !! ι =
      Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive) ->
    rel C (LHeap b ι) RW interp_in_memC -∗
    world_interp (revoke Wret) C
    ={E}=∗
    ∃ v_b : LWord,
      ⌜std (revoke Wret) !! LHeap b ι = Some Permanent⌝ ∗
      world_interp_open (revoke Wret) C [LHeap b ι] ∗
      sts_state_std C (LHeap b ι) Permanent ∗
      b ↦ₕ[ι] v_b.
  Proof.
    iIntros (Hbounds Hrelated_share_ret Hlive_rev) "#Hrel_b Hworld".
    assert (LHeap b ι ∉ LNonHeap <$> finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e)
      as Hb_not_callstk.
    { intros (a & Heq & _)%list_elem_of_fmap. discriminate. }
    assert (std (std_update_multiple (hts_Wshare W_init_C ι b)
      (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) !! LHeap b ι =
      Some Permanent) as Hstd_source.
    { rewrite std_sta_update_multiple_lookup_same_k;
        [exact (hts_Wshare_std ι b)|exact Hb_not_callstk]. }
    assert (LHeap b ι ∈ dom (std Wret)) as Hb_dom_ret.
    { apply (proj1 (proj1 Hrelated_share_ret)).
      apply (elem_of_dom_2 (std _ : gmap LAddr region_type) _ _ Hstd_source). }
    apply (elem_of_dom (std Wret : gmap LAddr region_type)) in Hb_dom_ret.
    destruct Hb_dom_ret as [ρ Hρ].
    pose proof (proj2 (proj1 Hrelated_share_ret)
      (LHeap b ι) Permanent ρ Hstd_source Hρ) as Hrtc.
    assert (ρ = Permanent) as Hperm
      by (eapply std_rel_pub_rtc_Permanent; eauto).
    subst ρ.
    assert (std (revoke Wret) !! LHeap b ι = Some Permanent) as Hstd_rev.
    { apply revoke_lookup_Perm. exact Hρ. }
    iDestruct (open_world_interp (revoke Wret) C (LHeap b ι) RW
      interp_in_memC Permanent with "Hrel_b Hworld")
      as "(Hworld_open & Hstate_b & Hres_b)".
    { rewrite /heap_key_live (heap_key_status_lookup _ _ _ _ Hlive_rev) //.
      unfold alloc_object_contains; cbn.
      rewrite /hts_buffer_bounds in Hbounds. solve_addr. }
    { by right. }
    { exact Hstd_rev. }
    iDestruct "Hres_b" as (v_b) "Hres_b".
    iDestruct "Hres_b" as "(>%Hp_nonO & >Hb_phys & _)".
    iModIntro. iExists v_b. by iFrame.
  Qed.

End HTS_World.

Section HTS_World_Free.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .
  Context (C : CmptName).

  Lemma hts_Wfree_related Wret ι :
    related_sts_priv_world Wret (hts_Wfree Wret ι).
  Proof.
    eapply related_sts_priv_pub_trans_world.
    - apply revoke_related_sts_priv_world.
    - apply related_sts_pub_world_heap_update.
      apply heap_quarantine_future.
  Qed.

  (** After the call to free: [ι ⊒ AQuar] lets the world quarantine [ι], and
      the world entry of [b] closes with no resources. *)
  Lemma hts_world_quarantine E ι b Wret :
    hts_buffer_bounds b ->
    heap_std (revoke Wret) !! ι =
      Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive) ->
    std (revoke Wret) !! LHeap b ι = Some Permanent ->
    rel C (LHeap b ι) RW interp_in_memC -∗
    sts_state_std C (LHeap b ι) Permanent -∗
    ι ⊒ AQuar -∗
    world_interp_open (revoke Wret) C [LHeap b ι]
    ={E}=∗
    world_interp (hts_Wfree Wret ι) C.
  Proof.
    iIntros (Hbounds Hι_lookup Hstd_rev)
      "#Hrel_b Hstate_b #Hquar Hworld_open".
    assert (LHeap b ι ∈ dom (std (revoke Wret))) as Hb_dom_rev.
    { apply (elem_of_dom_2 (std _ : gmap LAddr region_type) _ _ Hstd_rev). }
    iMod (hts_world_open_heap_transition (revoke Wret) C (LHeap b ι) ι
      with "Hquar Hworld_open") as "Hworld_open".
    { exact Hb_dom_rev. }
    iModIntro.
    iApply (close_world_interp_quarantined_heap (hts_Wfree Wret ι) C b ι RW
      interp_in_memC Permanent
      (MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined)
      with "Hworld_open Hrel_b Hstate_b").
    - rewrite /hts_Wfree /heap_std_update /=.
      by rewrite (heap_quarantine_lookup _ ι _ Hι_lookup).
    - reflexivity.
    - unfold alloc_object_contains; cbn.
      rewrite /hts_buffer_bounds in Hbounds. solve_addr.
  Qed.
End HTS_World_Free.
