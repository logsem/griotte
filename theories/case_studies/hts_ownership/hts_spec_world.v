From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import switcher_base.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants.
From griotte.case_studies.hts_ownership Require Import hts_spec_states.

(** * Ghost-only steps between the segments of [hts_main_asm] *)

Section HTS_World_Buffer.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
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
      + rewrite !interp_unfold /= /interp_sb.
        iDestruct "Hadv" as "[$ $]".
      + iApply interp_untagged. reflexivity.
    - destruct t.
      + rewrite !interp_unfold /= /interp_sb.
        iDestruct "Hadv" as "[$ _]".
      + iApply interp_untagged. reflexivity.
  Qed.

  Lemma hts_buffer_heap_address b :
    hts_buffer_bounds b -> is_heap_address b = true.
  Proof.
    intros Hbounds. apply withinBounds_true_iff.
    rewrite /hts_buffer_bounds in Hbounds. solve_addr.
  Qed.
End HTS_World_Buffer.

Section HTS_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
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

  (** Share [b] with the first adversary call: make [b], fresh in the
      revoked world, a [Permanent] cell holding [0], and transport what the
      switcher needs to [hts_Wshare ι b]. *)
  Lemma hts_world_share_buffer E ι b :
    LHeap b ι ∉ dom (std (revoke W_init_C)) ->
    hts_buffer_bounds b ->
    disjoint_from_heap csp_b csp_e ->
    revoked_addresses (revoke W_init_C) (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) ->
    alloc_obj ι b (b ^+ 1) -∗
    b ↦ₕ[ι] WInt 0 -∗
    world_interp (revoke W_init_C) C -∗
    StackRevokedResources W_init_C C (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1))
    ={E}=∗
    world_interp (hts_Wshare W_init_C ι b) C ∗
    rel C (LHeap b ι) RW interp_in_memC ∗
    interp (hts_Wshare W_init_C ι b) C (hts_buffer b @@ ι) ∗
    StackRevokedResources (hts_Wshare W_init_C ι b) C
      (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) ∗
    ⌜revoked_addresses (hts_Wshare W_init_C ι b)
      (stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1))⌝.
  Proof.
    iIntros (Hb_fresh Hbounds Hstk_heap Hstack_revoked)
      "#Hobj Hb Hworld Hstack_revoked".
    set (stk_frame_addrs := stk_free csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)).
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    iDestruct (init_PermRes (revoke W_init_C) C (LHeap b ι) RW interp_in_memC (WInt 0)
      with "[] Hb []") as "Hbuf_perm".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm (revoke W_init_C) C (LHeap b ι) (WInt 0) RW interp_in_memC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
    { exact Hb_fresh. }
    iAssert (interp (hts_Wshare W_init_C ι b) C (hts_buffer b @@ ι)) as "#Hinterp_buf".
    { iEval (rewrite /hts_buffer interp_unfold /=).
      iSplitL.
      { rewrite /interp_cap_body.
        rewrite (finz_seq_between_cons b); last solve_addr.
        rewrite (finz_seq_between_empty _ (b ^+ 1)); last solve_addr.
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
      iSplit.
      { iPureIntro. split.
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
      iIntros (_). iSplit; first (iPureIntro; done).
      iExists b, (b ^+ 1). iFrame "Hobj". iPureIntro. solve_addr. }
    assert (related_sts_priv_world W_init_C (hts_Wshare W_init_C ι b))
      as Hrelated_init_share.
    { eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - apply related_sts_pub_world_fresh. exact Hb_fresh. }
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

  (** After the first adversary call: main still holds the free right of
      [ι], so [ι] is still live, and [b] is [Permanent] in
      [revoke Wret]. Open its world entry to get its memory back. *)
  Lemma hts_world_reopen_live E ι b Wret :
    hts_buffer_bounds b ->
    related_sts_pub_world
      (std_update_multiple (hts_Wshare W_init_C ι b)
        (callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) Temporary) Wret ->
    rel C (LHeap b ι) RW interp_in_memC -∗
    free_right ι -∗
    world_interp (revoke Wret) C
    ={E}=∗
    ∃ v_b : LWord,
      ⌜std (revoke Wret) !! LHeap b ι = Some Permanent⌝ ∗
      world_interp_open (revoke Wret) C [LHeap b ι] ∗
      sts_state_std C (LHeap b ι) Permanent ∗
      free_right ι ∗
      b ↦ₕ[ι] v_b.
  Proof.
    iIntros (Hbounds Hrelated_share_ret) "#Hrel_b Hright Hworld".
    assert (LHeap b ι ∉
              LNonHeap <$> callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e ^+ -1))
      as Hb_not_callstk.
    { intros (a & Heq & _)%list_elem_of_fmap. discriminate. }
    assert (std (std_update_multiple (hts_Wshare W_init_C ι b)
      (callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) Temporary) !! LHeap b ι =
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
    { by right. }
    { exact Hstd_rev. }
    iDestruct (heap_key_resource_live with "Hright Hres_b") as "[Hres_b Hright]".
    iDestruct "Hres_b" as (v_b) "Hres_b".
    iDestruct "Hres_b" as "(>%Hp_nonO & >Hb_phys & _)".
    iModIntro. iExists v_b. by iFrame.
  Qed.

End HTS_World.

Section HTS_World_Free.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
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
    apply revoke_related_sts_priv_world.
  Qed.

  (** After the call to free: [ι ⊒ AQuar] closes the world entry of [b]
      as a tombstone, with no resources. *)
  Lemma hts_world_quarantine E ι b Wret :
    hts_buffer_bounds b ->
    std (revoke Wret) !! LHeap b ι = Some Permanent ->
    rel C (LHeap b ι) RW interp_in_memC -∗
    sts_state_std C (LHeap b ι) Permanent -∗
    ι ⊒ AQuar -∗
    world_interp_open (revoke Wret) C [LHeap b ι]
    ={E}=∗
    world_interp (hts_Wfree Wret ι) C.
  Proof.
    iIntros (Hbounds Hstd_rev) "#Hrel_b Hstate_b #Hquar Hworld_open".
    iModIntro.
    iApply (close_world_interp_quarantined_heap (hts_Wfree Wret ι) C b ι RW
      interp_in_memC Permanent with "Hquar Hworld_open Hrel_b Hstate_b").
  Qed.
End HTS_World_Free.
