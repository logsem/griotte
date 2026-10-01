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
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
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
        rewrite /heap_cap_live Hheap in Hvalid |- *.
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

  Lemma hts_buffer_fresh b :
    hts_buffer_bounds b -> heap_fresh (∅ : Heap) b (b ^+ 1)%a.
  Proof.
    intros Hbounds.
    split; first apply lookup_empty.
    split; first exact (proj1 (proj2 Hbounds)).
    intros c o a Hc. rewrite lookup_empty in Hc. discriminate.
  Qed.

  Lemma hts_buffer_allocate_lookup b :
    hts_buffer_bounds b ->
    heap_lookup_addr (heap_allocate ∅ b (b ^+ 1)%a) b =
      Some (b, MkAllocObject b (b ^+ 1)%a AllocObjectLive).
  Proof.
    intros Hbounds.
    pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty
      (hts_buffer_fresh b Hbounds)) as Hwf_buf.
    rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
      b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
    - reflexivity.
    - rewrite /heap_allocate lookup_insert.
      case_decide; [reflexivity|congruence].
    - unfold alloc_object_contains; cbn.
      split; [clear -Hbounds; rewrite /hts_buffer_bounds in Hbounds; solve_addr
             |exact (proj1 (proj2 Hbounds))].
  Qed.
End HTS_World_Buffer.

Section HTS_World.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .
  Context (C : CmptName).
  Context (csp_b csp_e : Addr).
  Context (C_f : Sealable) (W_init_C : WORLD).





  Lemma hts_Wshare_heap_lookup b :
    hts_buffer_bounds b ->
    heap_lookup_addr (heap_std (hts_Wshare W_init_C b)) b =
      Some (b, MkAllocObject b (b ^+ 1)%a AllocObjectLive).
  Proof.
    intros Hbounds. rewrite /hts_Wshare /heap_std_update /=.
    by apply hts_buffer_allocate_lookup.
  Qed.

  Lemma hts_Wshare_std b :
    std (hts_Wshare W_init_C b) !! b = Some Permanent.
  Proof.
    rewrite /hts_Wshare lookup_insert.
    case_decide; [reflexivity|congruence].
  Qed.

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

  (** Share [b] with the first adversary call: allocate it in the revoked
      world as a [Permanent] cell holding [0], and transport what the
      switcher needs to [hts_Wshare b]. *)
  Lemma hts_world_share_buffer E b :
    heap_std W_init_C = ∅ ->
    hts_buffer_bounds b ->
    disjoint_from_heap csp_b csp_e ->
    revoked_addresses (revoke W_init_C) (finz.seq_between (csp_b ^+ 1)%a csp_e) ->
    allocator_allocation b (b ^+ 1)%a (0%Z, 0%Z) -∗
    b ↦ₐ WInt 0 -∗
    world_interp (revoke W_init_C) C -∗
    StackRevokedResources W_init_C C (finz.seq_between (csp_b ^+ 1)%a csp_e)
    ={E}=∗
    world_interp (hts_Wshare W_init_C b) C ∗
    rel C b RW interp_in_memC ∗
    interp (hts_Wshare W_init_C b) C (hts_buffer b) ∗
    StackRevokedResources (hts_Wshare W_init_C b) C
      (finz.seq_between (csp_b ^+ 1)%a csp_e) ∗
    ⌜revoked_addresses (hts_Wshare W_init_C b)
      (finz.seq_between (csp_b ^+ 1)%a csp_e)⌝.
  Proof.
    iIntros (Hheap_empty Hbounds Hstk_heap Hstack_revoked)
      "#Hallocation Hb Hworld Hstack_revoked".
    set (stk_frame_addrs := finz.seq_between (csp_b ^+ 1)%a csp_e).
    pose proof Hbounds as Hbnd; rewrite /hts_buffer_bounds in Hbnd.
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    pose proof (hts_buffer_fresh b Hbounds) as Hfresh_buf.
    assert (heap_std (revoke W_init_C) = ∅) as Hheap_revoke.
    { rewrite revoke_heap. exact Hheap_empty. }
    iDestruct (hts_world_empty_heap_fresh (revoke W_init_C) C b
      Hb_heap Hheap_revoke with "Hworld") as %Hb_fresh.
    iMod (hts_world_heap_allocate_empty (revoke W_init_C) C b (b ^+ 1)%a
      (0%Z, 0%Z) with "Hallocation Hworld") as "Hworld".
    { exact Hheap_revoke. }
    { exact (proj1 (proj2 Hbounds)). }
    set (Wbuf := heap_std_update (revoke W_init_C)
      (heap_allocate ∅ b (b ^+ 1)%a)).
    iDestruct (init_PermRes Wbuf C b RW interp_in_memC (WInt 0)
      with "[] Hb []") as "Hbuf_perm".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm Wbuf C b (WInt 0) RW interp_in_memC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
    { rewrite /heap_addr_live /heap_addr_status Hb_heap /Wbuf
        /heap_std_update /= hts_buffer_allocate_lookup //. }
    { subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }
    iAssert (interp (hts_Wshare W_init_C b) C (hts_buffer b)) as "#Hinterp_buf".
    { iEval (rewrite /hts_buffer fixpoint_interp1_eq /=).
      iSplitL.
      { rewrite (finz_seq_between_cons b); last solve_addr.
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
      { rewrite /disjoint_from_shadow elem_of_disjoint.
        intros a Ha Hsh.
        pose proof heap_shadow_disjoint as Hdisj.
        rewrite elem_of_disjoint in Hdisj.
        eapply Hdisj; last exact Hsh.
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Ha.
        rewrite /hts_buffer_bounds in Hbounds. solve_addr. }
      intros _. rewrite /heap_cap_live Hb_heap hts_Wshare_heap_lookup //. }
    assert (related_sts_priv_world W_init_C (hts_Wshare W_init_C b))
      as Hrelated_init_share.
    { eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - eapply related_sts_pub_trans_world.
        + apply related_sts_pub_world_heap_update.
          rewrite revoke_heap Hheap_empty. apply heap_allocate_future.
          exact Hfresh_buf.
        + apply related_sts_pub_world_fresh.
          rewrite /heap_std_update /=. exact Hb_fresh. }
    iDestruct (StackRevokedResources_mono_priv W_init_C (hts_Wshare W_init_C b) C
      stk_frame_addrs Hrelated_init_share with "Hstack_revoked")
      as "Hstack_revoked_share".
    iModIntro. iFrame "∗#".
    iPureIntro.
    rewrite /revoked_addresses Forall_forall. intros a Ha.
    rewrite /hts_Wshare lookup_insert_ne.
    - cbn. rewrite /revoked_addresses Forall_forall in Hstack_revoked.
      apply Hstack_revoked. exact Ha.
    - intros Heq. apply (hts_buffer_not_stack b Hbounds Hstk_heap).
      apply elem_of_finz_seq_between.
      apply elem_of_finz_seq_between in Ha. rewrite ?Heq. solve_addr.
  Qed.

  (** After the first adversary call: the reload of the saved buffer kept
      its tag, so [b] is still live, and [Permanent] in [revoke Wret]. Open
      its world entry to get its memory back. *)
  Lemma hts_world_reopen_live E b Wret :
    hts_buffer_bounds b ->
    disjoint_from_heap csp_b csp_e ->
    related_sts_pub_world
      (std_update_multiple (hts_Wshare W_init_C b)
        (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) Wret ->
    filter_heap (revoke Wret) (hts_buffer b) = hts_buffer b ->
    rel C b RW interp_in_memC -∗
    world_interp (revoke Wret) C
    ={E}=∗
    ∃ v_b : Word,
      ⌜heap_wf (heap_std (revoke Wret))⌝ ∗
      ⌜heap_std (revoke Wret) !! b =
        Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive)⌝ ∗
      ⌜std (revoke Wret) !! b = Some Permanent⌝ ∗
      world_interp_open (revoke Wret) C [b] ∗
      sts_state_std C b Permanent ∗
      b ↦ₐ v_b.
  Proof.
    iIntros (Hbounds Hstk_heap Hrelated_share_ret Hfilter) "#Hrel_b Hworld".
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseals)".
    iDestruct (sts_full_world_heap_wf with "Hsts") as %Hwf_ret.
    iAssert (world_interp (revoke Wret) C) with "[Hregion Hsts Hseals]"
      as "Hworld".
    { rewrite world_interp_eq /world_interp_def. iFrame. }
    rewrite revoke_heap in Hwf_ret.
    assert (related_sts_heap_std (heap_std (hts_Wshare W_init_C b)) (heap_std Wret))
      as Hheap_future.
    { rewrite -(std_update_multiple_heap (hts_Wshare W_init_C b)
        (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary).
      exact (proj2 (proj2 (proj2 Hrelated_share_ret))). }
    destruct (heap_lookup_addr_future (heap_std (hts_Wshare W_init_C b)) (heap_std Wret)
      b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive)
      Hwf_ret Hheap_future (hts_Wshare_heap_lookup b Hbounds))
      as (obj_ret & Hlookup_ret & Hobj_future).
    assert (heap_lookup_addr (heap_std (revoke Wret)) b =
      Some (b,obj_ret)) as Hlookup_rev
      by (rewrite revoke_heap; exact Hlookup_ret).
    assert (heap_authority_base (hts_buffer b) = Some b) as Hauth_buf.
    { rewrite /hts_buffer /heap_authority_base.
      case_decide.
      - rewrite /heap_cap_base /memory_cap_base /= Hb_heap. reflexivity.
      - rewrite /hts_buffer_bounds in Hbounds. solve_addr. }
    assert (alloc_object_status obj_ret = AllocObjectLive) as Hlive_ret.
    { destruct (alloc_object_status obj_ret) eqn:Hstatus;
        first reflexivity.
      exfalso.
      pose proof (filter_heap_quarantined (revoke Wret)
        (hts_buffer b) b b obj_ret Hauth_buf Hlookup_rev Hstatus) as Hqu.
      rewrite Hqu in Hfilter.
      apply (f_equal get_tag) in Hfilter.
      rewrite /hts_buffer /= in Hfilter. discriminate. }
    assert (b ∉ finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) as Hb_not_callstk.
    { intros Hin. apply (hts_buffer_not_stack b Hbounds Hstk_heap).
      apply elem_of_finz_seq_between in Hin.
      apply elem_of_finz_seq_between. solve_addr. }
    assert (std (std_update_multiple (hts_Wshare W_init_C b)
      (finz.seq_between ((csp_b ^+ 1) ^+ 4)%a csp_e) Temporary) !! b =
      Some Permanent) as Hstd_source.
    { rewrite std_sta_update_multiple_lookup_same_i;
        [exact (hts_Wshare_std b)|exact Hb_not_callstk]. }
    assert (b ∈ dom (std Wret)) as Hb_dom_ret.
    { apply (proj1 (proj1 Hrelated_share_ret)).
      rewrite elem_of_dom. eexists. exact Hstd_source. }
    rewrite elem_of_dom in Hb_dom_ret.
    destruct Hb_dom_ret as [ρ Hρ].
    pose proof (proj2 (proj1 Hrelated_share_ret)
      b Permanent ρ Hstd_source Hρ) as Hrtc.
    assert (ρ = Permanent) as Hperm
      by (eapply std_rel_pub_rtc_Permanent; eauto).
    subst ρ.
    assert (std (revoke Wret) !! b = Some Permanent) as Hstd_rev.
    { apply revoke_lookup_Perm. exact Hρ. }
    iDestruct (open_world_interp_live_heap (revoke Wret) C b RW
      interp_in_memC Permanent b obj_ret Hb_heap Hlookup_rev Hlive_ret
      (or_intror eq_refl) Hstd_rev with "Hrel_b Hworld")
      as "(Hworld_open & Hstate_b & Hres_b)".
    iDestruct "Hres_b" as (v_b) "Hres_b".
    iDestruct "Hres_b" as "(>%Hp_nonO & >Hb_phys & _)".
    destruct obj_ret as [base_ret end_ret status_ret].
    destruct Hobj_future as (Hbase_ret & Hend_ret & _).
    simpl in Hbase_ret, Hend_ret, Hlive_ret.
    subst base_ret end_ret status_ret.
    pose proof (heap_lookup_addr_sound _ _ _ _ Hlookup_rev) as [Hb_lookup _].
    iModIntro. iExists v_b. iFrame.
    iPureIntro. split; last done.
    rewrite revoke_heap. exact Hwf_ret.
  Qed.

End HTS_World.

Section HTS_World_Free.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .
  Context (C : CmptName).

  Lemma hts_Wfree_related Wret b :
    related_sts_priv_world Wret (hts_Wfree Wret b).
  Proof.
    eapply related_sts_priv_pub_trans_world.
    - apply revoke_related_sts_priv_world.
    - apply related_sts_pub_world_heap_update.
      apply heap_quarantine_future.
  Qed.

  (** After the call to free: quarantine [b] in the world, relinquish its
      reclaim token and close its world entry. *)
  Lemma hts_world_quarantine E b Wret :
    hts_buffer_bounds b ->
    heap_wf (heap_std (revoke Wret)) ->
    heap_std (revoke Wret) !! b =
      Some (MkAllocObject b (b ^+ 1)%a AllocObjectLive) ->
    std (revoke Wret) !! b = Some Permanent ->
    rel C b RW interp_in_memC -∗
    sts_state_std C b Permanent -∗
    allocator_reclaimed b (b ^+ 1)%a -∗
    world_interp_open (revoke Wret) C [b]
    ={E}=∗
    world_interp (hts_Wfree Wret b) C.
  Proof.
    iIntros (Hbounds Hwf_rev Hb_lookup Hstd_rev)
      "#Hrel_b Hstate_b Hreclaimed Hworld_open".
    pose proof (hts_buffer_heap_address b Hbounds) as Hb_heap.
    assert ((b + 1)%a = Some (b ^+ 1)%a) as Hsucc
      by (rewrite /hts_buffer_bounds in Hbounds; solve_addr).
    pose proof (hts_heap_quarantine_single_status
      (heap_std (revoke Wret)) b (b ^+ 1)%a Hwf_rev Hsucc Hb_lookup)
      as Hstatus_other.
    assert (b ∈ dom (std (revoke Wret))) as Hb_dom_rev.
    { rewrite elem_of_dom. eexists. exact Hstd_rev. }
    iDestruct (world_interp_open_heap_provenance with "Hworld_open")
      as "[Hworld_open #Hprovenance]".
    iDestruct (heap_provenance_quarantine with "Hprovenance")
      as "#Hprovenance_free".
    iMod (hts_world_open_heap_transition (revoke Wret) C b
      (heap_quarantine (heap_std (revoke Wret)) b)
      with "Hprovenance_free Hworld_open") as "Hworld_open".
    { apply heap_quarantine_future. }
    { apply heap_quarantine_wf. exact Hwf_rev. }
    { exact Hstatus_other. }
    { exact Hb_dom_rev. }
    assert (heap_lookup_addr (heap_std (hts_Wfree Wret b)) b =
      Some (b, MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined))
      as Hlookup_free.
    { apply heap_lookup_original_base.
      - rewrite /hts_Wfree /heap_std_update /=.
        apply heap_quarantine_wf. exact Hwf_rev.
      - rewrite /hts_Wfree /heap_std_update /=.
        rewrite (heap_quarantine_lookup _ b _ Hb_lookup).
        reflexivity. }
    iEval (rewrite /allocator_reclaimed
      (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) /=)
      in "Hreclaimed".
    iDestruct "Hreclaimed" as "[Hreclaimed _]".
    iModIntro.
    iApply (close_world_interp_quarantined_heap (hts_Wfree Wret b) C b RW
      interp_in_memC Permanent b
      (MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined)
      with "Hworld_open Hrel_b Hstate_b Hreclaimed").
    { exact Hb_heap. }
    { exact Hlookup_free. }
    { reflexivity. }
  Qed.
End HTS_World_Free.
