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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .

  (* TODO: move to logrel/logrel.v, next to interp_global_world_free *)
  (** A word sealed with a Global-kind otype is valid in every world: the
      predicate of the otype does not depend on the world. *)
  Lemma interp_sealed_global_kind_world_free W W' C o P sb π :
    o ↪ₒ{SealGlobal} P -∗
    interp W C (WSealed o sb @@? π) -∗
    interp W' C (WSealed o sb @@? π).
  Proof.
    iIntros "#Hs #Hinterp".
    destruct (get_tag_sealable sb) eqn:Htag;
      last (rewrite !interp_untagged_eq //=; auto).
    rewrite !interp_unfold /= Htag /interp_sb.
    iDestruct "Hinterp" as "[(%κ & %P' & #Hs' & #Hok & #HP) $]".
    iDestruct (seal_pred_agree with "Hs Hs'") as "[<- _]".
    iExists SealGlobal, P'. iFrame "Hs' Hok".
    iDestruct "Hok" as "[_ #Hc]". iNext. by iApply ("Hc" $! th th W W').
  Qed.

  (** The adversary entry is sealed with the switcher's otype, whose
      predicate does not depend on the world, so its interpretation does not
      depend on the world. *)
  Lemma hts_interp_adv_world (C : CmptName) (C_f : Sealable) W W' :
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    interp W C (WSealed ot_switcher C_f) -∗
    interp W' C (WSealed ot_switcher C_f).
  Proof.
    iIntros (_) "#Hseal_switcher #Hadv".
    iApply (interp_sealed_global_kind_world_free W W' C ot_switcher _ C_f None
             with "Hseal_switcher Hadv").
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout}
  .
  Context (C : CmptName).
  Context (csp_b csp_e : Addr).
  Context (C_f : Sealable) (W_init_C : WORLD).


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

  (** Share [b] with the first adversary call: make [b] a Global region
      holding [0]; the world of the call is the revoked world. *)
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
    (LHeap b ι) ↪ᵍ[C]{RW} interp_in_mem_gC ∗
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
    iDestruct (init_PermRes C (LHeap b ι) RW interp_in_mem_gC (WInt 0)
      with "Hb []") as "Hbuf_perm".
    { done. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm (revoke W_init_C) C (LHeap b ι) (WInt 0) RW interp_in_mem_gC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
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
        iApply wcond_interp_in_mem. }
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
      as Hrelated_init_share by apply revoke_related_sts_priv_world.
    iDestruct (StackRevokedResources_mono_priv W_init_C (hts_Wshare W_init_C ι b) C
      stk_frame_addrs Hrelated_init_share with "Hstack_revoked")
      as "Hstack_revoked_share".
    iModIntro. iFrame "∗#".
    iPureIntro. exact Hstack_revoked.
  Qed.

  (** After the first adversary call: main still holds the free right of
      [ι], so [ι] is still live, and [b] is a Global region. Open its world
      entry to get its memory back. *)
  Lemma hts_world_reopen_live E ι b Wret :
    hts_buffer_bounds b ->
    related_sts_pub_world
      (std_update_multiple (hts_Wshare W_init_C ι b)
        (callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e ^+ -1)) Temporary) Wret ->
    (LHeap b ι) ↪ᵍ[C]{RW} interp_in_mem_gC -∗
    free_right ι -∗
    world_interp (revoke Wret) C
    ={E}=∗
    ∃ v_b : LWord,
      world_interp_open (revoke Wret) C [LHeap b ι] ∗
      free_right ι ∗
      b ↦ₕ[ι] v_b.
  Proof.
    iIntros (Hbounds Hrelated_share_ret) "#Hrel_b Hright Hworld".
    rewrite open_world_interp_empty.
    iDestruct (open_world_interp_permanent (revoke Wret) C [] (LHeap b ι) RW
      interp_in_mem_gC with "Hworld Hrel_b")
      as "(Hworld_open & Hres_b)".
    { set_solver+. }
    { apply revoke_conditions_sat. }
    iDestruct (heap_key_resource_live with "Hright Hres_b") as "[Hres_b Hright]".
    iDestruct "Hres_b" as (v_b) "Hres_b".
    iDestruct "Hres_b" as "(>%Hp_nonO & >Hb_phys & _)".
    iModIntro. iExists v_b. by iFrame.
  Qed.

End HTS_World.

Section HTS_World_Free.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
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
    (LHeap b ι) ↪ᵍ[C]{RW} interp_in_mem_gC -∗
    ι ⊒ AQuar -∗
    world_interp_open (revoke Wret) C [LHeap b ι]
    ={E}=∗
    world_interp (hts_Wfree Wret ι) C.
  Proof.
    iIntros (Hbounds) "#Hrel_b #Hquar Hworld_open".
    iModIntro.
    rewrite /hts_Wfree open_world_interp_empty.
    iApply (close_world_interp_next_quarantined_heap_g (revoke Wret) C [] b ι RW
      interp_in_mem_gC with "Hquar Hworld_open Hrel_b").
    { set_solver+. }
    { apply revoke_conditions_sat. }
  Qed.
End HTS_World_Free.
