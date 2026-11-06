From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel interp_weakening proofmode.
From griotte Require Import world_ghost_theory.
From griotte Require Import cmdc_compiled_spec_states.

(** * Logical steps of the proof of [cmdc_compiled_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [cmdc_compiled_spec_<segment>_blocks_<n>] in the proof
    of [cmdc_compiled_spec]. *)

Section CMDC_Compiled_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** The frame of [run]

      The cursor of [run], below its frame, is in the stack, and the spill
      of the switcher fits below it. *)
  Lemma cmdc_compiled_frame_a_bounds (csp_b csp_e : Addr) :
    let a_f := cmdc_compiled_frame_a csp_b csp_e in
    (csp_b + cmdc_compiled_main_run_min_stack + StackEntry_reserved_space <= csp_e)%Z ->
    (a_f + Z.of_nat cmdc_compiled_main_run_frame_size)%a = Some (stk_start_a csp_b csp_e) ∧
    (csp_b <= a_f)%a ∧
    (stk_start_a csp_b csp_e <= csp_e)%a ∧
    stk_spill_fits csp_b csp_e a_f.
  Proof.
    intros a_f Hstk_min; subst a_f.
    rewrite /cmdc_compiled_frame_a /cmdc_compiled_main_run_min_stack
      /cmdc_compiled_main_run_frame_size in Hstk_min |- *.
    stk_unfold; split_and!; solve_addr+Hstk_min.
  Qed.

  (** The stack $[b, e)$ of the thread, cut at the cursor of [run]: the free
      part below the frame, which the calls hand to the switcher, the 3
      words of the frame, and the space reserved at the top of the
      stack. *)
  Lemma cmdc_compiled_stack_frame (csp_b csp_e : Addr) (stk_mem : list LWord) :
    let a_f := cmdc_compiled_frame_a csp_b csp_e in
    (csp_b + cmdc_compiled_main_run_min_stack + StackEntry_reserved_space <= csp_e)%Z ->
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]] -∗
    ∃ stk_free wf0 wf1 wf2 stk_res,
      [[ stk_free_b csp_b a_f , stk_free_e csp_e a_f ]] ↦ₐ [[ stk_free ]] ∗
      a_f ↦ₐ wf0 ∗
      (a_f ^+ 1) ↦ₐ wf1 ∗
      (a_f ^+ 2) ↦ₐ wf2 ∗
      [[ stk_start_a csp_b csp_e , csp_e ]] ↦ₐ [[ stk_res ]].
  Proof.
    intros a_f.
    iIntros (Hstk_min) "Hstk".
    destruct (cmdc_compiled_frame_a_bounds csp_b csp_e Hstk_min)
      as (Ha_f & Hcsp_b & Hstk_start & _).
    rewrite /cmdc_compiled_main_run_frame_size in Ha_f.
    fold a_f in Ha_f; fold a_f in Hcsp_b.
    clearbody a_f.
    iDestruct (stk_cursor_region_split csp_b csp_e a_f with "Hstk")
      as (stk_free stk_rest) "[Hstk_free Hstk_rest]"; [solve_addr | solve_addr |].
    iDestruct (big_sepL2_length with "Hstk_rest") as %Hlen.
    rewrite finz_seq_between_length /finz.dist in Hlen.
    destruct stk_rest as [|wf0 [|wf1 [|wf2 stk_res] ] ]; cbn in Hlen; try solve_addr.
    iDestruct (region_pointsto_cons a_f (a_f ^+ 1) with "Hstk_rest") as "[Hf0 Hstk_rest]";
      [ solve_addr | solve_addr | ].
    iDestruct (region_pointsto_cons (a_f ^+ 1) (a_f ^+ 2) with "Hstk_rest")
      as "[Hf1 Hstk_rest]"; [ solve_addr | solve_addr | ].
    iDestruct (region_pointsto_cons (a_f ^+ 2) (stk_start_a csp_b csp_e) with "Hstk_rest")
      as "[Hf2 Hstk_rest]"; [ solve_addr | solve_addr | ].
    iExists _, _, _, _, _. iFrame.
  Qed.

  (** ** Sharing an address with a callee

      The shared address [a] becomes a Permanent region, which leaves the local
      world unchanged. *)

  (** Relinquish [a] into the world of the callee, so that the capability
      [(RW, Global, a, a_e, a)] is safe to share. *)
  Lemma cmdc_compiled_world_share W C (a a_e : Addr) (target : Sealable) :
    (a + 1)%a = Some a_e ->
    is_mmio_address a = false ->
    is_heap_address a = false ->
    world_interp W C -∗
    interp W C (WSealed ot_switcher target) -∗
    a ↦ₐ WInt 0
    ={⊤}=∗
    world_interp W C ∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) ∗
    interp W C (Cap RW Global a a_e a) ∗
    interp W C (WSealed ot_switcher target).
  Proof.
    iIntros (Ha_e Ha_mmio Ha_heap) "Hworld #Htarget Ha".

    (* Relinquish [a] into the world, as a Permanent region *)
    iDestruct (init_PermRes C (LNonHeap a) RW (safeGC interp_nonlocal) with "[$Ha] []") as "Ha".
    { done. }
    { iApply interp_nonlocal_int. }
    iMod (world_interp_extend_perm with "Hworld Ha") as "(Hworld & #Hrel_a)"; auto.
    iModIntro.
    iFrame "Hworld Hrel_a Htarget".

    (* The capability pointing to [a] is safe to share *)
    iEval (rewrite interp_unfold). iEval (cbn). iLeft.
    iSplitL; last first.
    { iSplit.
      - iPureIntro. split; [|split].
        + pose proof (not_mmio_not_shadow _ Ha_mmio) as Ha_shadow.
          rewrite /disjoint_from_shadow elem_of_disjoint.
          intros a' Ha' Hr; apply elem_of_finz_seq_between in Ha', Hr.
          assert (a' = a) as -> by solve_addr+Ha' Ha_e.
          apply withinBounds_true_iff in Hr.
          change (is_shadow_address a = true) in Hr; congruence.
        + pose proof (not_mmio_not_revoker _ Ha_mmio) as Ha_rev.
          intros Ha'; apply elem_of_finz_seq_between in Ha'.
          assert (revoker_addr = a) as Heq by solve_addr+Ha' Ha_e.
          rewrite -Heq /is_revoker_address bool_decide_eq_false in Ha_rev.
          by apply Ha_rev.
        + pose proof (not_mmio_not_time_device _ Ha_mmio) as Ha_td.
          apply orb_false_iff in Ha_td as [Ha_mtime Ha_mtimecmp].
          split; intros Ha'; apply elem_of_finz_seq_between in Ha'.
          * assert (mtime_addr = a) as Heq by solve_addr+Ha' Ha_e.
            rewrite -Heq bool_decide_eq_false in Ha_mtime.
            by apply Ha_mtime.
          * assert (mtimecmp_addr = a) as Heq by solve_addr+Ha' Ha_e.
            rewrite -Heq bool_decide_eq_false in Ha_mtimecmp.
            by apply Ha_mtimecmp.
      - iApply heap_cap_ok_disjoint.
        rewrite /disjoint_from_heap elem_of_disjoint.
        intros a' Ha' Hr; apply elem_of_finz_seq_between in Ha', Hr.
        assert (a' = a) as -> by solve_addr+Ha' Ha_e.
        apply withinBounds_true_iff in Hr.
        change (is_heap_address a = true) in Hr; congruence. }
    rewrite /interp_cap_body.
    rewrite (finz_seq_between_cons a); last solve_addr.
    rewrite (finz_seq_between_empty (a ^+ 1)); last solve_addr+Ha_e.
    iApply big_sepL_singleton.
    rewrite addr_key_None.
    iExists RW, interp_nonlocal.
    iEval (cbn).
    iSplit; first done.
    iSplit; first (iPureIntro; apply persistent_cond_interp_nonlocal).
    iSplit; first iFrame "Hrel_a".
    iSplit; first (iNext; iApply zcond_interp_nonlocal).
    iSplit; first (iNext; by iApply rcond_g_interp_nonlocal).
    iNext; iApply wcond_nwl_interp_nonlocal.
  Qed.

  (** ** Return from a call

      The world [Wret] at the return of a call, revoked: the shared address
      [a] is a Permanent region, which gives back a points-to of [a]. *)
  Lemma cmdc_compiled_world_return Wret C (a : Addr) :
    is_heap_address a = false ->
    world_interp (revoke Wret) C -∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) -∗
    ◇ ∃ v, a ↦ₐ v.
  Proof.
    iIntros (Ha_heap) "Hworld #Hrel_a".
    assert (std (revoke Wret) !! LNonHeap a ≠ Some Temporary) as Ha_perm.
    { apply revoke_conditions_sat. }
    rewrite (open_world_interp_empty _ C).
    iDestruct (open_world_interp_permanent with "Hworld Hrel_a")
      as "(_ & Ha)"; auto.
    { set_solver+. }
    iDestruct "Ha" as (v) "Ha".
    iDestruct (PermRes_acc with "Ha") as "[(Ha & _) _]".
    iEval (rewrite key_pointsto_nonheap) in "Ha".
    iModIntro. by iExists v.
  Qed.

End CMDC_Compiled_World.
