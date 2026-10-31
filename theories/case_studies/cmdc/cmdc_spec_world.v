From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack world_interp_allocation_compartments.
From griotte Require Import cmdc_spec_states.

(** * Logical steps of the proof of [cmdc_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [cmdc_spec_<segment>_blocks_<n>] in the proof of
    [cmdc_spec]. *)

Section CMDC_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing an address with a callee

      The shared address [a] becomes a Global region, which leaves the local
      world unchanged. *)

  (** Relinquish [a] into the world of the callee, so that the capability
      [(RW, Global, a, a_e, a)] is safe to share. The stack frame stays
      revoked. *)
  Lemma cmdc_world_share W C (a a_e csp_b csp_e : Addr) (target : Sealable)
    (stk_mem : list LWord) :
    let stk := finz.seq_between csp_b csp_e in
    (a + 1)%a = Some a_e ->
    is_mmio_address a = false ->
    is_heap_address a = false ->
    revoked_addresses W stk ->
    world_interp W C -∗
    StackRevokedResources W C stk -∗
    interp W C (WSealed ot_switcher target) -∗
    a ↦ₐ WInt 0 -∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
    ={⊤}=∗
    world_interp W C ∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) ∗
    interp W C (Cap RW Global a a_e a) ∗
    interp W C (WSealed ot_switcher target) ∗
    StackRevokedResources W C stk ∗
    ⌜ revoked_addresses W stk ⌝ ∗
    ⌜ a ∉ stk ⌝ ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]].
  Proof.
    intros stk.
    iIntros (Ha_e Ha_mmio Ha_heap Hrevoked_stk)
      "Hworld Hstack_revoked #Htarget Ha Hstk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Ha]") as "%Ha_stk".

    (* Relinquish [a] into the world, as a Global region *)
    iDestruct (init_PermRes C (LNonHeap a) RW (safeGC interp_nonlocal) with "[$Ha] []") as "Ha".
    { done. }
    { iApply interp_nonlocal_int. }
    iMod (world_interp_extend_perm with "Hworld Ha") as "(Hworld & #Hrel_a)"; auto.
    iModIntro.
    iFrame "Hworld Hrel_a Hstk Htarget Hstack_revoked".

    (* The capability pointing to [a] is safe to share *)
    iSplit.
    { iEval (rewrite interp_unfold). iEval (cbn).
      iSplitL; last first.
      { iSplit.
        - iPureIntro. split.
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
    }
    done.
  Qed.

  (** ** Return from a call

      The callee returned a public future [Wret] of the world of the call.
      The shared address [a] is a Global region, which gives back a
      points-to of [a]. *)
  Lemma cmdc_world_return W Wret C (a csp_b csp_e : Addr) :
    let stk' := callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e) in
    is_heap_address a = false ->
    a ∉ finz.seq_between csp_b csp_e ->
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    related_sts_pub_world (std_update_multiple W stk' Temporary) Wret ->
    world_interp (revoke Wret) C -∗
    (LNonHeap a) ↪ᵖ[C]{RW} (safeGC interp_nonlocal) -∗
    ◇ ∃ v, a ↦ₐ v.
  Proof.
    intros stk'.
    iIntros (Ha_heap Ha_stk Hcsp_bounds Hrelated_pub) "Hworld #Hrel_a".
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

End CMDC_World.
