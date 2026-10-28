From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import cmdc_spec_states.

(** * Logical steps of the proof of [cmdc_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [cmdc_spec_<segment>_blocks_<n>] in the proof of
    [cmdc_spec]. *)

Section CMDC_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing an address with a callee

      The world in which a call happens: the shared address [a] is added to
      the world as a permanent address. *)
  Definition cmdc_Wshare W (a : Addr) : WORLD :=
    <s[a := Permanent ]s> W.

  (** Relinquish [a] into the world of the callee, so that the capability
      [(RW, Global, a, a_e, a)] is safe to share. The stack frame stays
      revoked. *)
  Lemma cmdc_world_share W C (a a_e csp_b csp_e : Addr) (target : Sealable)
    (stk_mem : list LWord) :
    let W' := cmdc_Wshare W a in
    let stk := finz.seq_between csp_b csp_e in
    (a + 1)%a = Some a_e ->
    is_mmio_address a = false ->
    is_heap_address a = false ->
    LNonHeap a ∉ dom (std W) ->
    revoked_addresses W stk ->
    world_interp W C -∗
    StackRevokedResources W C stk -∗
    interp W C (WSealed ot_switcher target) -∗
    a ↦ₐ WInt 0 -∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]]
    ={⊤}=∗
    world_interp W' C ∗
    rel C (LNonHeap a) RW interp_in_memC ∗
    interp W' C (Cap RW Global a a_e a) ∗
    interp W' C (WSealed ot_switcher target) ∗
    StackRevokedResources W' C stk ∗
    ⌜ revoked_addresses W' stk ⌝ ∗
    ⌜ a ∉ stk ⌝ ∗
    [[ csp_b , csp_e ]] ↦ₐ [[ stk_mem ]].
  Proof.
    intros W' stk.
    iIntros (Ha_e Ha_mmio Ha_heap Ha_fresh Hrevoked_stk)
      "Hworld Hstack_revoked #Htarget Ha Hstk".
    iDestruct (big_sepL2_disjoint_pointsto with "[$Hstk $Ha]") as "%Ha_stk".

    (* Relinquish [a] into the world, as a permanent address *)
    iDestruct (init_PermRes W C a RW interp_in_memC with "[] [$Ha] []") as "Ha".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm_nonheap with "Hworld Ha") as "(Hworld & #Hrel_a)"; auto.
    iModIntro.
    assert (related_sts_priv_world W W') as HW_priv_W'.
    { subst W'. by eapply related_sts_priv_world_fresh_Permanent. }
    iFrame "Hworld Hrel_a Hstk".

    (* The capability pointing to [a] is safe to share *)
    iSplit.
    { iEval (rewrite interp_unfold). iEval (cbn).
      iSplitL; last first.
      { iPureIntro. split.
        - split.
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
        - apply heap_cap_valid_disjoint.
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
      iExists RW, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; by apply persistent_cond_interp_in_mem).
      iSplit; first iFrame "Hrel_a".
      iSplit; first (iNext; by iApply zcond_interp_in_mem).
      iSplit; first (iNext; by iApply rcond_interp_in_mem).
      iSplit; first (iNext; by iApply wcond_interp_in_mem).
      subst W'.
      iSplit.
      - iApply (monoReq_interp_in_mem _ _ _ _ Permanent); last done.
        rewrite /std_update. by rewrite lookup_insert_eq.
      - iPureIntro. by rewrite lookup_insert_eq.
    }

    (* The entry point of the callee is still safe to share *)
    iSplit; first (iApply (interp_monotone_sd_same_heap with "[] [$]"); eauto).

    (* The stack is still revoked *)
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); auto).
    iPureIntro; split; last done.
    rewrite /revoked_addresses Forall_forall.
    rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
    intros a' Ha'. subst W'; cbn.
    rewrite lookup_insert_ne; last (intros [= ->]; set_solver+Ha_stk Ha').
    by apply Hrevoked_stk.
  Qed.

  (** ** Return from a call

      The callee returned a public future [Wret] of the world of the call.
      The shared address [a] is still permanent in the revoked world, which
      gives back a points-to of [a]. *)
  Lemma cmdc_world_return W Wret C (a csp_b csp_e : Addr) :
    let stk' := callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e) in
    is_heap_address a = false ->
    a ∉ finz.seq_between csp_b csp_e ->
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    related_sts_pub_world (std_update_multiple (cmdc_Wshare W a) stk' Temporary) Wret ->
    world_interp (revoke Wret) C -∗
    rel C (LNonHeap a) RW interp_in_memC -∗
    ◇ ∃ v, a ↦ₐ v.
  Proof.
    intros stk'.
    iIntros (Ha_heap Ha_stk Hcsp_bounds Hrelated_pub) "Hworld #Hrel_a".
    assert (a ∉ stk') as Ha_stk'.
    { subst stk'.
      intro Ha_range. apply Ha_stk, elem_of_finz_seq_between.
      exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Ha_range).
    }
    assert (std (revoke Wret) !! LNonHeap a = Some Permanent) as Ha_perm.
    { apply revoke_lookup_Perm.
      eapply region_state_pub_perm; first exact Hrelated_pub.
      rewrite /cmdc_Wshare std_update_multiple_insert_commute; last exact Ha_stk'.
      by rewrite lookup_insert_eq.
    }
    rewrite (open_world_interp_empty _ C).
    iDestruct (open_world_interp_permanent_nonheap with "Hworld Hrel_a")
      as "(_ & _ & Ha)"; auto.
    { set_solver+. }
    iAssert (▷ ∃ v, a ↦ₐ v)%I with "[Ha]" as ">Ha".
    { iNext. iDestruct "Ha" as (v) "Ha".
      iDestruct (PermRes_acc with "Ha") as "[(Ha & _) _]".
      iEval (rewrite key_pointsto_nonheap) in "Ha".
      by iExists v. }
    by iModIntro.
  Qed.

End CMDC_World.
