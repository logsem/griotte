From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import droe_spec_states.

(** * Logical steps of the proof of [droe_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [droe_spec_<segment>_blocks_<n>] in the proof of
    [droe_spec]. *)

Section DROE_World.
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

  (** ** Sharing the data with the adversary

      The world in which the call happens: the revoked world. [cgp_b] and
      [cgp_b + 1] become Global regions, with a read-only safety predicate
      that fixes their content. *)
  Definition droe_Wshare W (cgp_b : Addr) : WORLD := revoke W.

  (** The safety predicate of [cgp_b]: it always contains [42]. *)
  Definition droe_b_pred : CmptName * LWord → iProp Σ :=
    safeGC (interp_in_mem_dro_eq (WInt 42)).

  Lemma droe_world_share W0 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable) :
    let W3 := droe_Wshare W0 cgp_b in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    LNonHeap cgp_b ∉ dom (std W0) ->
    LNonHeap (cgp_b ^+ 1) ∉ dom (std W0) ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    cgp_b ↦ₐ WInt 42 -∗
    (cgp_b ^+ 1) ↦ₐ Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b
    ={⊤}=∗
    world_interp W3 C ∗
    (LNonHeap cgp_b) ↪ᵍ[C]{RO_DRO} droe_b_pred ∗
    interp W3 C (Cap RO_DRO Global (cgp_b ^+ 1) (cgp_b ^+ 2) (cgp_b ^+ 1)) ∗
    interp W3 C (WSealed ot_switcher C_f) ∗
    StackRevokedResources W3 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W3 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W3'; subst W3'; rewrite /droe_Wshare.
    iIntros (Hcgp_contiguous Hcgp_shadow Hcgp_range Hcgp_b Hcgp_a Hstack_revoked)
      "#Hseal_switcher Hworld_interp_C #Hstack_revoked_W0 #Hinterp_W0_C_f Hcgp_b Hcgp_a".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].
    iDestruct (init_PermRes C (LNonHeap cgp_b) RO_DRO droe_b_pred
                with "[$Hcgp_b] []") as "PermRes_cgp_b"; first done.
    { cbn.
      iSplitR; [done |].
      iEval (rewrite /interp_in_mem_pre /=).
      iApply interp_int.
    }
    iMod (world_interp_extend_perm_nonheap with "Hworld_interp_C PermRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.

    (* A Global capability to Global regions is valid in any world *)
    iAssert (∀ W, interp W C (Cap RO_DRO Global cgp_b (cgp_b ^+ 1) cgp_b))%I
      as "#Hinterp_cgp_b".
    { iIntros (W).
      iEval (cbn). iEval (rewrite interp_unfold). iEval (cbn).
      iSplit; last (
        pose proof (switcher_disjoint_subseg cgp_b cgp_e cgp_b (cgp_b ^+ 1)
          ltac:(solve_addr) ltac:(solve_addr) (conj Hcgp_shadow Hcgp_heap))
          as [Hsub_shadow Hsub_heap];
        iSplit; [iPureIntro; exact Hsub_shadow|iApply heap_cap_ok_disjoint; exact Hsub_heap]).
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)); last solve_addr.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RO_DRO, (interp_in_mem_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z π) "[%Heq H]"; simplify_eq.
        rewrite /interp_in_mem_dro_eq /=.
        iSplitR; [done |].
        iEval (rewrite /interp_in_mem_pre /=).
        iApply interp_int.
      }
      iSplit.
      { iNext. iIntros "!>" (t') "_".
        iIntros "!>" (W1' w') "[-> _]".
        rewrite /interp_in_mem_pre /=.
        iApply interp_int.
      }
      done.
    }

    assert (is_heap_address (cgp_b ^+ 1) = false) as Hcgp1_nonheap.
    { apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hcgp_heap.
      eapply (Hcgp_heap (cgp_b ^+ 1)); apply elem_of_finz_seq_between;
        [solve_addr+Hcgp_contiguous|exact Hheap]. }

    iDestruct (init_PermRes C (LNonHeap (cgp_b ^+1)) RO_DRO
                 (safeGC (interp_in_mem_dro_eq (Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b)))
                with "[$Hcgp_a] []") as "PermRes_cgp_a"; first done.
    { cbn. iSplit; [done |].
      iApply interp_to_in_mem.
      iApply "Hinterp_cgp_b". }
    iMod (world_interp_extend_perm_nonheap with "Hworld_interp_C PermRes_cgp_a")
      as "(Hworld_interp_C & #Hrel_cgp_a)"; auto.

    iAssert (interp (revoke W0) C (Cap RO_DRO Global (cgp_b ^+ 1) (cgp_b ^+ 2) (cgp_b ^+ 1)))
      as "#Hinterp_W3_C_a".
    { iEval (cbn). iEval (rewrite interp_unfold). iEval (cbn).
      iSplit; last (
        pose proof (switcher_disjoint_subseg cgp_b cgp_e (cgp_b ^+ 1) (cgp_b ^+ 2)
          ltac:(solve_addr) ltac:(solve_addr) (conj Hcgp_shadow Hcgp_heap))
          as [Hsub_shadow Hsub_heap];
        iSplit; [iPureIntro; exact Hsub_shadow|iApply heap_cap_ok_disjoint; exact Hsub_heap]).
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)); last solve_addr.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RO_DRO, (interp_in_mem_dro_eq _).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit.
      { iIntros "!>" (W1').
        iIntros "!>" (W1'' z π) "[% H]"; done.
      }
      iSplit.
      { iNext. iIntros "!>" (t') "_".
        iIntros "!>" (W1' w') "[-> _]".
        rewrite /interp_in_mem_pre /=.
        rewrite -(interp_global_thread_world_free th t' W1' W1' C); last done.
        iApply "Hinterp_cgp_b".
      }
      done.
    }

    iModIntro.
    iFrame "Hworld_interp_C Hrel_cgp_b Hinterp_W3_C_a".
    iSplit.
    { iApply (interp_monotone_sd with "[] Hseal_switcher Hinterp_W0_C_f").
      iPureIntro. apply revoke_related_sts_priv_world. }
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W0");
                   apply revoke_related_sts_priv_world).
    done.
  Qed.

  (** ** Return from the call

      The adversary returned a public future [W4] of [W3]. Since [cgp_b] is
      a Global region, opening the world gives back [cgp_b], which still
      contains [42]. *)
  Lemma droe_world_return W0 W4 C (cgp_b cgp_e csp_b csp_e : Addr) :
    let W3 := droe_Wshare W0 cgp_b in
    let stk := finz.seq_between csp_b csp_e in
    let stk' := callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e) in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    is_heap_address cgp_b = false ->
    revoked_addresses W3 stk ->
    related_sts_pub_world (std_update_multiple W3 stk' Temporary) W4 ->
    world_interp (revoke W4) C -∗
    (LNonHeap cgp_b) ↪ᵍ[C]{RO_DRO} droe_b_pred -∗
    ◇ cgp_b ↦ₐ WInt 42.
  Proof.
    intros W3 stk stk'.
    iIntros (Hcgp_contiguous Hcsp_bounds Hcgp_nonheap Hstack_revoked_W3 Hrelated_pub)
      "Hworld_interp #Hrel_cgp_b".
    rewrite open_world_interp_empty.
    iDestruct (open_world_interp_permanent_nonheap with "Hworld_interp Hrel_cgp_b")
      as "(_ & [%w (_ & >Hcgp_b & Hw)])"; auto.
    { set_solver+. }
    { apply revoke_conditions_sat. }
    rewrite /droe_b_pred /=.
    iDestruct "Hw" as "[>-> _]".
    by iModIntro.
  Qed.

End DROE_World.
