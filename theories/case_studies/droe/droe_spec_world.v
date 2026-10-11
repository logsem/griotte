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
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing the data with the adversary

      The world in which the call happens: [cgp_b] and [cgp_b + 1] are
      added to the revoked world as permanent addresses, with a read-only
      safety predicate that fixes their content. *)
  Definition droe_Wshare W (cgp_b : Addr) : WORLD :=
    <s[(cgp_b ^+ 1)%a := Permanent ]s> (<s[cgp_b := Permanent ]s> (revoke W)).

  (** The safety predicate of [cgp_b]: it always contains [42]. *)
  Definition droe_b_pred : WORLD * CmptName * LWord → iProp Σ :=
    safeC (interp_in_mem_dro_eq (WInt 42)).

  Lemma droe_world_share W0 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable) :
    let W3 := droe_Wshare W0 cgp_b in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    LNonHeap cgp_b ∉ dom (std W0) ->
    LNonHeap (cgp_b ^+ 1)%a ∉ dom (std W0) ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    cgp_b ↦ₐ WInt 42 -∗
    (cgp_b ^+ 1)%a ↦ₐ WCap true RW Global cgp_b (cgp_b ^+ 1)%a cgp_b
    ={⊤}=∗
    world_interp W3 C ∗
    rel C (LNonHeap cgp_b) RO_DRO droe_b_pred ∗
    interp W3 C (WCap true RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a) ∗
    interp W3 C (WSealed ot_switcher C_f) ∗
    StackRevokedResources W3 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W3 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W3'; subst W3'; rewrite /droe_Wshare.
    iIntros (Hcgp_contiguous Hcgp_shadow Hcgp_range Hcgp_b Hcgp_a Hstack_revoked)
      "Hworld_interp_C #Hstack_revoked_W0 #Hinterp_W0_C_f Hcgp_b Hcgp_a".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].
    set (W1 := revoke W0).
    iDestruct ( init_PermRes W1 C cgp_b RO_DRO (safeC (interp_in_mem_dro_eq (WInt 42)))
                with "[] [$Hcgp_b] []" ) as "PermRes_cgp_b"; auto.
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelated) "H"; cbn.
      iDestruct "H" as "[%Hval Hinterp]".
      iSplitR; [done |].
      iApply (interp_in_mem_monotone_nl W W' C RWL (WInt 42) with "Hinterp");
        [exact Hrelated |].
      cbn. done.
    }
    { cbn.
      iSplitR; [done |].
      iEval (rewrite /interp_in_mem_pre /=).
      iApply interp_int.
    }
    iMod (world_interp_extend_perm_nonheap with "Hworld_interp_C PermRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.
    { by rewrite -revoke_dom_eq. }

    match goal with
    | _ : _ |- context [ world_interp ?W' ] => set (W2 := W')
    end.

    iAssert (interp W2 C (WCap true RO_DRO Global cgp_b (cgp_b ^+ 1)%a cgp_b)) as "#Hinterp_cgp_b".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      iSplit; last (iPureIntro;
        pose proof (switcher_disjoint_subseg cgp_b cgp_e cgp_b (cgp_b ^+ 1)%a
          ltac:(solve_addr) ltac:(solve_addr) (conj Hcgp_shadow Hcgp_heap))
          as [Hsub_shadow Hsub_heap];
        split; [exact Hsub_shadow|apply heap_cap_valid_disjoint; exact Hsub_heap]).
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (cgp_b)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)%a); last solve_addr.
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
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W1.
      iSplit.
      + rewrite /monoReq; cbn; rewrite lookup_insert_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w.(lw)); done.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    assert (is_heap_address (cgp_b ^+ 1)%a = false) as Hcgp1_nonheap.
    { apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hcgp_heap.
      eapply (Hcgp_heap (cgp_b ^+ 1)%a); apply elem_of_finz_seq_between;
        [solve_addr+Hcgp_contiguous|exact Hheap]. }

    iDestruct ( init_PermRes W2 C (cgp_b ^+1)%a RO_DRO  (safeC (interp_in_mem_dro_eq (WCap true RW Global cgp_b (cgp_b ^+ 1)%a cgp_b)))
                with "[] [$Hcgp_a] []" ) as "PermRes_cgp_a"; auto.
    { rewrite /future_priv_mono.
      iIntros "!>" (W W' Hrelared) "[%Hval H]"; cbn.
      iSplitR; [done |].
      iApply (interp_in_mem_monotone_nl W W' C RWL with "H"); [exact Hrelared | done].
    }
    { cbn. iSplit; [done |].
      iApply interp_to_in_mem.
      iExact "Hinterp_cgp_b". }
    iMod (world_interp_extend_perm_nonheap with "Hworld_interp_C PermRes_cgp_a")
      as "(Hworld_interp_C & #Hrel_cgp_a)"; auto.
    { subst W1.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; apply LNonHeap_ne; solve_addr+Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }

    match goal with
    | _ : _ |- context [ world_interp ?W' ] => set (W3 := W')
    end.

    assert (related_sts_priv_world W0 W3) as HWinit_privC_W3.
    { subst W3.
      eapply related_sts_priv_trans_world with (W' := W1) ; eauto; first eapply revoke_related_sts_priv_world.
      eapply related_sts_priv_trans_world with (W' := W2) ; eauto; apply related_sts_priv_world_fresh_Permanent.
    }

    iAssert (interp W3 C (WCap true RO_DRO Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a)) as "#Hinterp_W3_C_a".
    { iEval (cbn). iEval (rewrite fixpoint_interp1_eq). iEval (cbn).
      iSplit; last (iPureIntro;
        pose proof (switcher_disjoint_subseg cgp_b cgp_e (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a
          ltac:(solve_addr) ltac:(solve_addr) (conj Hcgp_shadow Hcgp_heap))
          as [Hsub_shadow Hsub_heap];
        split; [exact Hsub_shadow|apply heap_cap_valid_disjoint; exact Hsub_heap]).
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)%a); last solve_addr.
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
      { iIntros "!>" (W1').
        iIntros "!>" (w') "[-> H]".
        done.
      }
      iSplit; first done.
      subst W1.
      iSplit.
      + rewrite /monoReq; cbn; rewrite lookup_insert_eq.
        iIntros (?) "%Hcontra"; rewrite /canStore in Hcontra.
        destruct (isLocalWord w.(lw)); done.
      + iPureIntro.
        by rewrite lookup_insert_eq.
    }

    iModIntro.
    iFrame "Hworld_interp_C Hrel_cgp_b Hinterp_W3_C_a".
    iSplit.
    { iApply (interp_monotone_sd_same_heap with "[] Hinterp_W0_C_f"); first reflexivity.
      by iPureIntro. }
    iSplit; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W0"); auto).

    (* The stack is still revoked *)
    iPureIntro.
    rewrite /revoked_addresses Forall_forall.
    intros x Hx.
    rewrite /revoked_addresses Forall_forall in Hstack_revoked.
    pose proof (Hstack_revoked x Hx) as Hx_revoked.
    assert (LNonHeap x ≠ LNonHeap cgp_b).
    { intros Heq. apply Hcgp_b. rewrite -Heq revoke_dom_eq elem_of_dom; eauto. }
    assert (LNonHeap x ≠ LNonHeap (cgp_b ^+ 1)%a).
    { intros Heq. apply Hcgp_a. rewrite -Heq revoke_dom_eq elem_of_dom; eauto. }
    rewrite /droe_Wshare /=.
    rewrite !lookup_insert_ne //.
  Qed.

  (** ** Return from the call

      The adversary returned a public future [W4] of [W3]. Since [cgp_b] is
      permanent in [W3], it is still permanent in [revoke W4], and opening
      the world gives back [cgp_b], which still contains [42]. *)
  Lemma droe_world_return W0 W4 C (cgp_b cgp_e csp_b csp_e : Addr) :
    let W3 := droe_Wshare W0 cgp_b in
    let stk := finz.seq_between csp_b csp_e in
    let stk' := finz.seq_between (csp_b ^+ 4)%a csp_e in
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    (csp_b <= csp_b ^+ 4)%a ->
    is_heap_address cgp_b = false ->
    revoked_addresses W3 stk ->
    related_sts_pub_world (std_update_multiple W3 stk' Temporary) W4 ->
    world_interp (revoke W4) C -∗
    rel C (LNonHeap cgp_b) RO_DRO droe_b_pred -∗
    ◇ cgp_b ↦ₐ WInt 42.
  Proof.
    intros W3 stk stk'.
    iIntros (Hcgp_contiguous Hcsp_bounds Hcgp_nonheap Hstack_revoked_W3 Hrelated_pub)
      "Hworld_interp #Hrel_cgp_b".
    assert (std W3 !! LNonHeap cgp_b = Some Permanent) as HW3_cgp_b.
    { rewrite /W3 /droe_Wshare /=.
      rewrite lookup_insert_ne; last (apply LNonHeap_ne; solve_addr).
      by rewrite lookup_insert_eq.
    }
    assert (cgp_b ∉ stk') as Hcgp_b_stk'.
    { intros Hin.
      rewrite /revoked_addresses Forall_forall in Hstack_revoked_W3.
      assert (cgp_b ∈ stk) as Hin'.
      { rewrite /stk /stk' !elem_of_finz_seq_between in Hin |- *; solve_addr+Hin Hcsp_bounds. }
      apply Hstack_revoked_W3 in Hin'; congruence.
    }
    rewrite open_world_interp_empty.
    iDestruct (open_world_interp_permanent_nonheap with "Hworld_interp Hrel_cgp_b")
      as "(_ & _ & [%w (_ & >Hcgp_b & Hw & _)])"; auto.
    { set_solver+. }
    { eapply (region_state_priv_perm W4); eauto.
      { eapply revoke_related_sts_priv_world. }
      eapply region_state_pub_perm; eauto.
      by rewrite std_sta_update_multiple_lookup_same_i.
    }
    rewrite /droe_b_pred /=.
    iDestruct "Hw" as "[>-> _]".
    by iModIntro.
  Qed.

End DROE_World.
