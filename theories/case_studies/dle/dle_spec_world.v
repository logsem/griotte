From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import dle_spec_states.

(** * Logical steps of the proof of [dle_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [dle_spec_<segment>_blocks_<n>] in the proof of
    [dle_spec]. *)

Section DLE_World.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** ** Sharing the data with the adversary

      The world in which the first call happens: [cgp_b] and [cgp_b + 1] are
      added to the revoked world as temporary addresses. *)
  Definition dle_Wshare W (cgp_b : Addr) : WORLD :=
    <s[(cgp_b ^+ 1) := Temporary ]s> (<s[cgp_b := Temporary ]s> (revoke W)).

  Lemma dle_world_share W0 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable) :
    let W3 := dle_Wshare W0 cgp_b in
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    LNonHeap cgp_b ∉ dom (std W0) ->
    LNonHeap (cgp_b ^+ 1) ∉ dom (std W0) ->
    revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e) ->
    world_interp (revoke W0) C -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    cgp_b ↦ₐ WInt 0 -∗
    (cgp_b ^+ 1) ↦ₐ Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b
    ={⊤}=∗
    world_interp W3 C ∗
    interp W3 C (Cap RW_DL Local (cgp_b ^+ 1) (cgp_b ^+ 2) (cgp_b ^+ 1)) ∗
    interp W3 C (WSealed ot_switcher C_f) ∗
    StackRevokedResources W3 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W3 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W3.
    iIntros (Hcgp_contiguous Hcgp_mmio Hcgp_range Hcgp_b Hcgp_a Hstack_revoked)
      "Hworld_interp_C #Hstack_revoked_W0 #Hinterp_W0_C_f Hcgp_b Hcgp_a".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].
    set (W1 := revoke W0).

    (* First, extend the world such that [cgp_b] is valid with RW_DL access *)
    iDestruct (init_TmpRes W1 C cgp_b RW_DL interp_in_memC
      with "[] [$Hcgp_b] []") as "TmpRes_cgp_b"; auto.
    { iApply future_pub_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_temp_nonheap
      with "Hworld_interp_C TmpRes_cgp_b")
      as "(Hworld_interp_C & #Hrel_cgp_b)"; auto.
    { by rewrite -revoke_dom_eq. }
    set (W2 := <s[cgp_b:=Temporary]s> W1).

    (* And prove that the RW_DL capability pointing to it is safe *)
    iAssert (interp W2 C (Cap RW_DL Local cgp_b (cgp_b ^+ 1) cgp_b))
      as "#Hinterp_cgp_b".
    { iEval (rewrite interp_unfold); iEval (cbn).
      iSplit; cycle 1.
      { pose proof (switcher_disjoint_subseg cgp_b cgp_e cgp_b (cgp_b ^+ 1))
          as [Hsub_shadow Hsub_heap];
          [solve_addr + Hcgp_contiguous | solve_addr + Hcgp_contiguous | split; auto |].
        iSplit; first (iPureIntro; done).
        iApply heap_cap_ok_disjoint; done.
      }
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons cgp_b); last solve_addr + Hcgp_contiguous.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 1)); last solve_addr + Hcgp_contiguous.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RW_DL, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit; first iFrame "Hrel_cgp_b".
      iSplit; first iApply zcond_interp_in_mem.
      iSplit; first iApply rcond_interp_in_mem.
      iSplit; first iApply wcond_interp_in_mem.
      iSplit; first iApply monoReq_interp_in_mem.
      + subst W2; cbn; by rewrite lookup_insert_eq.
      + by intro.
      + by iPureIntro; right; subst W2; cbn; rewrite lookup_insert_eq.
    }

    assert (is_heap_address (cgp_b ^+ 1) = false) as Hcgp1_nonheap.
    { apply not_true_is_false; intros Hheap.
      apply withinBounds_true_iff in Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hcgp_heap.
      eapply (Hcgp_heap (cgp_b ^+ 1)); apply elem_of_finz_seq_between;
        [solve_addr + Hcgp_contiguous | exact Hheap]. }

    (* Second, extend the world such that [cgp_b+1] is valid with RW_DL access *)
    iDestruct (init_TmpRes W2 C (cgp_b ^+ 1) RW_DL (safeC interp_in_mem_dl)
      with "[] [$Hcgp_a] []") as "TmpRes_cgp_a"; auto.
    { iApply future_pub_mono_interp_in_mem_dl. }
    iMod (world_interp_extend_temp_nonheap
      with "Hworld_interp_C TmpRes_cgp_a")
      as "(Hworld_interp_C & Hrel_cgp_a)"; auto.
    { subst W2.
      cbn; rewrite dom_insert_L not_elem_of_union; split.
      + rewrite not_elem_of_singleton; intros [= Heq]; solve_addr + Heq Hcgp_contiguous.
      + by rewrite -revoke_dom_eq.
    }
    iFrame "Hworld_interp_C".
    iModIntro.

    assert (related_sts_priv_world W0 W3) as Hrelated_priv_W0_W3.
    { eapply related_sts_priv_trans_world with (W' := W1); eauto
      ; first eapply revoke_related_sts_priv_world.
      eapply related_sts_pub_priv_trans_world with (W' := W2); eauto.
      { eapply related_sts_pub_world_revoked_temporary'.
        by rewrite -revoke_lookup_None -not_elem_of_dom.
      }
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_revoked_temporary'.
      rewrite lookup_insert_ne; last (apply LNonHeap_ne; solve_addr + Hcgp_contiguous).
      by rewrite -revoke_lookup_None -not_elem_of_dom.
    }

    (* The RW_DL capability pointing to [cgp_b+1] is safe *)
    iSplit.
    { iEval (rewrite interp_unfold); iEval (cbn).
      iSplit; cycle 1.
      { pose proof (switcher_disjoint_subseg cgp_b cgp_e (cgp_b ^+ 1) (cgp_b ^+ 2))
          as [Hsub_shadow Hsub_heap];
          [solve_addr + Hcgp_contiguous | solve_addr + Hcgp_contiguous | split; auto |].
        iSplit; first (iPureIntro; done).
        iApply heap_cap_ok_disjoint; done.
      }
      rewrite /interp_cap_body.
      rewrite (finz_seq_between_cons (cgp_b ^+ 1)); last solve_addr + Hcgp_contiguous.
      rewrite (finz_seq_between_empty _ (cgp_b ^+ 2)); last solve_addr + Hcgp_contiguous.
      iApply big_sepL_singleton.
      rewrite addr_key_None.
      iExists RW_DL, interp_in_mem_dl.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro; apply persistent_cond_interp_in_mem_dl).
      iSplit; first iFrame "Hrel_cgp_a".
      iSplit; first iApply zcond_interp_in_mem_dl.
      iSplit; first (iApply rcond_interp_in_mem_dl; auto).
      iSplit; first iApply wcond_interp_in_mem_dl.
      iSplit; last (by iPureIntro; right; rewrite lookup_insert_eq).
      rewrite /monoReq; rewrite lookup_insert_eq; cbn.
      iApply mono_pub_interp_in_mem_dl.
    }
    iSplit.
    { iApply (interp_monotone_sd_same_heap with "[] Hinterp_W0_C_f").
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
    assert (LNonHeap x ≠ LNonHeap (cgp_b ^+ 1)).
    { intros Heq. apply Hcgp_a. rewrite -Heq revoke_dom_eq elem_of_dom; eauto. }
    rewrite /W3 /dle_Wshare /=.
    rewrite !lookup_insert_ne //.
  Qed.

  (** ** Return from the first call

      The adversary returned a public future [W4] of [W3]. Revoking [W4]
      gives back [cgp_b], and the stack and the entry point of the adversary
      are still valid in the revoked world. *)
  Lemma dle_world_return W0 W4 C (cgp_b cgp_e csp_b csp_e : Addr) (C_f : Sealable)
    (l : list LAddr) :
    let W3 := dle_Wshare W0 cgp_b in
    let stk := finz.seq_between csp_b csp_e in
    let stk_f := stk_free csp_b csp_e (stk_start_a csp_b csp_e) in
    let stk' := callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e) in
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    revoked_addresses W3 stk ->
    extract_temporaries_condition W4 (l ++ (LNonHeap <$> stk')) ->
    related_sts_pub_world (std_update_multiple W3 stk' Temporary) W4 ->
    RevokedResources W4 C l -∗
    interp W3 C (WSealed ot_switcher C_f) -∗
    StackRevokedResources W4 C stk_f -∗
    ◇ ( (∃ w, cgp_b ↦ₐ w) ∗
        interp (revoke W4) C (WSealed ot_switcher C_f) ∗
        StackRevokedResources (revoke W4) C stk_f ).
  Proof.
    intros W3 stk stk_f stk'.
    iIntros (Hcgp_contiguous Hcsp_bounds Hsealed_nonheap Hstack_revoked_W3 Hl_unk Hrelated_pub)
      "Hrevoked_l #Hinterp_W3_C_f #Hstack_revoked_W4".
    assert (std W3 !! LNonHeap cgp_b = Some Temporary) as HW3_cgp_b.
    { rewrite /W3 /dle_Wshare /=.
      rewrite lookup_insert_ne; last (apply LNonHeap_ne; solve_addr).
      by rewrite lookup_insert_eq.
    }
    assert (Forall (λ a, std W3 !! LNonHeap a = Some Revoked) stk') as Hstack_revoked_W3'.
    { rewrite /revoked_addresses Forall_forall in Hstack_revoked_W3.
      apply Forall_forall; intros a Ha; apply Hstack_revoked_W3.
      apply elem_of_finz_seq_between.
      exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Ha).
    }
    assert (related_sts_pub_world W3 W4) as Hrelated_pub_W3_W4.
    { eapply related_sts_pub_trans_world ; eauto.
      by apply related_sts_pub_update_multiple_temp.
    }

    (* Extract [cgp_b] out of the revoked addresses *)
    iDestruct (big_sepL_elem_of_extract _
      (fun k => (∀ a', ⌜k = LNonHeap a'⌝ -∗ ▷ ∃ v, a' ↦ₐ v)%I) (LNonHeap cgp_b)
      with "[] [$Hrevoked_l]")
      as (l'') "(_ & _ & Hcgp_b_nonheap)".
    { assert (std W4 !! LNonHeap cgp_b = Some Temporary) as HW4.
      { eapply region_state_pub_temp; eauto. }
      destruct Hl_unk as [_ Hl_unk].
      apply Hl_unk in HW4.
      apply elem_of_app in HW4 as [?|Hstk]; first done.
      exfalso.
      apply elem_of_LNonHeap_fmap in Hstk.
      rewrite Forall_forall in Hstack_revoked_W3'.
      apply Hstack_revoked_W3' in Hstk; congruence.
    }
    { by destruct Hl_unk as [Hl_unk _]; apply NoDup_app in Hl_unk as (? & _ & _). }
    { iClear "#"; clear; cbn.
      iIntros (a) "(%&%&% & _ & Haddr)". iIntros (a' ->).
      iEval (cbn) in "Haddr".
      iDestruct "Haddr" as (wa) "(_ & Ha & _)".
      iNext. iExists wa. iExact "Ha". }
    iDestruct ("Hcgp_b_nonheap" $! cgp_b with "[//]") as ">[%wcgpb Hcgp_b]".
    iModIntro.
    iSplitL "Hcgp_b"; first by iExists _.

    (* The entry point of the adversary and the stack are still valid *)
    assert (related_sts_priv_world W4 (revoke W4)) as Hrelated_priv_W4
        by apply revoke_related_sts_priv_world.
    iSplit.
    { iApply (interp_monotone_sd_same_heap W3 (revoke W4) with "[] Hinterp_W3_C_f").
      iPureIntro.
      eapply related_sts_priv_trans_world; last exact Hrelated_priv_W4.
      by apply related_sts_pub_priv_world.
    }
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W4"); auto.
  Qed.

End DLE_World.
