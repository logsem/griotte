From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import ti_spec_states.

(** * Logical steps of the proof of [ti_spec]

    The lemmas of this file do not execute code. They are used between the
    block groups of [ti_spec_<segment>_blocks_<n>] in the proof of
    [ti_spec]. *)

Section TI_World.
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

  (** ** Lending [b] to the callee

      The world of the call: [cgp_b] is added to the local map of the
      thread as a Temporary address. *)
  Definition ti_Wshare W (cgp_b : Addr) : WORLD := <s[cgp_b := Temporary ]s> W.

  (** Lend [cgp_b] in the local map of the thread, so that the capability
      [(RW, Local, cgp_b, cgp_b + 1, cgp_b)] is safe to share. The map of
      Permanent regions is not touched, so the lemma holds in either regime
      of [C]. The stack stays revoked. *)
  Lemma ti_world_share W C (cgp_b cgp_e csp_b csp_e : Addr) (B_f : Sealable) :
    let W1 := ti_Wshare W cgp_b in
    (cgp_b + length ti_K_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    LNonHeap cgp_b ∉ dom (std W) ->
    revoked_addresses W (finz.seq_between csp_b csp_e) ->
    thread_in th C -∗
    ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    world_resources W C -∗
    StackRevokedResources W C (finz.seq_between csp_b csp_e) -∗
    interp W C (WSealed ot_switcher B_f) -∗
    cgp_b ↦ₐ WInt 0
    ={⊤}=∗
    world_resources W1 C ∗
    interp W1 C (Cap RW Local cgp_b (cgp_b ^+ 1) cgp_b) ∗
    interp W1 C (WSealed ot_switcher B_f) ∗
    StackRevokedResources W1 C (finz.seq_between csp_b csp_e) ∗
    ⌜ revoked_addresses W1 (finz.seq_between csp_b csp_e) ⌝.
  Proof.
    intros W1.
    iIntros (Hcgp_contiguous Hcgp_mmio Hcgp_range Hcgp_b Hstack_revoked)
      "#Hthread #Hseal_switcher Hworld #Hstack_revoked_W #Hinterp_W_B_f Hcgp_b".
    destruct Hcgp_range as [Hcgp_nonheap Hcgp_heap].

    (* Extend the local map of the thread such that [cgp_b] is valid with RW access *)
    iDestruct (init_TmpRes W C cgp_b RW interp_in_memC
      with "[] [$Hcgp_b] []") as "TmpRes_cgp_b"; auto.
    { iApply future_pub_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iEval (rewrite world_resources_split) in "Hworld".
    iDestruct "Hworld" as "[Hlocal Hperm]".
    iMod (local_extend_temp W C (LNonHeap cgp_b) with "Hlocal TmpRes_cgp_b")
      as "[Hlocal #Hrel_cgp_b]"; first done.
    iModIntro.
    iSplitL "Hlocal Hperm".
    { rewrite world_resources_split. iFrame. }

    assert (related_sts_pub_world W W1) as Hrelated_pub_W_W1.
    { apply related_sts_pub_world_revoked_temporary'. by rewrite -not_elem_of_dom. }

    (* The RW capability pointing to [cgp_b] is safe *)
    iSplit.
    { iEval (rewrite interp_unfold); iEval (cbn). iLeft.
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
      iExists RW, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit.
      { iPureIntro; intros WCv; tc_solve. }
      iSplit.
      { iRight. iSplit; first iExact "Hrel_cgp_b".
        iSplit; first (iPureIntro; subst W1; cbn; by rewrite lookup_insert_eq).
        iApply mono_pub_interp_in_mem. }
      iSplit; first iApply zcond_interp_in_mem.
      iSplit; first iApply (rcond_l_interp_in_mem with "Hthread").
      iNext; iApply wcond_wl_wcond_nwl; iApply wcond_wl_interp_in_mem.
    }
    iSplit.
    { iApply (interp_sealed_global_kind_world_free with "Hseal_switcher Hinterp_W_B_f"). }
    iSplit.
    { iApply (StackRevokedResources_mono_priv with "Hstack_revoked_W").
      by apply related_sts_pub_priv_world. }

    (* The stack is still revoked *)
    iPureIntro.
    rewrite /revoked_addresses Forall_forall.
    intros x Hx.
    rewrite /revoked_addresses Forall_forall in Hstack_revoked.
    pose proof (Hstack_revoked x Hx) as Hx_revoked.
    assert (LNonHeap x ≠ LNonHeap cgp_b) as Hx_ne.
    { intros Heq. apply Hcgp_b. rewrite -Heq elem_of_dom; eauto. }
    rewrite /W1 /ti_Wshare /=.
    rewrite lookup_insert_ne //.
  Qed.

  (** ** Return from the call

      The callee returned a public future [W2] of the world of the call.
      The address [cgp_b], Temporary in it, is among the revoked addresses
      [l] that the switcher returns, which gives back a points-to of
      [cgp_b]. *)
  Lemma ti_world_return W W2 C (cgp_b csp_b csp_e : Addr) (l : list LAddr) :
    let W1 := ti_Wshare W cgp_b in
    let stk' := callee_stk_region csp_b csp_e (stk_start_a csp_b csp_e) in
    callee_stk_bounds csp_b csp_e (stk_start_a csp_b csp_e) ->
    revoked_addresses W1 (finz.seq_between csp_b csp_e) ->
    extract_temporaries_condition W2 (l ++ (LNonHeap <$> stk')) ->
    related_sts_pub_world (std_update_multiple W1 stk' Temporary) W2 ->
    RevokedResources W2 C l -∗
    ◇ ∃ w, cgp_b ↦ₐ w.
  Proof.
    intros W1 stk'.
    iIntros (Hcsp_bounds Hstack_revoked_W1 Hl_unk Hrelated_pub) "Hrevoked_l".
    assert (std W1 !! LNonHeap cgp_b = Some Temporary) as HW1_cgp_b.
    { rewrite /W1 /ti_Wshare /=. by rewrite lookup_insert_eq. }
    assert (Forall (λ a, std W1 !! LNonHeap a = Some Revoked) stk') as Hstack_revoked_W1'.
    { rewrite /revoked_addresses Forall_forall in Hstack_revoked_W1.
      apply Forall_forall; intros a Ha; apply Hstack_revoked_W1.
      apply elem_of_finz_seq_between.
      exact (callee_stk_region_incl _ _ _ _ Hcsp_bounds Ha).
    }
    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    { eapply related_sts_pub_trans_world ; eauto.
      by apply related_sts_pub_update_multiple_temp.
    }

    (* Extract [cgp_b] out of the revoked addresses *)
    iDestruct (big_sepL_elem_of_extract _
      (fun k => (∀ a', ⌜k = LNonHeap a'⌝ -∗ ▷ ∃ v, a' ↦ₐ v)%I) (LNonHeap cgp_b)
      with "[] [$Hrevoked_l]")
      as (l'') "(_ & _ & Hcgp_b_nonheap)".
    { assert (std W2 !! LNonHeap cgp_b = Some Temporary) as HW2.
      { eapply region_state_pub_temp; eauto. }
      destruct Hl_unk as [_ Hl_unk].
      apply Hl_unk in HW2.
      apply elem_of_app in HW2 as [?|Hstk]; first done.
      exfalso.
      apply elem_of_LNonHeap_fmap in Hstk.
      rewrite Forall_forall in Hstack_revoked_W1'.
      apply Hstack_revoked_W1' in Hstk; congruence.
    }
    { by destruct Hl_unk as [Hl_unk _]; apply NoDup_app in Hl_unk as (? & _ & _). }
    { clear; cbn.
      iIntros (a) "(%&%&% & _ & Haddr)". iIntros (a' ->).
      iEval (cbn) in "Haddr".
      iDestruct "Haddr" as (wa) "(_ & Ha & _)".
      iNext. iExists wa. iExact "Ha". }
    iDestruct ("Hcgp_b_nonheap" $! cgp_b with "[//]") as ">[%wcgpb Hcgp_b]".
    iModIntro. by iExists _.
  Qed.

End TI_World.
