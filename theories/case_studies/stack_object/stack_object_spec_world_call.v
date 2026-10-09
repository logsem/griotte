From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode register_tactics.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Import interp_weakening monotone world_std_revocation.
From griotte Require Import world_ghost_theory world_interp_stack interp_switcher_call.
From griotte Require Import stack_object_spec_states.

(** * Preparation of the call to the callback [g]

    The lemmas of this file do not execute code. They are used between the
    block group [stack_object_spec_call_blocks_3] and the call to the
    switcher in the proof of [stack_object_f_spec]:
    - [so_world_call] reinstates the freshly allocated stack object [z] in
      the world, so that it is safe to share,
    - [so_call_args] builds the argument registers of the call,
    - [so_args_zero] states that the unused argument registers of [f] are
      cleared. *)

Section SO_World_Call.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma stack_object_reinstate_fresh_object
      (W0 W2 : WORLD) (C : CmptName)
      (stack_b stack_e stack_a a_stk1 a_stk2 : Addr) :
    let W3 := reinstate W2 [a_stk1] in
    (a_stk1 + 1)%a = Some a_stk2 ->
    (stack_b <= a_stk1)%a /\
    (a_stk1 < a_stk2)%a /\
    (a_stk2 <= stack_e)%a ->
    std W0 !! a_stk1 = Some Temporary ->
    std W2 !! a_stk1 = Some Revoked ->
    related_sts_priv_world W0 W2 ->
    interp W0 C (WCap RWL Local stack_b stack_e stack_a)
    ∗ world_interp W2 C
    ∗ a_stk1 ↦ₐ WInt 0
    ∗ £ 1
    ={⊤}=∗
      world_interp W3 C
      ∗ ⌜related_sts_pub_world W2 W3⌝
      ∗ ⌜std W3 !! a_stk1 = Some Temporary⌝
      ∗ interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1).
  Proof.
    intros W3 Ha_stk2 Hbounds Ha_stk1_W0 Ha_stk1_W2 Hpriv.
    iIntros "(#Hinterp_stack & Hworld_interp & Ha_stk1 & Hlc)".
    destruct Hbounds as (Hstack_b_stk1 & Hastk1_stk2 & Hastk2_stack_e).

    (* Turn the freshly zeroed stack cell into the closing resource required
       by [world_interp_restore_world], consuming exactly one later credit. *)
    iAssert (
        |={⊤}=> ([∗ list] a ∈ [a_stk1],
          ∃ p φ, ⌜forall Wv, Persistent (φ Wv)⌝
            ∗ temp_resources W2 C φ a p ∗ rel C a p φ)
      )%I with "[Ha_stk1 Hlc]" as ">Hclosing_resources".
    { cbn.
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp_stack")
        as "(%pastk1 & %Pastk1 & %Hpastk1_rwl & %Hpers_Pastk1
             & #Hrel_astk1 & Hzcond_Pastk1 & Hrcond_Pastk1
             & Hwcond_Pastk1 & Hmono_Pastk1)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      replace (writeAllowed pastk1) with true.
      2: { symmetry; eapply writeAllowed_flowsto; eauto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hwcond_Pastk1]")
        as ">#Hwcond_Pastk1'".
      assert (isWL pastk1 = true) as Hpastk1_wl.
      { apply isWL_flowsto in Hpastk1_rwl; done. }
      iModIntro.
      iSplitL; last done.
      iExists pastk1, (safeC Pastk1).
      iSplit; first iPureIntro.
      { intros Wcv; apply Hpers_Pastk1. }
      iSplit; last iFrame "#".
      iFrame "Ha_stk1".
      iSplit; first iPureIntro.
      { by apply isWL_nonO. }
      rewrite /monoReq !Hpastk1_wl Ha_stk1_W0.
      iSplit; first iApply "Hmono_Pastk1".
      rewrite /=.
      iApply "Hwcond_Pastk1'".
      iApply interp_int.
    }

    (* Reinstate the cell and package both its state transition and the safe
       singleton RWL capability needed by the adversary call. *)
    iMod (world_interp_restore_world W2 W2 C [a_stk1]
      with "[$Hworld_interp] [Hclosing_resources]")
      as "Hworld_interp".
    { apply close_list_related_sts_pub. }
    { iClear "#".
      iApply (big_sepL_impl with "Hclosing_resources").
      iModIntro; iIntros (k ka Hka) "(%&%&$&(%&$&$&?&$)&$)".
      by rewrite mono_temporary_eq.
    }

    assert (related_sts_pub_world W2 W3) as Hpub.
    { apply close_list_related_sts_pub. }
    assert (std W3 !! a_stk1 = Some Temporary) as Ha_stk1_W3.
    { apply close_list_lookup_in; auto; set_solver+. }

    iAssert (interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1))%I
      as "#Hinterp_fresh".
    { iEval (rewrite fixpoint_interp1_eq interp1_eq).
      cbn.
      iSplit; last done.
      rewrite (finz_seq_between_singleton a_stk1 a_stk2);
        last solve_addr+Ha_stk2 Hastk1_stk2.
      cbn.
      iSplit; last done.
      iClear "∗".
      iDestruct "Hinterp_stack" as "-#Hinterp"; iClear "#".
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp")
        as "(%px & %Px & %Hpx_flow & %HPx_pers & Hrelx
             & Hzcondx & Hrcondx & Hwcondx & Hmonox)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      iFrame "∗%".
      apply readAllowed_flowsto in Hpx_flow; last done.
      rewrite Hpx_flow; iFrame.
      rewrite /monoReq Ha_stk1_W0 Ha_stk1_W3; done.
    }
    iModIntro. iFrame "#∗%".
  Qed.

  (** After the checks of the stack object [in] (whose temporary addresses
      have been put back in the revoked world [W0]), the one-cell stack
      object [z] at [a_stk1], right after the secret at [csp_b], is
      reinstated in the world [W3] of the call. The arguments of the call
      are safe in [W3], and the stack frame of the callee is revoked. *)
  Lemma so_world_call
      (W0 : WORLD) (C : CmptName)
      (p : Perm) (g : Locality) (b e : Addr)
      (csp_b csp_e a_stk1 a_stk2 : Addr)
      (l_revoked : list Addr) (wct1 : Word) :
    let W2 := close_list (so_object_temporaries W0 b e) (revoke W0) in
    let W3 := reinstate W2 [a_stk1] in
    extract_temporaries_condition W0 (l_revoked ++ finz.seq_between csp_b csp_e) ->
    finz.seq_between b e ## finz.seq_between csp_b csp_e ->
    (csp_b + 1)%a = Some a_stk1 ->
    (a_stk1 + 1)%a = Some a_stk2 ->
    (a_stk2 <= csp_e)%a ->
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    interp W0 C wct1 -∗
    world_interp W2 C -∗
    interp W2 C (WCap p g b e (finz.max b e)) -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    a_stk1 ↦ₐ WInt 0 -∗
    £ 1
    ={⊤}=∗
    world_interp W3 C ∗
    interp W3 C (WCap p g b e (finz.max b e)) ∗
    interp W3 C (WCap RWL Local a_stk1 a_stk2 a_stk1) ∗
    (if is_sealed_with_o wct1 ot_switcher then interp W3 C wct1 else True) ∗
    StackRevokedResources W3 C (finz.seq_between a_stk2 csp_e) ∗
    ⌜revoked_addresses W3 (finz.seq_between a_stk2 csp_e)⌝ ∗
    ⌜related_sts_priv_world W0 W3⌝ ∗
    ⌜std W3 !! a_stk1 = Some Temporary⌝.
  Proof.
    intros W2 W3.
    iIntros (Hextract Hno_overlap Hastk1 Hastk2 Hastk2_csp_e)
      "#Hinterp_csp #Hinterp_wct1 Hworld_interp_C #Hinterp_object Hstack_revoked Hastk1 Hlc".
    destruct Hextract as [Hl_revoked_nodup Hl_revoked_temporaries].
    set (temps := so_object_temporaries W0 b e) in *.
    assert (related_sts_priv_world W0 (revoke W0)) as Hpriv_W0_W1
      by apply revoke_related_sts_priv_world.
    assert (related_sts_pub_world (revoke W0) W2) as Hpub_W1_W2
      by apply close_list_related_sts_pub.
    assert (related_sts_priv_world W0 W2) as Hpriv_W0_W2
      by (eapply related_sts_priv_pub_trans_world; eauto).
    assert (finz.seq_between csp_b csp_e ## temps) as Hstack_temps.
    { rewrite elem_of_disjoint in Hno_overlap |- *.
      intros x Hx_stk Hx_temp.
      eapply Hno_overlap; last exact Hx_stk.
      subst temps.
      by apply list_elem_of_filter in Hx_temp as [_ Hx_object].
    }
    assert (std W0 !! a_stk1 = Some Temporary) as Ha_stk1_W0.
    { apply Hl_revoked_temporaries.
      apply elem_of_app; right.
      apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hastk2_csp_e.
    }
    assert (std W2 !! a_stk1 = Some Revoked) as Ha_stk1_W2.
    { subst W2.
      rewrite close_list_lookup_not_in.
      - apply revoke_lookup_Monotemp. exact Ha_stk1_W0.
      - intro Ha'.
        rewrite elem_of_disjoint in Hstack_temps.
        eapply Hstack_temps; eauto.
        apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hastk2_csp_e.
    }

    (* Insert the allocated stack object [a_stk1] in the world *)
    iMod (stack_object_reinstate_fresh_object
            W0 W2 C csp_b csp_e csp_b a_stk1 a_stk2
           with "[$Hinterp_csp $Hworld_interp_C $Hastk1 $Hlc]")
      as "(Hworld_interp_C & %Hpub_W2_W3 & %Ha_stk1_W3 & #Hinterp_z)"; eauto.
    { split; first solve_addr+Hastk1.
      split; solve_addr+Hastk1 Hastk2 Hastk2_csp_e. }
    assert (related_sts_priv_world W0 W3) as Hpriv_W0_W3.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    iModIntro.
    iFrame "Hworld_interp_C Hinterp_z".
    iSplit; first (iApply interp_monotone; eauto).

    (* The callback is safe to share in [W3] *)
    iSplit.
    { destruct (is_sealed_with_o wct1 ot_switcher) eqn:His_sealed; last done.
      destruct wct1 as [| [|] | |]; try discriminate.
      iApply (interp_monotone_sd W0 W3); eauto.
    }

    (* The stack frame of the callee is still revoked *)
    rewrite (finz_seq_between_cons csp_b csp_e); last solve_addr+Hastk1 Hastk2 Hastk2_csp_e.
    iEval (cbn) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[_ Hstack_revoked]".
    rewrite (finz_seq_between_cons ((csp_b ^+ 1)%a) csp_e);
      last solve_addr+Hastk1 Hastk2 Hastk2_csp_e.
    iEval (cbn) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[_ Hstack_revoked]".
    replace ((csp_b ^+ 1) ^+ 1)%a with a_stk2 by solve_addr+Hastk1 Hastk2.
    iSplitL; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto).
    iPureIntro.
    split; last done.
    apply Forall_forall; intros x Hx.
    apply elem_of_finz_seq_between in Hx.
    subst W3 W2.
    rewrite close_list_lookup_not_in.
    2: { intros Hx'; apply list_elem_of_singleton in Hx'; simplify_eq.
         solve_addr+Hx Hastk2. }
    rewrite close_list_lookup_not_in.
    2: { intro Hx'.
         apply Hstack_temps in Hx'; first done.
         apply elem_of_finz_seq_between.
         solve_addr+Hx Hastk1 Hastk2.
    }
    apply revoke_lookup_Monotemp.
    apply Hl_revoked_temporaries.
    apply elem_of_app; right.
    apply elem_of_finz_seq_between.
    solve_addr+Hx Hastk1 Hastk2.
  Qed.

  (** The argument registers of [f] other than [in] and [g] are cleared. *)
  Lemma so_args_zero (rmap : Reg) :
    (∀ r, is_Some (rmap !! r)) ->
    (∀ (r : RegName) (v : Word),
        ⌜r ∉ ({[PC; cra; cgp; csp]} ∪ dom_arg_rmap 2 : gset RegName)⌝ →
        ⌜rmap !! r = Some v⌝ →
        ⌜v = WInt 0⌝ : iProp Σ) -∗
    ⌜∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) → rmap !! r = Some (WInt 0)⌝.
  Proof.
    iIntros (Hfull) "#Hzero".
    iIntros (r Hr).
    destruct (Hfull r) as [v Hv].
    iDestruct ("Hzero" $! r v with "[%] [%]") as %->; [|done|done].
    rewrite /dom_arg_rmap.
    set_solver.
  Qed.

  (** The argument registers of the call to [g]: the stack objects [in]
      (in [ca0]) and [z] (in [ca1]), the entry point of the switcher (in
      [ct0]), and the cleared argument registers. *)
  Lemma so_call_args W C (Nswitcher : namespace) (rmap : Reg) (wca0 wca1 : Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ct0 ]} ->
    (∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) → rmap !! r = Some (WInt 0)) ->
    na_inv cerise_nais Nswitcher switcher_inv -∗
    ca0 ↦ᵣ wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ wca1 -∗
    interp W C wca1 -∗
    ct0 ↦ᵣ so_switcher_entry -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg) ∗
      ([∗ map] r↦w ∈ rmap', r ↦ᵣ w).
  Proof.
    iIntros (Hrmap_dom Hzero) "#Hswitcher Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hct0 Hrmap".
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]".
    { apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]".
    { rewrite lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := WInt 0; ca3 := WInt 0;
               ca4 := WInt 0; ca5 := WInt 0; ct0 := so_switcher_entry ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      rewrite !dom_delete_L Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    iAssert (interp W C (WInt 0)) as "#Hinterp_0"; first iApply interp_int.
    iAssert (interp W C so_switcher_entry) as "#Hinterp_switcher".
    { iApply interp_switcher_call; done. }
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  (** ** Call to the adversary [C.adv] in [run]

      Revoke the world [W0], to get the stack frame. The entry point of the
      adversary is still safe in the revoked world. *)
  Lemma so_world_run_call W0 C (csp_b csp_e : Addr) (C_f : Sealable) :
    interp W0 C (WCap RWL Local csp_b csp_e csp_b) -∗
    interp W0 C (WSealed ot_switcher C_f) -∗
    world_interp W0 C
    ={⊤}=∗
    ∃ stk_mem,
      world_interp (revoke W0) C ∗
      interp (revoke W0) C (WSealed ot_switcher C_f) ∗
      ▷ StackRevokedResources (revoke W0) C (finz.seq_between csp_b csp_e) ∗
      ⌜revoked_addresses (revoke W0) (finz.seq_between csp_b csp_e)⌝ ∗
      [[csp_b, csp_e]] ↦ₐ [[stk_mem]].
  Proof.
    iIntros "#Hinterp_csp #Hinterp_C_f Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & _ & _)".
    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    iModIntro.
    iExists stk_mem.
    iFrame "Hworld_interp_C Hstk".
    iSplit; first (iApply interp_monotone_sd; eauto).
    iSplit; last done.
    iNext.
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

End SO_World_Call.
