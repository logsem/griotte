From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region proofmode register_tactics.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Import interp_weakening monotone world_std_revocation.
From griotte Require Import world_ghost_theory world_interp_stack switcher_base_interp.
From griotte Require Import allocator_resources heap_region.
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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma stack_object_reinstate_fresh_object
      (W0 W2 : WORLD) (C : CmptName)
      (stack_b stack_e stack_a a_stk1 a_stk2 : Addr) :
    let W3 := reinstate W2 [LNonHeap a_stk1] in
    (a_stk1 + 1)%a = Some a_stk2 ->
    (stack_b <= a_stk1)%a /\
    (a_stk1 < a_stk2)%a /\
    (a_stk2 <= stack_e)%a ->
    std W0 !! LNonHeap a_stk1 = Some Temporary ->
    std W2 !! LNonHeap a_stk1 = Some Revoked ->
    related_sts_priv_world W0 W2 ->
    interp W0 C (Cap RWL Local stack_b stack_e stack_a)
    ∗ world_interp W2 C
    ∗ a_stk1 ↦ₐ WInt 0
    ∗ £ 1
    ={⊤}=∗
      world_interp W3 C
      ∗ ⌜related_sts_pub_world W2 W3⌝
      ∗ ⌜std W3 !! LNonHeap a_stk1 = Some Temporary⌝
      ∗ interp W3 C (Cap RWL Local a_stk1 a_stk2 a_stk1).
  Proof.
    intros W3 Ha_stk2 Hbounds Ha_stk1_W0 Ha_stk1_W2 Hpriv.
    iIntros "(#Hinterp_stack & Hworld_interp & Ha_stk1 & Hlc)".
    destruct Hbounds as (Hstack_b_stk1 & Hastk1_stk2 & Hastk2_stack_e).
    assert (addr_key None a_stk1 = LNonHeap a_stk1) as Hkey_stk1 by done.

    (* The freshly zeroed stack address is the closing resource required by
       [world_interp_restore_world]: its predicate holds for [0] under a
       later. *)
    iAssert (RevokedResources W2 C [LNonHeap a_stk1])%I
      with "[Ha_stk1]" as "Hclosing_resources".
    { iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp_stack")
        as "(%pastk1 & %Pastk1 & %Hpastk1_rwl & %Hpers_Pastk1
             & #Hrel_astk1 & _ & _ & Hwcond_Pastk1)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      iEval (rewrite /region_rel /= ?Hkey_stk1) in "Hrel_astk1".
      iDestruct "Hrel_astk1" as "(#Hrel_astk1 & _ & #Hmono_Pastk1)".
      replace (writeAllowed pastk1) with true.
      2: { symmetry; eapply writeAllowed_flowsto; eauto. }
      assert (isWL pastk1 = true) as Hpastk1_wl.
      { apply isWL_flowsto in Hpastk1_rwl; done. }
      rewrite /RevokedResources /=.
      iSplitL; last done.
      iExists pastk1, (safeC Pastk1).
      iSplit; first iPureIntro.
      { intros Wcv; apply Hpers_Pastk1. }
      iFrame "Hrel_astk1".
      rewrite /temp_res. iApply heap_key_resource_intro.
      iExists (WInt 0). rewrite /temp_body.
      iSplit; first iPureIntro.
      { by apply isWL_nonO. }
      iFrame "Ha_stk1".
      iSplit; first iApply "Hmono_Pastk1".
      iNext. rewrite /=.
      iApply "Hwcond_Pastk1".
      iApply interp_int.
    }

    (* Reinstate the address and package both its state transition and the safe
       singleton RWL capability needed by the adversary call. *)
    iDestruct (interp_cap_disjoint_wl with "Hinterp_stack") as %[_ Hstack_heap]; first done.
    assert (is_heap_address a_stk1 = false) as Hastk1_nonheap.
    { apply not_true_is_false. intros Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hstack_heap.
      apply (Hstack_heap a_stk1).
      - apply elem_of_finz_seq_between. solve_addr.
      - apply elem_of_finz_seq_between.
        apply withinBounds_true_iff in Hheap. solve_addr.
    }
    iMod (world_interp_restore_world W2 W2 C [LNonHeap a_stk1]
      with "[$Hworld_interp] [Hclosing_resources]")
      as "Hworld_interp".
    { apply close_list_related_sts_pub. }
    { iExact "Hclosing_resources". }

    assert (related_sts_pub_world W2 W3) as Hpub.
    { apply close_list_related_sts_pub. }
    assert (std W3 !! LNonHeap a_stk1 = Some Temporary) as Ha_stk1_W3.
    { apply close_list_lookup_in; auto; set_solver+. }

    iAssert (interp W3 C (Cap RWL Local a_stk1 a_stk2 a_stk1))%I
      as "#Hinterp_fresh".
    { iEval (rewrite interp_unfold interp1_eq).
      cbn.
      iDestruct (interp_cap_disjoint_wl with "Hinterp_stack") as %[Hshadow Hheap]; first done.
      iSplit; last first.
      { rewrite /disjoint_from_heap elem_of_disjoint in Hheap.
        iSplit.
        - iPureIntro. split; first done.
          eapply disjoint_from_mmio_weaken; last exact Hshadow; solve_addr.
        - iApply heap_cap_ok_disjoint.
          rewrite /disjoint_from_heap elem_of_disjoint.
          intros x Hx Hregion.
          eapply Hheap; [|exact Hregion].
          apply elem_of_finz_seq_between.
          apply elem_of_finz_seq_between in Hx. solve_addr.
      }
      rewrite (finz_seq_between_singleton a_stk1 a_stk2);
        last solve_addr+Ha_stk2 Hastk1_stk2.
      cbn.
      iSplit; last done.
      iClear "∗".
      iDestruct "Hinterp_stack" as "-#Hinterp"; iClear "#".
      iDestruct (read_allowed_inv _ _ a_stk1 with "Hinterp")
        as "(%px & %Px & %Hpx_flow & %HPx_pers & Hrelx
             & Hzcondx & Hrcondx & Hwcondx)"; auto.
      { solve_addr+Ha_stk2 Hstack_b_stk1 Hastk1_stk2 Hastk2_stack_e. }
      iEval (rewrite /region_rel /= ?Hkey_stk1) in "Hrelx".
      iDestruct "Hrelx" as "(Hrelx & _ & Hmonox)".
      iExists px, Px. iFrame "Hzcondx %".
      iSplitL "Hrelx Hmonox".
      { rewrite /region_rel /=. by iFrame "Hrelx Hmonox". }
      apply readAllowed_flowsto in Hpx_flow; last done.
      rewrite Hpx_flow; iFrame.
    }
    iModIntro. iFrame "#∗%".
  Qed.

  (** Split the revoked keys [l] into the keys that hold their cells and the
      tombstones of freed objects, and close the tombstones in [Wcur]: they
      own no memory. *)
  Lemma so_world_quarantine (Wbase Wcur : WORLD) (C : CmptName) (l : list LAddr) :
    world_interp Wcur C -∗
    RevokedResources Wbase C l
    ==∗
    ∃ l_live l_q,
      ⌜l ≡ₚ l_live ++ l_q⌝ ∗
      ⌜Forall (λ a, ∃ x ι, a = LHeap x ι) l_q⌝ ∗
      world_interp (close_list l_q Wcur) C ∗
      RevokedCells Wbase C l_live.
  Proof.
    iIntros "Hworld_interp_C Hrevoked_l".
    iAssert (∃ l_live l_q,
      ⌜l ≡ₚ l_live ++ l_q⌝ ∗
      ⌜Forall (λ a, ∃ x ι, a = LHeap x ι) l_q⌝ ∗
      RevokedResources Wcur C l_q ∗
      RevokedCells Wbase C l_live)%I
      with "[Hrevoked_l]" as (l_live l_q) "(%Hpartition & %Hq & Hl_q & Hl_live)".
    { iInduction l as [|k l] "IH".
      { iExists [], []. rewrite /RevokedResources /RevokedCells /=. by iFrame. }
      iDestruct "Hrevoked_l" as "[(%pa & %Φa & %Hpers & #Hrel & Hk) Hl]".
      iDestruct ("IH" with "Hl") as (l_live l_q) "(%Hpartition & %Hq & Hl_q & Hl_live)".
      iDestruct (heap_key_open_cases with "Hk") as "[Hk | (%x & %ι & -> & #Hquar)]".
      - iExists (k :: l_live), l_q. iFrame "Hl_q Hl_live".
        iSplit; first (iPureIntro; by rewrite Hpartition).
        iSplit; first done.
        iExists pa, Φa. rewrite /temp_body. by iFrame "Hrel Hk".
      - iExists l_live, (LHeap x ι :: l_q). iFrame "Hl_live Hl_q".
        iSplit; first (iPureIntro; rewrite Hpartition; apply Permutation_middle).
        iSplit; first (iPureIntro; constructor; eauto).
        iExists pa, Φa. iFrame "Hrel". iSplit; first done.
        by iApply heap_key_close_tomb. }
    iMod (world_interp_restore_world Wcur Wcur C l_q
           with "Hworld_interp_C Hl_q") as "Hworld_interp_C".
    { apply close_list_related_sts_pub. }
    iModIntro. iExists l_live, l_q. by iFrame.
  Qed.

  (** After the checks of the stack object [in] (whose temporary addresses
      have been put back in the revoked world [W0], together with the
      quarantined revoked keys [l_q]), the one-cell stack object [z] at
      [a_stk2], right below the secret at [a_stk1], is reinstated in the
      world [W3] of the call. The arguments of the call are safe in [W3],
      and the stack frame of the callee is revoked. *)
  Lemma so_world_call
      (W0 : WORLD) (C : CmptName)
      (t : bool) (p : Perm) (g : Locality) (b e : Addr) (π : option AId)
      (csp_b csp_e a_stk1 a_stk2 : Addr)
      (l_revoked l_q : list LAddr) (wct1 : LWord) :
    let W2 := close_list (addr_key π <$> so_object_temporaries W0 π b e) (revoke W0) in
    let W2q := close_list l_q W2 in
    let W3 := reinstate W2q [LNonHeap a_stk2] in
    extract_temporaries_condition W0 (l_revoked ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    l_q ## (LNonHeap <$> finz.seq_between csp_b csp_e) ->
    finz.seq_between b e ## finz.seq_between csp_b csp_e ->
    (a_stk1 + (1 + StackEntry_reserved_space))%a = Some csp_e ->
    (a_stk2 + 1)%a = Some a_stk1 ->
    (csp_b <= a_stk2)%a ->
    ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    interp W0 C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)) -∗
    interp W0 C wct1 -∗
    world_interp W2q C -∗
    interp W2 C (WCap t p g b e (finz.max b e) @@? π) -∗
    StackRevokedResources W0 C (finz.seq_between csp_b csp_e) -∗
    a_stk2 ↦ₐ WInt 0 -∗
    £ 1
    ={⊤}=∗
    world_interp W3 C ∗
    interp W3 C (WCap t p g b e (finz.max b e) @@? π) ∗
    interp W3 C (Cap RWL Local a_stk2 a_stk1 a_stk2) ∗
    (if is_sealed_with_o wct1.(lw) ot_switcher then interp W3 C wct1 else True) ∗
    StackRevokedResources W3 C (stk_free csp_b csp_e a_stk2) ∗
    ⌜revoked_addresses W3 (stk_free csp_b csp_e a_stk2)⌝ ∗
    ⌜related_sts_priv_world W0 W3⌝ ∗
    ⌜std W3 !! LNonHeap a_stk2 = Some Temporary⌝.
  Proof.
    intros W2 W2q W3.
    iIntros (Hextract Hq_stack Hno_overlap Hastk1 Hastk2 Hcsp_b_astk2)
      "#Hseal #Hinterp_csp #Hinterp_wct1 Hworld_interp_C #Hinterp_object Hstack_revoked Hastk2 Hlc".
    unfold StackEntry_reserved_space in Hastk1.
    destruct Hextract as [Hl_revoked_nodup Hl_revoked_temporaries].
    set (temps := so_object_temporaries W0 π b e) in *.
    assert (related_sts_priv_world W0 (revoke W0)) as Hpriv_W0_W1
      by apply revoke_related_sts_priv_world.
    assert (related_sts_pub_world (revoke W0) W2) as Hpub_W1_W2
      by apply close_list_related_sts_pub.
    assert (related_sts_pub_world W2 W2q) as Hpub_W2_W2q
      by apply close_list_related_sts_pub.
    assert (related_sts_priv_world W0 W2q) as Hpriv_W0_W2q.
    { eapply related_sts_priv_pub_trans_world; eauto.
      eapply related_sts_pub_trans_world; eauto. }
    assert (finz.seq_between csp_b csp_e ## temps) as Hstack_temps.
    { rewrite elem_of_disjoint in Hno_overlap |- *.
      intros x Hx_stk Hx_temp.
      eapply Hno_overlap; last exact Hx_stk.
      subst temps.
      by apply list_elem_of_filter in Hx_temp as [_ Hx_object].
    }
    assert (std W0 !! LNonHeap a_stk2 = Some Temporary) as Ha_stk2_W0.
    { apply Hl_revoked_temporaries.
      apply elem_of_app; right.
      apply elem_of_LNonHeap_fmap, elem_of_finz_seq_between;
        solve_addr+Hastk1 Hastk2 Hcsp_b_astk2.
    }
    assert (std W2q !! LNonHeap a_stk2 = Some Revoked) as Ha_stk2_W2q.
    { subst W2q W2.
      rewrite close_list_lookup_not_in.
      2: { rewrite elem_of_disjoint in Hq_stack.
           intros Hx. eapply Hq_stack; eauto.
           apply elem_of_LNonHeap_fmap, elem_of_finz_seq_between;
             solve_addr+Hastk1 Hastk2 Hcsp_b_astk2. }
      rewrite close_list_lookup_not_in.
      - apply revoke_lookup_Monotemp. exact Ha_stk2_W0.
      - intro Ha'.
        apply LNonHeap_elem_of_addr_key_fmap in Ha'.
        rewrite elem_of_disjoint in Hstack_temps.
        eapply Hstack_temps; eauto.
        apply elem_of_finz_seq_between; solve_addr+Hastk1 Hastk2 Hcsp_b_astk2.
    }

    (* Insert the allocated stack object [a_stk2] in the world *)
    iMod (stack_object_reinstate_fresh_object
            W0 W2q C csp_b csp_e (stk_start_a csp_b csp_e) a_stk2 a_stk1
           with "[$Hinterp_csp $Hworld_interp_C $Hastk2 $Hlc]")
      as "(Hworld_interp_C & %Hpub_W2q_W3 & %Ha_stk2_W3 & #Hinterp_z)"; eauto.
    { split; first exact Hcsp_b_astk2.
      split; solve_addr+Hastk1 Hastk2. }
    assert (related_sts_priv_world W0 W3) as Hpriv_W0_W3.
    { eapply related_sts_priv_pub_trans_world; eauto. }
    assert (related_sts_pub_world W2 W3) as Hpub_W2_W3.
    { eapply related_sts_pub_trans_world; eauto. }
    iModIntro.
    iFrame "Hworld_interp_C Hinterp_z".
    iSplit.
    { iApply (interp_monotone_same_heap W2 W3 C _ with "[] Hinterp_object"); eauto. }

    (* The callback is safe to share in [W3] *)
    iSplit.
    { destruct (is_sealed_with_o wct1.(lw) ot_switcher) eqn:His_sealed; last done.
      destruct wct1 as [ [| [|] | |] π1]; try discriminate.
      simpl in His_sealed; apply Z.eqb_eq, finz_to_z_eq in His_sealed as ->.
      iApply (interp_monotone_sd_same_heap W0 W3 with "[] Hseal Hinterp_wct1"); eauto.
    }

    (* The stack frame of the callee is still revoked *)
    iEval (rewrite (finz_seq_between_split csp_b a_stk2 csp_e);
      last solve_addr+Hastk1 Hastk2 Hcsp_b_astk2) in "Hstack_revoked".
    iEval (rewrite StackRevokedResources_app) in "Hstack_revoked".
    iDestruct "Hstack_revoked" as "[Hstack_revoked _]".
    iSplitL; first (iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto).
    iPureIntro.
    split; last done.
    apply Forall_forall; intros x Hx.
    apply elem_of_finz_seq_between in Hx; unfold stk_free_b, stk_free_e in Hx.
    subst W3 W2q W2.
    rewrite close_list_lookup_not_in.
    2: { intros Hx'; apply list_elem_of_singleton in Hx'; simplify_eq.
         solve_addr+Hx. }
    rewrite close_list_lookup_not_in.
    2: { intro Hxq.
         rewrite elem_of_disjoint in Hq_stack.
         eapply Hq_stack; eauto.
         apply elem_of_LNonHeap_fmap, elem_of_finz_seq_between.
         solve_addr+Hx Hastk1 Hastk2. }
    rewrite close_list_lookup_not_in.
    2: { intro Hx'.
         apply LNonHeap_elem_of_addr_key_fmap in Hx'.
         apply Hstack_temps in Hx'; first done.
         apply elem_of_finz_seq_between.
         solve_addr+Hx Hastk1 Hastk2.
    }
    apply revoke_lookup_Monotemp.
    apply Hl_revoked_temporaries.
    apply elem_of_app; right.
    apply elem_of_LNonHeap_fmap, elem_of_finz_seq_between.
    solve_addr+Hx Hastk1 Hastk2.
  Qed.

  (** The argument registers of [f] other than [in] and [g] are cleared. *)
  Lemma so_args_zero (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    (∀ (r : RegName) (v : LWord),
        ⌜r ∉ ({[cra; cgp; csp]} ∪ dom_arg_rmap 2 : gset RegName)⌝ →
        ⌜rmap !! r = Some v⌝ →
        ⌜v = WInt 0⌝ : iProp Σ) -∗
    ⌜∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) →
         rmap !! r = Some (lword_of_word (WInt 0))⌝.
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
  Lemma so_call_args W C (rmap : LReg) (wca0 wca1 : LWord) :
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ca0 ; ca1 ; ct0 ]} ->
    (∀ r, r ∈ ({[ ca2 ; ca3 ; ca4 ; ca5 ]} : gset RegName) →
          rmap !! r = Some (lword_of_word (WInt 0))) ->
    na_inv (tpool th) Ntstack trusted_stack_inv -∗
    switcher_static -∗
    ca0 ↦ᵣ[th] wca0 -∗
    interp W C wca0 -∗
    ca1 ↦ᵣ[th] wca1 -∗
    interp W C wca1 -∗
    ct0 ↦ᵣ[th] switcher_entry_call -∗
    regs[th] rmap -∗
    ∃ arg_rmap rmap',
      ⌜ dom rmap' = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ⌝ ∗
      ⌜ is_arg_rmap arg_rmap 8 ⌝ ∗
      ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ[th] warg ∗ interp W C warg) ∗
      regs[th] rmap'.
  Proof.
    iIntros (Hrmap_dom Hzero) "#Hswitcher #Hswitcher_static Hca0 #Hinterp_ca0 Hca1 #Hinterp_ca1 Hct0 Hrmap".
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]".
    { apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]".
    { rewrite lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]".
    { rewrite !lookup_delete_ne //; apply Hzero; set_solver+. }
    iExists {[ ca0 := wca0; ca1 := wca1; ca2 := lword_of_word (WInt 0);
               ca3 := lword_of_word (WInt 0); ca4 := lword_of_word (WInt 0);
               ca5 := lword_of_word (WInt 0); ct0 := lword_of_word switcher_entry_call ]}, _.
    iFrame "Hrmap".
    iSplit.
    { iPureIntro.
      rewrite !dom_delete_L Hrmap_dom /dom_arg_rmap.
      set_solver+.
    }
    iSplit; first by rewrite /is_arg_rmap.
    iAssert (interp W C (WInt 0)) as "#Hinterp_0"; first iApply interp_int.
    iAssert (interp W C switcher_entry_call) as "#Hinterp_switcher".
    { iApply interp_switcher_call. iFrame "Hswitcher Hswitcher_static". }
    repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
    done.
  Qed.

  (** ** Call to the adversary [C.adv] in [run]

      Revoke the world [W0], to get the stack frame. The entry point of the
      adversary is still safe in the revoked world. *)
  Lemma so_world_run_call W0 C (csp_b csp_e : Addr) (C_f : Sealable) :
    ot_switcher ↪ₒ{SealGlobal} ot_switcher_propC -∗
    interp W0 C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)) -∗
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
    iIntros "#Hseal #Hinterp_csp #Hinterp_C_f Hworld_interp_C".
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld_interp_C]")
      as (l) "(_ & Hworld_interp_C & Hstack_revoked & >%Hstack_revoked
               & >[%stk_mem Hstk] & _ & _)".
    pose proof (revoke_related_sts_priv_world W0) as Hpriv_W0_W1.
    iModIntro.
    iExists stk_mem.
    iFrame "Hworld_interp_C Hstk".
    iSplit.
    { iApply (interp_monotone_sd_same_heap with "[] Hseal Hinterp_C_f").
      by iPureIntro. }
    iSplit; last done.
    iNext.
    iApply (StackRevokedResources_mono_priv with "Hstack_revoked"); eauto.
  Qed.

End SO_World_Call.
