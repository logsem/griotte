From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary monotone_binary interp_weakening_binary fundamental_binary.
From griotte Require Import region_invariants_revocation_binary memory_region_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Export switcher_helpers_cframe_binary.

(** * Helper lemmas for the switcher proofs of the binary model

    The stack frames of both runs have the same bounds; the points-to
    predicates and the contents of both memories are handled side by side. *)

Section switcher_helper.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma world_interp_stack_fixing
    (Wcur W0 : WORLD) (C : CmptName)
    (a_stk4 b_stk csp_b csp_e : Addr) (l : list Addr)
    ccrel
    :

    let a_stk := (csp_b ^+ -4)%a in
    let Wfixed := close_list (l ++ finz.seq_between csp_b csp_e) Wcur in
    let closing_region := finz.seq_between csp_b csp_e in

    ((csp_b ^+ -4) ^+ 3 < csp_e)%a ->
    (b_stk <= csp_b ^+ -4)%a ->
    (csp_b ^+ -4 + 4)%a = Some a_stk4 ->

    related_sts_pub_world W0 Wfixed ->
    interp W0 C
      (WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e a_stk,
       WCap RWL Local (if is_untrusted_caller ccrel then b_stk else (a_stk ^+ 4)%a) csp_e a_stk) -∗
    world_interp Wcur C -∗
    [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] -∗
    [[a_stk,a_stk4]]↣ₐ[[region_addrs_zeroes a_stk a_stk4]] -∗
    [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]] -∗
    [[a_stk4,csp_e]]↣ₐ[[region_addrs_zeroes a_stk4 csp_e]] -∗

    CloseRes_gen Wcur Wfixed C csp_b csp_e a_stk l ccrel -∗

    £ 1 -∗
    |={⊤}=>
          world_interp Wfixed C
          ∗ (if (is_untrusted_caller ccrel)
             then True
             else [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]
                  ∗ [[a_stk,a_stk4]]↣ₐ[[region_addrs_zeroes a_stk a_stk4]]
            )
  .
  Proof.
    intros a_stk Wfixed closing_region.
    iIntros (He_a1 Hb_a4 Ha_stk4 Hrelated_pub_W0_Wfixed)
      "#Hinterp_callee_wstk Hworld_interp Hstk' Hsstk' Hstk Hsstk Hrevoked Hlc''".

    iAssert ( ▷( close_list_resources_gen C Wcur (l++(finz.seq_between csp_b csp_e)) (finz.seq_between csp_b csp_e) false) )%I
      with "[Hstk Hsstk]" as "Hstk".
    {
      replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
      replace (a_stk ^+4)%a with csp_b by (subst a_stk; solve_addr+Ha_stk4 He_a1).
      iAssert (interp W0 C (WCap RWL Local csp_b csp_e a_stk, WCap RWL Local csp_b csp_e a_stk)) as "Hvalid".
      {
        rewrite /is_untrusted_caller_frm /=; destruct (is_untrusted_caller ccrel); auto.
        iApply (interp_weakening _ _ _ _ _ _ b_stk csp_b with "[] Hinterp_callee_wstk"); auto.
        + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
        + subst a_stk; solve_addr+Ha_stk4 He_a1 Hb_a4.
        + iApply fundamental_ih.
      }

      iDestruct (write_allowed_inv_full_cap with "Hvalid") as "-#H"; auto.
      iClear "#";clear-Hrelated_pub_W0_Wfixed.
      rewrite /region_pointsto /spec_region_pointsto.
      rewrite !big_sepL2_replicate_r; try by rewrite finz_seq_between_length.
      iDestruct (big_sepL_sep with "[$Hstk $Hsstk]") as "Hstk".
      iDestruct (big_sepL_sep with "[$Hstk $H]") as "H".
      iNext.
      iApply (big_sepL_impl with "H").
      iIntros "!> %%% [[Hv Hsv] (%&%&%&%&Hrel&#Hzcond&#Hrcond&#Hwcond&Hmono)]".
      iExists x0, (safeC x1). iFrame.
      iSplit.
      { iPureIntro; intros W. rewrite /persistent_cond in H1.
        specialize (H1 W).
        apply _.
      }
      iExists W0. iSplit; first done.
      iExists (WInt 0, WInt 0). iFrame.
      iSplit; first (iPureIntro; eapply notisO_flowsfrom; eauto).
      iSplit.
      { erewrite isWL_flowsto;eauto.
        rewrite /future_pub_mono.
        iIntros "!> %%% H".
        iApply "Hzcond"; auto.
      }
      iApply "Hwcond"; iApply interp_int.
    }
    iDestruct (lc_fupd_elim_later with "[$] [$Hstk]") as ">Hstk".

    rewrite /CloseRes_gen.
    destruct (is_untrusted_caller ccrel).
    - (* caller is untrusted, we need to re-instate the whole stack frame *)
      iMod (reinstate_close_list_gen _ _ (l++closing_region) with
             "[$Hworld_interp Hrevoked Hstk Hstk' Hsstk']") as "Hworld_interp"; last by iFrame.
      iDestruct "Hrevoked" as (l') "(%Hl & Hclose_list_res & (Hrev0 & Hrev1 & Hrev2 & Hrev3 & _) )".
      rewrite /close_list_resources_gen.
      rewrite big_sepL_app.
      iSplitR "Hstk"; last done.
      iApply big_opL_permutation; first (symmetry; done).
      rewrite big_sepL_app.
      iFrame.
      cbn in *.
      replace a_stk4 with (a_stk ^+4)%a by (subst a_stk; solve_addr+Ha_stk4 He_a1).
      rewrite /region_addrs_zeroes.
      replace (finz.dist a_stk (a_stk ^+ 4)%a) with 4; first cbn.
      2: { do 4 (rewrite finz_dist_S; last (subst a_stk; solve_addr+Ha_stk4)).
           rewrite finz_dist_0; last (subst a_stk; solve_addr+Ha_stk4).
           done.
      }
      iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk0 Hstk']"
      ; [ transitivity ( Some (a_stk ^+ 1)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk1 Hstk']"
      ; [ transitivity ( Some (a_stk ^+ 2)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk2 Hstk']"
      ; [ transitivity ( Some (a_stk ^+ 3)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (region_pointsto_cons with "Hstk'") as "[Ha_stk3 _]"
      ; [ transitivity ( Some (a_stk ^+ 4)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (spec_region_pointsto_cons with "Hsstk'") as "[Hsa_stk0 Hsstk']"
      ; [ transitivity ( Some (a_stk ^+ 1)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (spec_region_pointsto_cons with "Hsstk'") as "[Hsa_stk1 Hsstk']"
      ; [ transitivity ( Some (a_stk ^+ 2)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (spec_region_pointsto_cons with "Hsstk'") as "[Hsa_stk2 Hsstk']"
      ; [ transitivity ( Some (a_stk ^+ 3)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      iDestruct (spec_region_pointsto_cons with "Hsstk'") as "[Hsa_stk3 _]"
      ; [ transitivity ( Some (a_stk ^+ 4)%a ); subst a_stk; solve_addr+Ha_stk4
        | subst a_stk; solve_addr+Ha_stk4 He_a1
        |].
      rewrite /close_addr_resources_gen.
      iSplitL "Hrev0 Ha_stk0 Hsa_stk0".
      { iDestruct "Hrev0" as " (%p & %P & $ & ($ & $ & HW) & $)".
        iDestruct "HW" as (W') "[% HW]".
        iExists W'. iSplit; first done. iFrame.
      }
      iSplitL "Hrev1 Ha_stk1 Hsa_stk1".
      { iDestruct "Hrev1" as " (%p & %P & $ & ($ & $ & HW) & $)".
        iDestruct "HW" as (W') "[% HW]".
        iExists W'. iSplit; first done. iFrame.
      }
      iSplitL "Hrev2 Ha_stk2 Hsa_stk2".
      { iDestruct "Hrev2" as " (%p & %P & $ & ($ & $ & HW) & $)".
        iDestruct "HW" as (W') "[% HW]".
        iExists W'. iSplit; first done. iFrame.
      }
      iSplitL "Hrev3 Ha_stk3 Hsa_stk3".
      { iDestruct "Hrev3" as " (%p & %P & $ & ($ & $ & HW) & $)".
        iDestruct "HW" as (W') "[% HW]".
        iExists W'. iSplit; first done. iFrame.
      }
      done.

    - (* caller is trusted, we need only need re-instate callee's stack frame *)
      iFrame "Hstk' Hsstk'".
      iMod (reinstate_close_list_gen _ _ (l++closing_region) with
             "[$Hworld_interp Hrevoked Hstk]") as "Hworld_interp"; last by iFrame.
      rewrite /close_list_resources_gen big_sepL_app.
      iFrame.
  Qed.


  (** Jump to a safe return address [wret], in both runs, with safe
      callee-save registers [cgp], [cs0], [cs1], [csp], safe return values
      [ca0], [ca1], and cleared registers. *)
  Lemma switcher_jump_to_caller_spec
    (W : WORLD) (C : CmptName) (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : Reg) (wret wcgp wcs0 wcs1 wcsp wca0 wca1 : Word * Word) :
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    frame_match Ws Cs stk W C ->

    spec_ctx -∗
    interp W C wret -∗
    interp W C wcgp -∗
    interp W C wcs0 -∗
    interp W C wcs1 -∗
    interp W C wcsp -∗
    interp W C wca0 -∗
    interp W C wca1 -∗
    PC ↦ᵣ updatePcPerm wret.1 -∗
    PC ↣ᵣ updatePcPerm wret.2 -∗
    cra ↦ᵣ wret.1 -∗
    cra ↣ᵣ wret.2 -∗
    cgp ↦ᵣ wcgp.1 -∗
    cgp ↣ᵣ wcgp.2 -∗
    cs0 ↦ᵣ wcs0.1 -∗
    cs0 ↣ᵣ wcs0.2 -∗
    cs1 ↦ᵣ wcs1.1 -∗
    cs1 ↣ᵣ wcs1.2 -∗
    csp ↦ᵣ wcsp.1 -∗
    csp ↣ᵣ wcsp.2 -∗
    ca0 ↦ᵣ wca0.1 -∗
    ca0 ↣ᵣ wca0.2 -∗
    ca1 ↦ᵣ wca1.1 -∗
    ca1 ↣ᵣ wca1.2 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝) -∗
    world_interp W C -∗
    interp_continuation stk Ws Cs -∗
    cstack_frag (map fst stk) -∗
    cstack_frag_spec (map snd stk) -∗
    ⤇ Seq (Instr Executable) -∗
    na_own cerise_nais ⊤ -∗
    £ 1 -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom Hframe) "#Hspec #Hwret #Hwcgp #Hwcs0 #Hwcs1 #Hwcsp #Hwca0 #Hwca1
      HPC HsPC Hcra Hscra Hcgp Hscgp Hcs0 Hscs0 Hcs1 Hscs1 Hcsp Hscsp Hca0 Hsca0 Hca1 Hsca1
      Hrmap Hworld_interp HK Hcstk Hcstk_spec Hj Hna Hlc".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap Hsmap]".
    iDestruct (big_sepM_sep with "Hsmap") as "[Hsmap %Hrmap_zero]".
    iInsertList "Hrmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
    iInsertListSpec "Hsmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
    iDestruct (big_sepM_insert with "[$Hrmap $HPC]") as "Hrmap".
    { apply not_elem_of_dom; rewrite !dom_insert_L Hdom; set_solver+. }
    iDestruct (big_sepM_insert with "[$Hsmap $HsPC]") as "Hsmap".
    { apply not_elem_of_dom; rewrite !dom_insert_L Hdom; set_solver+. }
    destruct wret as [wret swret].
    iDestruct (interp_updatePcPerm with "Hwret") as "Hinterp_wret".
    iMod (lc_fupd_elim_later with "Hlc Hinterp_wret") as "Hinterp_wret'".
    rewrite /interp_expression /interp_expr /=.
    match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => set (rmap' := m) end.
    match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↣ᵣ w)%I ] => set (smap' := m) end.
    iApply ("Hinterp_wret'" $! stk Ws Cs rmap' smap'
             with "[- $Hspec $Hworld_interp $HK $Hna $Hcstk $Hcstk_spec $Hj]").
    rewrite /registers_pointsto /spec_registers_pointsto /rmap' /smap' !insert_insert_eq.
    iFrame "Hrmap Hsmap".
    iSplit; last (iPureIntro; done).
    iSplit; [|iSplit].
    - iIntros (r); iPureIntro.
      clear -Hdom.
      destruct (decide (r = PC)); simplify_map_eq; first done.
      destruct (decide (r = csp)); simplify_map_eq; first done.
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first done.
      destruct (decide (r = ca0)); simplify_map_eq; first done.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      apply elem_of_dom.
      rewrite Hdom.
      pose proof all_registers_s_correct.
      set_solver.
    - iIntros (r); iPureIntro.
      clear -Hdom.
      destruct (decide (r = PC)); simplify_map_eq; first done.
      destruct (decide (r = csp)); simplify_map_eq; first done.
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first done.
      destruct (decide (r = ca0)); simplify_map_eq; first done.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      apply elem_of_dom.
      rewrite Hdom.
      pose proof all_registers_s_correct.
      set_solver.
    - iIntros (r rv1 rv2 HrPC Hr1 Hr2); cbn in Hr1, Hr2.
      destruct (decide (r = csp)); simplify_map_eq; first (by destruct wcsp).
      destruct (decide (r = cs1)); simplify_map_eq; first (by destruct wcs1).
      destruct (decide (r = cs0)); simplify_map_eq; first (by destruct wcs0).
      destruct (decide (r = ca1)); simplify_map_eq; first (by destruct wca1).
      destruct (decide (r = ca0)); simplify_map_eq; first (by destruct wca0).
      destruct (decide (r = cgp)); simplify_map_eq; first (by destruct wcgp).
      destruct (decide (r = cra)); simplify_map_eq; first done.
      repeat match goal with H : rmap !! r = Some ?v |- _ =>
               apply Hrmap_zero in H; cbn in H; subst v end.
      iApply interp_int.
  Qed.

End switcher_helper.
