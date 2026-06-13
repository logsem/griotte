From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import switcher_preamble assert_spec.
From griotte Require Import rules seal_store call_stack.
From griotte Require Import mkregion_helpers memory_region disjoint_regions_tactics.
From griotte Require Import switcher_adequacy compartment_layout.


Section adequacy_helpers.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters} .

    Lemma initialise_assert_compartment
      {E : coPset} (assert_cmpt : cmptAssert) (assertN flagN : namespace) :
      ([∗ map] a↦v ∈ mk_initial_assert assert_cmpt, a ↦ₐ v)
      ={E}=∗
      inv flagN (flag_assert assert_cmpt ↦ₐ WInt 0) ∗
      na_inv cerise_nais assertN
        (assert_inv (b_assert assert_cmpt) (e_assert assert_cmpt) (flag_assert assert_cmpt)).
    Proof.
      iIntros "Hcmpt_assert".
      rewrite /mk_initial_assert.
      iDestruct (big_sepM_union with "Hcmpt_assert") as "[Hassert Hassert_flag]".
      { eapply cmpt_assert_flag_mregion_disjoint ; eauto. }
      iDestruct (big_sepM_union with "Hassert") as "[Hassert Hassert_cap]".
      { eapply cmpt_assert_cap_mregion_disjoint ; eauto. }
      rewrite /cmpt_assert_flag_mregion.
      rewrite /mkregion.
      rewrite finz_seq_between_singleton.
      2: { pose proof (assert_flag_size assert_cmpt) as H; solve_addr+H. }
      cbn.
      iDestruct (big_sepM_insert with "Hassert_flag") as "[Hassert_flag _]"; first done.
      iMod (inv_alloc flagN E (flag_assert assert_cmpt ↦ₐ WInt 0%Z) with "Hassert_flag")%I
        as "#Hinv_assert_flag".
      rewrite /cmpt_assert_cap_mregion.
      rewrite /mkregion.
      rewrite finz_seq_between_singleton.
      2: { pose proof (assert_cap_size assert_cmpt) as H; solve_addr+H. }
      cbn.
      iDestruct (big_sepM_insert with "Hassert_cap") as "[Hassert_cap _]"; first done.

      rewrite /cmpt_assert_code_mregion.
      iDestruct (mkregion_prepare with "[Hassert]") as ">Hassert"; auto.
      { apply (assert_code_size assert_cmpt). }
      iAssert (assert_inv
                 (b_assert assert_cmpt)
                 (e_assert assert_cmpt)
                 (flag_assert assert_cmpt))
        with "[Hassert Hassert_cap]" as "Hassert".
      { rewrite /assert_inv. iExists (cap_assert assert_cmpt).
        rewrite /codefrag /region_pointsto.
        replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)%a
          with (cap_assert assert_cmpt).
        2: { pose proof (assert_code_size assert_cmpt); solve_addr+H. }
        iFrame.
        iSplit; first (iPureIntro ; apply (assert_code_size assert_cmpt)).
        iSplit; iPureIntro.
        + apply (assert_cap_size assert_cmpt).
        + by rewrite (assert_flag_size assert_cmpt).
      }
      iMod (na_inv_alloc cerise_nais _ assertN _ with "Hassert") as "#Hassert".
      iModIntro; iFrame "#".
    Qed.

    Lemma initialise_switcher_compartment
      {E : coPset} (switcher_cmpt : cmptSwitcher) (switcherN : namespace) :
      let swlayout :=  (cmptSwitcher_switcherLayout switcher_cmpt) in
      ([∗ map] k↦y ∈ mk_initial_switcher switcher_cmpt, k ↦ₐ y) -∗
      can_alloc_pred (ot_switcher switcher_cmpt) -∗
      cstack_full [] -∗
      mtdc ↦ₛᵣ WCap RWL Local (b_trusted_stack switcher_cmpt) (e_trusted_stack switcher_cmpt) (b_trusted_stack switcher_cmpt)
      ={E}=∗
      seal_pred (ot_switcher switcher_cmpt) ot_switcher_propC ∗
      na_inv cerise_nais switcherN switcher_inv ∗
      [[ (b_stack switcher_cmpt), (e_stack switcher_cmpt) ]] ↦ₐ [[ ( stack_content switcher_cmpt ) ]].
    Proof.
      intros.
      iIntros "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc".
      rewrite /mk_initial_switcher.
      iDestruct (big_sepM_union with "Hcmpt_switcher") as "[Hswitcher Hstack]".
      { eapply cmpt_switcher_stack_mregion_disjoint ; eauto. }
      iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher Htrusted_stack]".
      { eapply cmpt_switcher_trusted_stack_mregion_disjoint ; eauto. }

      rewrite /cmpt_switcher_code_mregion.
      iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
      { eapply cmpt_switcher_code_stack_mregion_disjoint ; eauto. }
      iEval (rewrite /mkregion) in "Hswitcher_sealing".
      rewrite finz_seq_between_singleton.
      2: { apply switcher_call_entry_point. }
      iEval (cbn) in "Hswitcher_sealing".
      iDestruct (big_sepM_insert with "Hswitcher_sealing") as "[Hswitcher_sealing _]"; first done.
      iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
      { apply switcher_size. }
      rewrite /cmpt_switcher_trusted_stack_mregion.
      iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
      { apply (trusted_stack_size switcher_cmpt). }
      iMod (seal_store_update_alloc _ ( ot_switcher_propC ) with "Hseal_store") as "#Hsealed_pred_ot_switcher".
      iAssert ( switcher_preamble.switcher_inv )
        with "[Hswitcher Hswitcher_sealing Htrusted_stack Hcstk_full Hmtdc]" as "Hswitcher".
      {
        rewrite /switcher_inv /codefrag /region_pointsto /=.
        replace ((a_switcher_call switcher_cmpt) ^+ length switcher_instrs)%a
          with (e_switcher switcher_cmpt).
        2: { pose proof (switcher_size switcher_cmpt) as H.
             solve_addr+H.
        }
        iFrame "∗#".
        iExists (tl (trusted_stack_content switcher_cmpt)).
        iSplitR; first (iPureIntro; apply (ot_switcher_size switcher_cmpt)).
        pose proof (trusted_stack_content_base_zeroed switcher_cmpt) as Htstk_head.
        pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
        destruct (trusted_stack_content switcher_cmpt); cbn in Htstk_head; simplify_eq.
        rewrite finz_seq_between_cons; last solve_addr+Htstk_size.
        iDestruct "Htrusted_stack" as "[Hbase_stack Htrusted_stack]".
        iFrame.
        iSplitL; last (iPureIntro ; by rewrite finz_add_0).
        iSplit; iPureIntro; solve_addr.
      }
      iMod (na_inv_alloc cerise_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".

      iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
      { apply (stack_size switcher_cmpt). }
    Qed.

    Lemma initialise_compartment ( C_cmpt : cmpt ) :
      let PCC := WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ cmpt_data C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ CGP ∗
      [[ (cmpt_exp_tbl_entries_start C_cmpt), (cmpt_exp_tbl_entries_end C_cmpt) ]] ↦ₐ [[ cmpt_exp_tbl_entries C_cmpt ]].
    Proof.
      intros PCC CGP.
      iIntros "Hcmpt_C".
      iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
      iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
      { eapply cmpt_exp_tbl_disjoint ; eauto. }
      iDestruct (big_sepM_union with "HC") as "[HC_code HC_data]".
      { eapply cmpt_cgp_disjoint ; eauto. }
      rewrite /cmpt_pcc_mregion.
      iDestruct (big_sepM_union with "HC_code") as "[HC_imports HC_code]".
      { eapply cmpt_code_disjoint ; eauto. }
      iEval (rewrite /mkregion) in "HC_imports".
      rewrite /cmpt_cgp_mregion.
      iDestruct (mkregion_prepare with "[HC_code]") as ">HC_code"; auto.
      { apply (cmpt_code_size C_cmpt). }
      iDestruct (mkregion_prepare with "[HC_data]") as ">HC_data"; auto.
      { apply (cmpt_data_size C_cmpt). }
      iDestruct (mkregion_prepare with "[HC_imports]") as ">HC_imports"; auto.
      { by pose proof (cmpt_import_size C_cmpt) as H ; cbn in *. }

      iEval (rewrite /cmpt_exp_tbl_mregion) in "HC_etbl".
      iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl HC_etbl_entries]".
      { eapply cmpt_exp_tbl_entries_disjoint. }
      iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl_pcc HC_etbl_cgp]".
      { eapply cmpt_exp_tbl_pcc_cgp_disjoint. }
      iDestruct (mkregion_prepare with "[HC_etbl_entries]") as ">HC_etbl_entries"; auto.
      { apply cmpt_exp_tbl_entries_size. }
      iDestruct (mkregion_prepare with "[HC_etbl_pcc]") as ">HC_etbl_pcc"; auto.
      { cbn; apply cmpt_exp_tbl_pcc_size. }
      iDestruct (mkregion_prepare with "[HC_etbl_cgp]") as ">HC_etbl_cgp"; auto.
      { cbn; apply cmpt_exp_tbl_cgp_size. }
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc C_cmpt))
      ; last (apply cmpt_exp_tbl_pcc_size).
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp C_cmpt))
      ; last (apply cmpt_exp_tbl_cgp_size).
      rewrite !big_sepL2_singleton.
      iFrame.
      done.
    Qed.

    Lemma initialise_adversary_compartment {E : coPset} ( C_cmpt : cmpt ) ( C : CmptName ) :
      let PCC := WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let exp_tbl_addrs := (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ y)
      ={E}=∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ cmpt_data C_cmpt ]] ∗
      inv (export_table_PCCN (nroot.@C)) (cmpt_exp_tbl_pcc C_cmpt ↦ₐ PCC) ∗
      inv (export_table_CGPN (nroot.@C)) (cmpt_exp_tbl_cgp C_cmpt ↦ₐ CGP) ∗
      ([∗ list] a;v ∈ exp_tbl_addrs ; cmpt_exp_tbl_entries C_cmpt,
         inv (export_table_entryN (nroot .@ C) a) (a ↦ₐ v)).
    Proof.
      intros PCC CGP exp_tbl_addrs.
      iIntros "Hcmpt_C".
      iMod (initialise_compartment with "Hcmpt_C")
        as "(HC_imports & HC_code & HC_data & HC_etbl_pcc & HC_etbl_cgp & HC_etbl_entries)".
      iFrame.

      iMod (inv_alloc (export_table_PCCN (nroot .@ C)) E _ with "HC_etbl_pcc")%I as "$".
      iMod (inv_alloc (export_table_CGPN (nroot .@ C)) E _ with "HC_etbl_cgp")%I as "$".

      iStopProof.
      subst exp_tbl_addrs.
      rewrite /region_pointsto.
      generalize (cmpt_exp_tbl_entries C_cmpt) as lv.
      generalize (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) as la.
      clear PCC CGP.
      induction la; iIntros (lv) "H"; first done.
      iDestruct (big_sepL2_length with "H") as "%Hlen".
      destruct lv as [|v lv]; simplify_eq.
      iDestruct "H" as "[H IH]".
      iMod (IHla with "IH") as "$".
      iMod (inv_alloc (export_table_entryN (nroot .@ C) a) E _ with "H")%I as "$".
      done.
    Qed.

End adequacy_helpers.
