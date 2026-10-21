From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import switcher_preamble assert_spec.
From griotte Require Import rules call_stack.
From griotte Require Import mkregion_helpers memory_region disjoint_regions_tactics.
From griotte Require Import switcher_adequacy compartment_layout.
From griotte Require Import allocator_resources.


Section adequacy_helpers.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters} .

    Lemma initialise_assert_compartment
      {E : coPset} (assert_cmpt : cmptAssert) (flagN : namespace) :
      ([∗ map] a↦v ∈ mk_initial_assert assert_cmpt, a ↦ₐ lword_of_word v)
      ={E}=∗
      inv flagN (flag_assert assert_cmpt ↦ₐ WInt 0) ∗
      assert_static (b_assert assert_cmpt) (e_assert assert_cmpt) (flag_assert assert_cmpt).
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
      iAssert (codefrag (b_assert assert_cmpt) assert_subroutine_instrs)
        with "[Hassert]" as "Hassert".
      { rewrite /codefrag /region_pointsto big_sepL2_fmap_r.
        replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)%a
          with (cap_assert assert_cmpt).
        2: { pose proof (assert_code_size assert_cmpt); solve_addr+H. }
        iFrame.
      }
      iMod (codefrag_persist with "Hassert") as "#Hassert".
      iMod (pointsto_persist with "Hassert_cap") as "#Hassert_cap".
      iModIntro. iFrame "Hinv_assert_flag".
      rewrite /assert_static.
      iSplit; first (iPureIntro; apply (assert_code_nonheap assert_cmpt)).
      iExists (cap_assert assert_cmpt).
      iFrame "Hassert Hassert_cap".
      iSplit; first (iPureIntro ; apply (assert_code_size assert_cmpt)).
      iSplit; iPureIntro.
      + apply (assert_cap_size assert_cmpt).
      + by rewrite (assert_flag_size assert_cmpt).
    Qed.

    Lemma initialise_switcher_compartment
      {E : coPset} (switcher_cmpt : cmptSwitcher) (switcherN : namespace) :
      let swlayout :=  (cmptSwitcher_switcherLayout switcher_cmpt) in
      mtcc_vec = switcher_label_pc "exception_entry_asm" ->
      ([∗ map] k↦y ∈ mk_initial_switcher switcher_cmpt, k ↦ₐ lword_of_word y) -∗
      can_alloc_pred (ot_switcher switcher_cmpt) -∗
      cstack_full [] -∗
      mtdc ↦ₛᵣ WCap true RWL Global (b_trusted_stack switcher_cmpt) (e_trusted_stack switcher_cmpt) (b_trusted_stack switcher_cmpt)
      ={E}=∗
      seal_pred (ot_switcher switcher_cmpt) ot_switcher_propC ∗
      na_inv cerise_nais switcherN switcher_inv ∗
      switcher_static ∗
      [[ (b_stack switcher_cmpt), (e_stack switcher_cmpt) ]] ↦ₐ [[ lword_of_word <$> stack_content switcher_cmpt ]].
    Proof.
      intros swlayout Hmtcc.
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
      iAssert (codefrag (a_switcher_call switcher_cmpt) switcher_instrs)
        with "[Hswitcher]" as "Hswitcher_code".
      {
        rewrite /codefrag /region_pointsto.
        setoid_rewrite big_sepL2_fmap_r.
        replace ((a_switcher_call switcher_cmpt) ^+ length switcher_instrs)%a
          with (e_switcher switcher_cmpt).
        2: { pose proof (switcher_size switcher_cmpt) as H.
             solve_addr+H.
        }
        iFrame.
      }
      iAssert (|==> switcher_preamble.switcher_inv )%I
        with "[Htrusted_stack Hcstk_full Hmtdc]" as ">Hswitcher".
      {
        pose proof (trusted_stack_content_export_table switcher_cmpt)
          as (b_tbl & w_tbl & Hw_tbl & Htbl_cap).
        pose proof (trusted_stack_content_error_count switcher_cmpt) as [n_cnt Hw_cnt].
        pose proof (trusted_stack_content_frameoffset switcher_cmpt) as Hframeoffset.
        pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
        pose proof (trusted_stack_frames_fit switcher_cmpt) as [n Hfit].
        pose proof (ot_switcher_size switcher_cmpt) as Hot.
        iAssert ([[ b_trusted_stack switcher_cmpt, e_trusted_stack switcher_cmpt ]]
                   ↦ₐ [[ lword_of_word <$> trusted_stack_content switcher_cmpt ]])%I
          with "[Htrusted_stack]" as "Htrusted_stack".
        { rewrite /region_pointsto big_sepL2_fmap_r. iFrame. }
        set (b := b_trusted_stack switcher_cmpt) in *.
        set (e := e_trusted_stack switcher_cmpt) in *.
        set (l := trusted_stack_content switcher_cmpt) in *.
        set (i_frameoffset := Z.to_nat TrustedStack_offset_frameoffset) in Hframeoffset.
        set (a_threadID := (b ^+ TrustedStack_offset_threadID)%a).
        (* The entry frame [frames[0]], and its cells *)
        set (a_entry := (b ^+ TrustedStack_offset_frames)%a).
        set (a_export_table := (a_entry ^+ TrustedStackFrame_offset_calleeExportTable)%a).
        set (a_error_count := (a_entry ^+ TrustedStackFrame_offset_errorHandlerCount)%a).
        set (a_next := (a_entry ^+ TrustedStackFrame_size)%a).
        assert (length l = Z.to_nat (tstack_frame_offset (S n))) as Hlen
          by (tstack_unfold; solve_addr).
        (* The save area, the header ([frameoffset] and [threadID]), the entry
           frame and the unused part *)
        assert (drop (S i_frameoffset) l !! 2 = Some w_tbl) as Hw_tbl'.
        { by rewrite lookup_drop -Hw_tbl. }
        assert (drop (S i_frameoffset) l !! 3 = Some (WInt n_cnt)) as Hw_cnt'.
        { by rewrite lookup_drop -Hw_cnt. }
        clear Hw_tbl Hw_cnt.
        rewrite -(take_drop_middle l i_frameoffset _ Hframeoffset).
        revert Hw_tbl' Hw_cnt'.
        assert (length (drop (S i_frameoffset) l)
                = Z.to_nat (TSTACK_HEADER_SZ - 1 + TrustedStackFrame_size * Z.of_nat (S n)))
          as Hlen_rest
          by (rewrite length_drop Hlen; subst i_frameoffset; tstack_unfold; lia).
        destruct (drop (S i_frameoffset) l) as [|w_threadID rest];
          first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_csp rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_export_table rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_error_count rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        intros Hw_tbl' Hw_cnt'. cbn in Hw_tbl', Hw_cnt'. simplify_eq.
        rewrite fmap_app fmap_cons.
        iDestruct (region_pointsto_split _ _ (b ^+ TSTACK_REGFRAME_SZ)%a with "Htrusted_stack")
          as "[Hsave_area Htrusted_stack]".
        { tstack_unfold; solve_addr. }
        { rewrite length_fmap length_take /finz.dist; subst i_frameoffset; tstack_unfold; solve_addr. }
        iDestruct (region_pointsto_cons _ a_threadID with "Htrusted_stack")
          as "[Hframeoffset Htrusted_stack]"; [subst a_threadID; tstack_unfold; solve_addr..|].
        iDestruct (region_pointsto_cons _ a_entry with "Htrusted_stack")
          as "[HthreadID Htrusted_stack]";
          [subst a_threadID a_entry; tstack_unfold; solve_addr..|].
        iDestruct (region_pointsto_cons _ a_export_table with "Htrusted_stack")
          as "[Hcsp Htrusted_stack]";
          [subst a_entry a_export_table; tstack_unfold; solve_addr..|].
        iDestruct (region_pointsto_cons _ a_error_count with "Htrusted_stack")
          as "[Hexport_table Htrusted_stack]";
          [subst a_entry a_export_table a_error_count; tstack_unfold; solve_addr..|].
        iDestruct (region_pointsto_cons _ a_next with "Htrusted_stack")
          as "[Herror_count Htrusted_stack]";
          [subst a_entry a_error_count a_next; tstack_unfold; solve_addr..|].
        iMod (pointsto_persist with "Hexport_table") as "#Hexport_table".
        iModIntro.
        rewrite /switcher_inv.
        iExists a_entry, [], _, _.
        cbn.
        rewrite /TrustedStackFrame_offset_csp finz_add_0_default.
        iFrame "∗ #".
        iSplit; first done.
        iSplit; last (iExists b_tbl; done).
        iPureIntro; subst a_entry b e; tstack_unfold; split; solve_addr.
      }
      iMod (na_inv_alloc cerise_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".
      iMod (codefrag_persist with "Hswitcher_code") as "#Hswitcher_code".
      iMod (pointsto_persist with "Hswitcher_sealing") as "#Hswitcher_sealing".
      iAssert switcher_static as "#Hswitcher_static".
      { rewrite /switcher_static. iFrame "Hswitcher_code Hswitcher_sealing". by iPureIntro. }
      iClear "Hswitcher_code Hswitcher_sealing".

      iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
      { apply (stack_size switcher_cmpt). }
      rewrite /region_pointsto big_sepL2_fmap_r.
      iFrame "∗ Hsealed_pred_ot_switcher Hswitcher Hswitcher_static".
      done.
    Qed.

    Lemma initialise_compartment ( C_cmpt : cmpt ) :
      let PCC := WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let a_eh := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler)%a in
      let a_ehs := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless)%a in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ lword_of_word y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] ∗
      [[ (cmpt_b_static_sealed C_cmpt), (cmpt_e_static_sealed C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_static_sealed C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ CGP ∗
      a_eh ↦ₐ lword_of_word (cmpt_exp_tbl_handler C_cmpt) ∗
      a_ehs ↦ₐ lword_of_word (cmpt_exp_tbl_handler_stackless C_cmpt) ∗
      [[ (cmpt_exp_tbl_entries_start C_cmpt), (cmpt_exp_tbl_entries_end C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_exp_tbl_entries C_cmpt ]].
    Proof.
      intros PCC CGP a_eh a_ehs.
      subst a_eh a_ehs.
      iIntros "Hcmpt_C".
      iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
      iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
      { eapply cmpt_exp_tbl_disjoint ; eauto. }
      iDestruct (big_sepM_union with "HC") as "[HC HC_static_sealed]".
      { eapply cmpt_static_sealed_disjoint ; eauto. }
      rewrite /cmpt_static_sealed_mregion.
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
      iDestruct (mkregion_prepare with "[HC_static_sealed]") as ">HC_static_sealed"; auto.
      { apply (cmpt_static_sealed_size C_cmpt). }
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
      { pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
        pose proof (cmpt_exp_tbl_header_size C_cmpt).
        cbn; solve_addr. }
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc C_cmpt))
      ; last (apply cmpt_exp_tbl_pcc_size).
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
      pose proof (cmpt_exp_tbl_header_size C_cmpt).
      rewrite (finz_seq_between_cons (cmpt_exp_tbl_cgp C_cmpt)); last solve_addr.
      rewrite (finz_seq_between_cons (cmpt_exp_tbl_cgp C_cmpt ^+ 1)%a); last solve_addr.
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp C_cmpt ^+ 1 ^+ 1)%a); last solve_addr.
      replace (cmpt_exp_tbl_cgp C_cmpt ^+ 1)%a
        with (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler)%a
        by (exptbl_unfold; solve_addr).
      replace (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler ^+ 1)%a
        with (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless)%a
        by (exptbl_unfold; solve_addr).
      rewrite !big_sepL2_singleton.
      rewrite /region_pointsto !big_sepL2_fmap_r /=.
      iDestruct "HC_etbl_cgp" as "($ & $ & $ & _)".
      iFrame.
      done.
    Qed.

    Lemma initialise_adversary_compartment ( C_cmpt : cmpt ) :
      let PCC := WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let exp_tbl_addrs := (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) in
      let a_eh := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler)%a in
      let a_ehs := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless)%a in
      ([∗ map] k↦y ∈ mk_initial_cmpt C_cmpt, k ↦ₐ lword_of_word y)
      ==∗
      [[ (cmpt_b_pcc C_cmpt), (cmpt_a_code C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] ∗
      [[ (cmpt_a_code C_cmpt), (cmpt_e_pcc C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] ∗
      [[ (cmpt_b_cgp C_cmpt), (cmpt_e_cgp C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] ∗
      [[ (cmpt_b_static_sealed C_cmpt), (cmpt_e_static_sealed C_cmpt) ]] ↦ₐ [[ lword_of_word <$> cmpt_static_sealed C_cmpt ]] ∗
      cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ PCC ∗
      cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ CGP ∗
      a_eh ↦ₐ□ lword_of_word (cmpt_exp_tbl_handler C_cmpt) ∗
      a_ehs ↦ₐ□ lword_of_word (cmpt_exp_tbl_handler_stackless C_cmpt) ∗
      ([∗ list] a;v ∈ exp_tbl_addrs ; cmpt_exp_tbl_entries C_cmpt, a ↦ₐ□ lword_of_word v).
    Proof.
      intros PCC CGP exp_tbl_addrs a_eh a_ehs.
      subst a_eh a_ehs.
      iIntros "Hcmpt_C".
      iMod (initialise_compartment with "Hcmpt_C")
        as "($ & $ & $ & $ & HC_etbl_pcc & HC_etbl_cgp & HC_etbl_eh & HC_etbl_ehs & HC_etbl_entries)".
      iMod (pointsto_persist with "HC_etbl_pcc") as "$".
      iMod (pointsto_persist with "HC_etbl_cgp") as "$".
      iMod (pointsto_persist with "HC_etbl_eh") as "$".
      iMod (pointsto_persist with "HC_etbl_ehs") as "$".
      iMod (region_pointsto_persist with "HC_etbl_entries") as "HC_etbl_entries".
      subst exp_tbl_addrs.
      rewrite /region_pointsto_pers big_sepL2_fmap_r.
      by iFrame "HC_etbl_entries".
    Qed.

End adequacy_helpers.

(** ** Ghost initialisation *)
Section adequacy_ghost_init.
  Context `{MP : MachineParameters}.

  (** With zero in [cnull], the initial logical registers are the physical
      ones without identifiers. *)
  Lemma init_lregs_cnull (reg : Reg) :
    reg !! cnull = Some (WInt 0) → init_lregs reg = lword_of_word <$> reg.
  Proof.
    intros Hnull. rewrite /init_lregs Hnull insert_id //.
    by rewrite lookup_fmap Hnull.
  Qed.

End adequacy_ghost_init.
