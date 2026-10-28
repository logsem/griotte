From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import switcher_base_interp assert_spec.
From griotte Require Import rules call_stack.
From griotte Require Import mkregion_helpers memory_region disjoint_regions_tactics.
From griotte Require Import switcher_adequacy compartment_layout.
From griotte Require Import allocator_resources.

(** The namespace of the invariant on the flag of the assert library. *)
Definition Nassert_flag : namespace := nroot .@ "assert_flag".

(** The layout of a trusted stack [ [b, e)] with contents [ts] and hazard
    slots [ [b_hz, e_hz)]. *)
Section trusted_stack_layout.
  Context `{MP : MachineParameters}.

  Record trusted_stack_layout (b e b_hz e_hz : Addr) (ts : list Word) : Prop :=
    MkTrustedStackLayout {
    tsl_size : (b + length ts)%a = Some e;
    tsl_frameoffset :
      ts !! Z.to_nat TrustedStack_offset_frameoffset = Some (WInt (tstack_frameoffset 0));
    tsl_frames_fit : ∃ n : nat, (b + tstack_frame_offset (S n))%a = Some e;
    tsl_error_count :
      ts !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_errorHandlerCount)
      = Some (WInt 0);
    tsl_words : Forall trusted_stack_word ts;
    tsl_hazard :
      ts !! Z.to_nat TrustedStack_offset_hazardPointers = Some (Cap WO Global b_hz e_hz b_hz);
  }.
End trusted_stack_layout.

Section adequacy_helpers.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters} .

    Lemma initialise_assert_compartment
      {E : coPset} (assert_cmpt : cmptAssert) :
      ([∗ map] a↦v ∈ mk_initial_assert assert_cmpt, a ↦ₐ lword_of_word v)
      ={E}=∗
      inv Nassert_flag (flag_assert assert_cmpt ↦ₐ WInt 0) ∗
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
      iMod (inv_alloc Nassert_flag E (flag_assert assert_cmpt ↦ₐ WInt 0%Z) with "Hassert_flag")%I
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
        replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)
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

    (** The code of the switcher and its sealing type, once for every
        thread: the code and the unsealing key become persistent, and the
        sealing type gets the predicate of the export entries. The layout
        is the class [swlayout], as in the switcher's specifications. *)
    Lemma initialise_switcher_shared
      {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf} {E : coPset} :
      mtcc_vec = switcher_label_pc "exception_entry_asm" ->
      ([∗ map] k↦y ∈ mkregion switcher.b_switcher switcher.a_switcher_call
                       (switcher_data_words switcher.ot_switcher) ∪
                     mkregion switcher.a_switcher_call switcher.e_switcher switcher_instrs,
         k ↦ₐ lword_of_word y) -∗
      can_alloc_pred switcher.ot_switcher
      ={E}=∗
      seal_pred switcher.ot_switcher ot_switcher_propC ∗
      switcher_static.
    Proof.
      intros Hmtcc.
      iIntros "Hswitcher Hseal_store".
      pose proof switcher.switcher_call_entry_point as Hcall.
      pose proof switcher.switcher_size as Hsize.
      iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
      { apply map_disjoint_dom_2.
        repeat rewrite dom_mkregion_eq; try solve_addr.
        apply elem_of_disjoint. intros a Ha Ha'.
        rewrite !elem_of_list_to_set !elem_of_finz_seq_between in Ha, Ha'.
        solve_addr. }
      (* The data words of the switcher, with its key at their second word *)
      iDestruct (mkregion_prepare with "[Hswitcher_sealing]") as ">Hswitcher_data"; auto.
      { exact Hcall. }
      rewrite /switcher_data_words.
      rewrite (finz_seq_between_cons switcher.b_switcher); last solve_addr.
      rewrite (finz_seq_between_cons (switcher.b_switcher ^+ 1)); last solve_addr.
      iDestruct "Hswitcher_data" as "(_ & Hswitcher_sealing & _)".
      iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
      { exact Hsize. }
      iMod (seal_store_update_alloc _ ot_switcher_propC with "Hseal_store")
        as "#Hsealed_pred_ot_switcher".
      iAssert (codefrag switcher.a_switcher_call switcher_instrs)
        with "[Hswitcher]" as "Hswitcher_code".
      { rewrite /codefrag /region_pointsto.
        setoid_rewrite big_sepL2_fmap_r.
        replace (switcher.a_switcher_call ^+ length switcher_instrs)
          with switcher.e_switcher by solve_addr+Hsize.
        iFrame. }
      iMod (codefrag_persist with "Hswitcher_code") as "#Hswitcher_code".
      iMod (pointsto_persist with "Hswitcher_sealing") as "#Hswitcher_sealing".
      iModIntro. iFrame "Hsealed_pred_ot_switcher".
      rewrite /switcher_static /switcher_sealing_inv.
      iFrame "Hswitcher_code Hswitcher_sealing".
      iPureIntro. split; [done | apply switcher.ot_switcher_size].
    Qed.

    (** The trusted-stack invariant for the thread [th], from its trusted
        stack with contents [ts], its hazard slots and its call stack. The
        entry frame of the thread holds the words [w_csp] and [w_tbl], a
        capability to the export table at [b_tbl], and no error handler
        invocation. *)
    Lemma initialise_switcher_thread
      {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf} {E : coPset}
      (ts : list Word) (w_csp w_tbl : Word) (b_tbl : Addr) :
      let ef := {| tf_csp := lword_of_word w_csp; tf_export_tbl := lword_of_word w_tbl;
                   tf_error_count := 0 |} in
      trusted_stack_layout switcher.b_trusted_stack switcher.e_trusted_stack
        switcher.b_hazard_slots switcher.e_hazard_slots ts ->
      ts !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_csp) = Some w_csp ->
      ts !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_calleeExportTable)
        = Some w_tbl ->
      exp_tbl_cap b_tbl w_tbl ->
      ([∗ map] k↦y ∈ mkregion switcher.b_trusted_stack switcher.e_trusted_stack ts,
         k ↦ₐ lword_of_word y) -∗
      ([∗ map] k↦y ∈ mkregion switcher.b_hazard_slots switcher.e_hazard_slots [WInt 0; WInt 0],
         k ↦ₐ lword_of_word y) -∗
      ●(CSTK)[th] (entry_cstack ef) -∗
      mtdc ↦ₜ[th] Capₗ RWL _ switcher.b_trusted_stack switcher.e_trusted_stack switcher.b_trusted_stack
      ={E}=∗
      na_inv (tpool th) Ntstack trusted_stack_inv.
    Proof.
      intros ef Hts Hw_csp Hw_tbl Htbl_cap.
      iIntros "Htrusted_stack Hhazard_slots Hcstk_full Hmtdc".
      destruct Hts as [Htstk_size Hframeoffset [n Hfit] Hw_cnt _ Hhazard_cell].
      iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
      { exact Htstk_size. }
      iDestruct (mkregion_prepare with "[Hhazard_slots]") as ">Hhazard_slots"; auto.
      { apply switcher.hazard_slots_size. }
      iAssert (|==> switcher_preamble.trusted_stack_inv)%I
        with "[Htrusted_stack Hhazard_slots Hcstk_full Hmtdc]" as ">Hswitcher".
      {
        iAssert ([[ switcher.b_trusted_stack, switcher.e_trusted_stack ]]
                   ↦ₐ [[ lword_of_word <$> ts ]])%I
          with "[Htrusted_stack]" as "Htrusted_stack".
        { rewrite /region_pointsto big_sepL2_fmap_r. iFrame. }
        iAssert (∃ ws, [[ switcher.b_hazard_slots, switcher.e_hazard_slots ]] ↦ₐ [[ ws ]])%I
          with "[Hhazard_slots]" as "Hhazard_slots".
        { iExists (lword_of_word <$> [WInt 0; WInt 0]).
          rewrite /region_pointsto big_sepL2_fmap_r. iFrame. }
        set (b := switcher.b_trusted_stack) in *.
        set (e := switcher.e_trusted_stack) in *.
        set (l := ts) in *.
        set (i_frameoffset := Z.to_nat TrustedStack_offset_frameoffset) in Hframeoffset.
        set (a_threadID := b ^+ TrustedStack_offset_threadID).
        (* The entry frame [frames[0]], and its cells *)
        set (a_entry := b ^+ TrustedStack_offset_frames).
        set (a_export_table := a_entry ^+ TrustedStackFrame_offset_calleeExportTable).
        set (a_error_count := a_entry ^+ TrustedStackFrame_offset_errorHandlerCount).
        set (a_next := a_entry ^+ TrustedStackFrame_size).
        assert (length l = Z.to_nat (tstack_frame_offset (S n))) as Hlen
          by (tstack_unfold; solve_addr).
        (* The save area, the header ([frameoffset] and [threadID]), the entry
           frame and the unused part *)
        assert (drop (S i_frameoffset) l !! 1 = Some w_csp) as Hw_csp'.
        { by rewrite lookup_drop -Hw_csp. }
        clear Hw_csp.
        assert (drop (S i_frameoffset) l !! 2 = Some w_tbl) as Hw_tbl'.
        { by rewrite lookup_drop -Hw_tbl. }
        clear Hw_tbl.
        assert (drop (S i_frameoffset) l !! 3 = Some (WInt 0)) as Hw_cnt'.
        { by rewrite lookup_drop -Hw_cnt. }
        clear Hw_cnt.
        rewrite -(take_drop_middle l i_frameoffset _ Hframeoffset).
        revert Hw_csp' Hw_tbl' Hw_cnt'.
        assert (length (drop (S i_frameoffset) l)
                = Z.to_nat (TSTACK_HEADER_SZ - 1 + TrustedStackFrame_size * Z.of_nat (S n)))
          as Hlen_rest
          by (rewrite length_drop Hlen; subst i_frameoffset; tstack_unfold; lia).
        destruct (drop (S i_frameoffset) l) as [|w_threadID rest];
          first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_csp_cell rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_export_table rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        destruct rest as [|w_error_count rest]; first (cbn in Hlen_rest; tstack_unfold; lia).
        intros Hw_csp' Hw_tbl' Hw_cnt'. cbn in Hw_csp', Hw_tbl', Hw_cnt'. simplify_eq.
        rewrite fmap_app fmap_cons.
        iDestruct (region_pointsto_split _ _ (b ^+ TSTACK_REGFRAME_SZ) with "Htrusted_stack")
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
        rewrite /trusted_stack_inv.
        iExists a_entry, (entry_cstack ef), _, _.
        rewrite /cstack_interp.
        subst ef. cbn.
        rewrite /trusted_frame_interp /TrustedStackFrame_offset_csp finz_add_0_default /=.
        iFrame "∗ #".
        iSplit.
        { iPureIntro. rewrite list_lookup_fmap lookup_take_lt; last (vm_compute; lia).
          by rewrite Hhazard_cell. }
        iSplit; last (iPureIntro; destruct Htbl_cap as (p & g & e_tbl & a_tbl & -> & Htbl);
                      rewrite /tf_export_tbl_ok /=; split; [by exists p, g, e_tbl, a_tbl | done]).
        iPureIntro; subst a_entry b e; tstack_unfold; split; solve_addr.
      }
      iMod (na_inv_alloc (tpool th) _ Ntstack _ with "Hswitcher") as "#Hswitcher".
      by iModIntro.
    Qed.

    Lemma initialise_compartment ( C_cmpt : cmpt ) :
      let PCC := Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let a_eh := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler) in
      let a_ehs := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless) in
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
      assert (finz.seq_between (cmpt_exp_tbl_cgp C_cmpt) (cmpt_exp_tbl_entries_start C_cmpt) =
                [cmpt_exp_tbl_cgp C_cmpt;
                 (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler);
                 (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless)])
        as Hheader_addrs.
      { rewrite finz_seq_between_cons; last solve_addr.
        rewrite finz_seq_between_cons; last solve_addr.
        rewrite finz_seq_between_singleton; last solve_addr.
        f_equal; f_equal; [solve_addr | f_equal; solve_addr]. }
      rewrite Hheader_addrs.
      rewrite !big_sepL2_singleton.
      rewrite /region_pointsto !big_sepL2_fmap_r /=.
      iDestruct "HC_etbl_cgp" as "($ & $ & $ & _)".
      iFrame.
      done.
    Qed.

    Lemma initialise_adversary_compartment ( C_cmpt : cmpt ) :
      let PCC := Cap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt) in
      let CGP := Cap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt) in
      let exp_tbl_addrs := (finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)) in
      let a_eh := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandler) in
      let a_ehs := (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_errorHandlerStackless) in
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
