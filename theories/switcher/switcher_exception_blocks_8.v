From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_handler
  copy_context_spec.

(** * Exception path, block 35: the installation of the handler's context

    Block 35 ([.Lhandle_error_install_context]) installs the context that
    the error handler returns, its [ErrorState], read below the handler's
    stack pointer [csp]. The resumed PC is the PCC of the export table of
    the topmost frame, with the address of word 0 of the [ErrorState]: the
    handler chooses an address, not the bounds or permissions. Words 1-15
    of the [ErrorState] are copied to the register save area
    ([copy_context_asm]), the error handler count of the topmost frame is
    incremented, and the block jumps to the context install (block 39)
    with the resumed PC in [ct2].

    Three loads may fault: the load of the PCC of the table when the cell
    of the export table in the frame is cleared, the load of word 0 of the
    [ErrorState] through [csp], and a load of the copy past the end of
    [csp]. *)

Section Switcher_Exception_Blocks_8.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  #[local] Lemma switcher_instrs_35_split :
    switcher_instrs_n 35 =
      encodeInstrsW [ SpecialRW ct1 MTDC (inr cnull);
                      CLoad ctp ct1 TrustedStack_offset_frameoffset;
                      machine_instructions.Add ctp (inr ctp) (inl (- TrustedStackFrame_size)%Z);
                      Lea ctp ct1 (inr ctp);
                      CLoad ct0 ctp TrustedStackFrame_offset_calleeExportTable;
                      GetB cs0 ct0;
                      SetA ct0 ct0 (inr cs0);
                      CLoad ct0 ct0 ExportTable_offset_pcc;
                      CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size);
                      GetA cra cra;
                      SetA ct2 ct0 (inr cra);
                      Lea ca2 csp (inl (TrustedStack_offset_cra - ErrorState_size)%Z);
                      Lea ca3 ct1 (inl TrustedStack_offset_cra) ] ++
      copy_context_instrs ca3 ca2 cs1 ca4 ++
      encodeInstrsW [ CLoad cs1 ctp TrustedStackFrame_offset_errorHandlerCount;
                      machine_instructions.Add cs1 (inr cs1) (inl 1%Z);
                      Store ctp (inr cs1) TrustedStackFrame_offset_errorHandlerCount;
                      Mov csp (inr ct1);
                      Jmp (inl 12%Z) ].
  Proof. reflexivity. Qed.

  (** Block 35, at [pc_a]. [d] is the depth of the call stack, [a_tstk] its
      topmost frame, whose cell of the export table holds [wcell] (cleared,
      or a capability to the table at [b_tbl], whose PCC is [wpcc]) and
      whose error handler count is [n]. [L i ls] holds once the first [i]
      words [ls] of the [ErrorState] are loaded, through the accessor given
      for the [ErrorState] below [wcsp]. A fault happens at [pc_a ^+ k]:
      at the load of the PCC of the table ([k = 7]), at the load of
      word 0 of the [ErrorState] ([k = 8]), or at a load of the copy
      ([k = 14]). *)
  #[local] Lemma switcher_exception_block_35_spec_aux
    (pc_a : Addr) (d : nat) (a_tstk b_tbl : Addr) (n : Z) (save : list LWord)
    (wpcc wcell wcsp wcra wctp wct0 wct1 wct2 wcs0 wcs1 wca2 wca3 wca4 : LWord)
    (dq : dfrac) (L : nat → list LWord → iProp Σ) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_cnt_cell := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 35))%a ->
    (pc_a + 36)%a = Some (pc_a ^+ 36)%a ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    length save = 21%nat ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ wcsp ∗
    cra ↦ᵣ wcra ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    mtdc ↦ₛᵣ tstack_cap ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    a_cnt_cell ↦ₐ WInt n ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₐ□ wpcc) ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
    codefrag_pers pc_a (switcher_instrs_n 35) ∗
    L 0 [] ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜lea_result wcsp (- ErrorState_size) = Some (WCap true p g b e a @@? π)⌝ -∗
       ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
       cells_load_acc L p e a π (Z.to_nat ErrorState_size)) ∗
    ▷ ( ( ∀ (k : Z) (i : nat) (ls save' : list LWord),
          ⌜k = 7%Z ∨ k = 8%Z ∨ k = 14%Z⌝ -∗
          ⌜length save' = 21%nat⌝ -∗
          csp ↦ᵣ wcsp ∗
          cra ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt n ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] ∗
          L i ls -∗
          trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ k)%a) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ∀ ls : list LWord,
          ⌜length ls = Z.to_nat ErrorState_size⌝ -∗
          ⌜exp_tbl_cap b_tbl wcell.(lw)⌝ -∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 36)%a ∗
          csp ↦ᵣ tstack_cap ∗
          cra ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ tstack_cap ∗
          ct2 ↦ᵣ resumed_pc wpcc (get_a (ls !!! 0%nat).(lw)) ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt (n + 1) ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ save !!! 0%nat :: drop 1 ls ++ drop 16 save ]] ∗
          L (Z.to_nat ErrorState_size) ls -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_tbl_cell a_cnt_cell.
    iIntros (Hsub Hjmp Ha_tstk Ha_tstk_end Hlen Hwcell)
      "(HPC & Hcsp & Hcra & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca2 & Hca3 & Hca4
       & Hmtdc & Hframeoffset & Hcell & Hcnt & #Hpcc & Hsave & #Hcode & HL & Hacc & Hpost)".
    pose proof trusted_stack_frames_fit as [nfit Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    iPoseProof "Hcode" as "Hcode_all".
    iEval (rewrite switcher_instrs_35_split) in "Hcode_all".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hcopy _]".
    iEval (simpl length) in "Hcopy".
    codefrag_facts "Hcode".
    assert (length (switcher_instrs_n 35) = 25%nat) as Hlen35 by reflexivity.
    rewrite Hlen35 in Hsub.
    rewrite /switcher_instrs_n /assembled_switcher_n /tstack_cap.
    (* SpecialRW ct1 mtdc cnull *)
    iInstr "Hcode".
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a = Some a_frameoffset) as Hfo
      by (subst a_frameoffset; tstack_unfold; solve_addr).
    (* CLoad ctp ct1 TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { subst a_frameoffset; tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. subst a_frameoffset; rewrite /withinBounds; tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* Add ctp ctp (- TrustedStackFrame_size) *)
    iInstr "Hcode".
    assert ((b_trusted_stack + (tstack_frameoffset d + - TrustedStackFrame_size))%a = Some a_tstk)
      as Ha_tstk'.
    { rewrite -Ha_tstk. f_equal. tstack_unfold. lia. }
    (* Lea ctp ct1 ctp *)
    iInstr "Hcode".
    assert ((a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell)
      as Ha_cell by (subst a_tbl_cell; tstack_unfold; solve_addr).
    assert (withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true) as Hcell_bounds
      by (subst a_tbl_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
    (* CLoad ct0 ctp TrustedStackFrame_offset_calleeExportTable *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ct0 ctp
         TrustedStackFrame_offset_calleeExportTable)
      with "[$HPC $Hct0 $Hctp $Hcell]" as "(HPC & Hct0 & Hctp & Hcell)".
    { eapply disjoint_from_shadow_not_in; [exact Hts_shadow | exact Hcell_bounds]. }
    rewrite lload_word_RWL.
    destruct Hwcell as [-> | (Htbl & Hprov)].
    { (* GetB cs0 ct0 *)
      iInstr "Hcode".
      (* SetA ct0 ct0 cs0 *)
      iInstr "Hcode".
      (* CLoad ct0 ct0 ExportTable_offset_pcc *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 7%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    destruct Htbl as (p_tbl & g_tbl & e_tbl & a_tbl & Hw & Hread_tbl & Hbnd & Hshadow_tbl
                      & Hdl & Hdro).
    destruct wcell as [w_cell π_cell]; cbn in Hw, Hprov; subst w_cell π_cell.
    iDestruct ("Hpcc" with "[%]") as "Hpcc_cell".
    { eexists _, _, _, _; split_and!; done. }
    (* GetB cs0 ct0 *)
    iInstr "Hcode".
    (* SetA ct0 ct0 cs0 *)
    iInstr "Hcode".
    (* CLoad ct0 ct0 ExportTable_offset_pcc *)
    iInstrApply "Hcode" (wp_load_witness_imm_same_inbounds_dq _ _ _ _ _ _ _ ct0 0)
      with "[$HPC $Hct0 $Hpcc_cell]" as "(HPC & Hct0 & _)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; [exact Hshadow_tbl | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    rewrite lload_word_no_dl_dro //.
    destruct wcsp as [wsp π].
    destruct (is_cap wsp) eqn:Hcap; cycle 1.
    { (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
      iInstrApply "Hcode" (wp_load_fail_not_cap_imm _ cra csp) with "[$HPC $Hcra $Hcsp]"
        as "(HPC & Hcra & Hcsp)".
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 8%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    destruct wsp as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    { iDestruct (map_of_regs_2 with "Hcra Hcsp") as "[Hmap %Hne]".
      (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
      iInstrApply "Hcode"
        (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
      { done. }
      iDestruct (regs_of_map_2 with "Hmap") as "[Hcra Hcsp]"; first done.
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 8%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    destruct (a + (TrustedStack_offset_mepcc - ErrorState_size))%a as [ea|] eqn:Hea; cycle 1.
    { iDestruct (map_of_regs_2 with "Hcra Hcsp") as "[Hmap %Hne]".
      (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
      iInstrApply "Hcode"
        (wp_load_fail_addr_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap true p g b e a @@? π))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
      all: try done.
      iDestruct (regs_of_map_2 with "Hmap") as "[Hcra Hcsp]"; first done.
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 8%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    destruct (readAllowed p) eqn:Hra; cycle 1.
    { (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
      iInstrApply "Hcode" (wp_load_fail_not_ra_imm _ cra csp) with "[$HPC $Hcra $Hcsp]"
        as "(HPC & Hcra & Hcsp)".
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 8%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    destruct (decide (b <= ea < e)%a) as [Hin | Hout]; cycle 1.
    { (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
      iInstrApply "Hcode" (wp_load_fail_not_withinbounds_imm _ cra csp)
        with "[$HPC $Hcra $Hcsp]" as "(HPC & Hcra & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! 8%Z 0%nat (@nil LWord) save with "[] [//] [-]"). }
    (* The accessor of the [ErrorState], below [csp] *)
    iPoseProof ("Hacc" $! p g b e ea π with "[%] [%]") as "#Hacc_es".
    { rewrite /lea_result /=. by rewrite Hea. }
    { split; [done | solve_addr]. }
    iMod ("Hacc_es" $! 0%nat [] with "[%] [%] HL")
      as (v dqv wit dw) "(%Hsh & %Hπ & Hes0 & Hwit & Hdw & Hclose)".
    { rewrite /ErrorState_size; lia. }
    { solve_addr. }
    rewrite (_ : (ea ^+ 0%nat)%a = ea) in Hsh |- *; last solve_addr.
    (* CLoad cra csp (TrustedStack_offset_mepcc - ErrorState_size) *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds_deref _ _ _ _ _ _ _ cra csp
         (TrustedStack_offset_mepcc - ErrorState_size))
      with "[$HPC $Hcra $Hcsp $Hes0 $Hwit $Hdw]"
      as (v0) "(%Hload & HPC & Hcra & Hcsp & Hes0 & Hwit & Hdw)".
    { rewrite /withinBounds; solve_addr. }
    iMod ("Hclose" $! v0 with "[//] Hes0 Hwit Hdw") as "HL".
    rewrite /TrustedStack_offset_mepcc /ErrorState_size in Hea.
    (* GetA cra cra *)
    iInstr "Hcode".
    destruct (lea_result_is_Some wpcc (get_a v0.(lw) - get_a wpcc.(lw))) as [wpc Hwpc].
    (* SetA ct2 ct0 cra *)
    iInstrApply "Hcode" (wp_seta_success_reg_any_src _ _ _ _ _ _ _ _ _ _ _ _ _ wpc)
      with "[$HPC $Hct0 $Hcra $Hct2]" as "(HPC & Hct0 & Hcra & Hct2)".
    { by rewrite seta_result_lea_result. }
    assert (resumed_pc wpcc (get_a v0.(lw)) = wpc) as Hresumed
      by (by rewrite /resumed_pc Hwpc).
    (* Lea ca2 csp (TrustedStack_offset_cra - ErrorState_size) *)
    iInstr "Hcode".
    { transitivity (Some (ea ^+ 1)%a); solve_addr. }
    (* Lea ca3 ct1 TrustedStack_offset_cra *)
    iInstr "Hcode".
    { pose proof (tstack_save_cell_ok 1 ltac:(lia)) as (Hts_1 & _). exact Hts_1. }
    (* The destination of the copy: the words 1-15 of the register save area *)
    assert ((b_trusted_stack + 21)%a = Some tstack_save_end) as Hsave_end.
    { rewrite /tstack_save_end. tstack_unfold. solve_addr. }
    pose proof (tstack_save_cell_ok 20 ltac:(lia)) as (_ & Hts_20 & _).
    rewrite /withinBounds in Hts_20.
    destruct (lookup_lt_is_Some_2 save 0%nat) as [w0 Hw0]; first lia.
    assert (save = w0 :: take 15 (drop 1 save) ++ drop 16 save) as Hsave_eq.
    { destruct save as [|w0' rest]; first done.
      cbn in Hw0 |- *. injection Hw0 as ->. by rewrite take_drop. }
    iEval (rewrite {1}Hsave_eq) in "Hsave".
    iEval (rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr])
      in "Hsave".
    iDestruct "Hsave" as "[Hs0 Hsave]".
    iEval (rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
           [|solve_addr|rewrite length_take length_drop Hlen /finz.dist; solve_addr])
      in "Hsave".
    iDestruct "Hsave" as "[Hdst Hrest]".
    iEval (rewrite (_ : (b_trusted_stack ^+ 16)%a = ((b_trusted_stack ^+ 1) ^+ 15)%a);
           last solve_addr) in "Hdst".
    iDestruct (cells_load_acc_tail L p e ea π 15 v0 with "[]") as "Hacc_tail".
    { rewrite /cells_load_acc. iModIntro. iExact "Hacc_es". }
    (* copy_context_asm ca3 ca2 cs1 ca4 *)
    iApply (copy_context_load_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (take 15 (drop 1 save)) _ _ (λ i ls, L (S i) (v0 :: ls))
             with "[- $HPC $Hcopy $Hca2 $Hca3 $Hcs1 $Hca4 $HL $Hacc_tail $Hdst]").
    all: try done.
    all: try (rewrite length_take length_drop Hlen; done).
    all: try (cbn; solve_addr).
    { rewrite /disjoint_from_shadow elem_of_disjoint in Hts_shadow |- *.
      intros x Hx HR. eapply Hts_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    { clear; set_solver. }
    iNext. iSplit.
    - iIntros (j ls wd' Hj Hls Hwd' Hout) "Hca2 Hca3 Hcs1 Hca4 Hdst HL".
      iDestruct "Hpost" as "[Hfailed _]".
      rewrite (_ : ((pc_a ^+ 13%nat) ^+ 1)%a = (pc_a ^+ 14)%a); last solve_addr.
      iApply ("Hfailed" $! 14%Z (S j) (v0 :: ls) (w0 :: wd' ++ drop 16 save)
               with "[] [%] [-]").
      { iPureIntro; by right; right. }
      { rewrite /= length_app length_drop Hwd' Hlen. lia. }
      rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
        [|solve_addr|rewrite Hwd' /finz.dist; solve_addr].
      rewrite (_ : ((b_trusted_stack ^+ 1) ^+ 15)%a = (b_trusted_stack ^+ 16)%a); last solve_addr.
      iFrame.
    - iIntros (ls wscratch' Hls) "HPC Hca2 Hca3 Hcs1 Hca4 Hdst HL".
      rewrite (_ : ((pc_a ^+ 13%nat) ^+ length (copy_context_instrs ca3 ca2 cs1 ca4))%a =
                   (pc_a ^+ 20)%a); last (cbn; solve_addr).
      assert ((a_tstk + TrustedStackFrame_offset_errorHandlerCount)%a = Some a_cnt_cell)
        as Ha_cnt by (subst a_cnt_cell; tstack_unfold; solve_addr).
      (* CLoad cs1 ctp TrustedStackFrame_offset_errorHandlerCount *)
      iInstr "Hcode".
      { subst a_cnt_cell; tstk_not_shadow Hts_shadow. }
      { done. }
      { split; auto. subst a_cnt_cell; rewrite /withinBounds; tstack_unfold; solve_addr. }
      rewrite lload_word_RWL.
      (* Add cs1 cs1 1 *)
      iInstr "Hcode".
      (* Store ctp cs1 TrustedStackFrame_offset_errorHandlerCount *)
      iInstr "Hcode".
      { subst a_cnt_cell; tstk_not_shadow Hts_shadow. }
      { subst a_cnt_cell; rewrite /withinBounds; tstack_unfold; solve_addr. }
      iEval (rewrite lstore_word_isWL //) in "Hcnt".
      (* Mov csp ct1 *)
      iInstr "Hcode".
      (* Jmp .Lcommon_context_install *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ 36)%a); solve_addr. }
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" $! (v0 :: ls) with "[%] [%] [-]").
      { cbn; rewrite Hls; done. }
      { eexists _, _, _, _; split_and!; done. }
      rewrite /= Hresumed (list_lookup_total_correct _ _ _ Hw0) drop_0.
      rewrite (list_fmap_ext (lstore_word RWL) id ls); last (intros; by apply lstore_word_isWL).
      rewrite list_fmap_id.
      rewrite (region_pointsto_cons _ (b_trusted_stack ^+ 1)%a); [|solve_addr|solve_addr].
      rewrite (region_pointsto_split _ _ (b_trusted_stack ^+ 16)%a);
        [|solve_addr|rewrite Hls /finz.dist; solve_addr].
      rewrite (_ : ((b_trusted_stack ^+ 1) ^+ 15)%a = (b_trusted_stack ^+ 16)%a); last solve_addr.
      iFrame.
  Qed.

  (** Block 35, from [.Lhandle_error_install_context]. [d] is the depth of
      the call stack, [a_tstk] its topmost frame, whose cell of the export
      table holds [wcell] (cleared, or a capability to the table at
      [b_tbl], whose PCC is [wpcc]) and whose error handler count is [n].
      [L i ls] holds once the first [i] words [ls] of the [ErrorState] are
      loaded, through the accessor given for the [ErrorState] below the
      handler's stack pointer [wcsp]. Outcomes:
      - a load faults at a switcher PC that does not resume: the cell of
        the export table is cleared, or [wcsp] does not allow the load of a
        word of the [ErrorState];
      - the 16 words [ls] of the [ErrorState] are loaded: words 1-15 are
        in the register save area, the count is incremented, [ct2] holds
        the PCC of the table with the address of word 0, and the PC is at
        the context install. *)
  Lemma switcher_install_context_block_spec
    (d : nat) (a_tstk b_tbl : Addr) (n : Z) (save : list LWord)
    (wpcc wcell wcsp wcra wctp wct0 wct1 wct2 wcs0 wcs1 wca2 wca3 wca4 : LWord)
    (dq : dfrac) (L : nat → list LWord → iProp Σ) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_cnt_cell := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    length save = 21%nat ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_install_context" ∗
    csp ↦ᵣ wcsp ∗
    cra ↦ᵣ wcra ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    mtdc ↦ₛᵣ tstack_cap ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    a_cnt_cell ↦ₐ WInt n ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₐ□ wpcc) ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
    switcher_code ∗
    L 0 [] ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜lea_result wcsp (- ErrorState_size) = Some (WCap true p g b e a @@? π)⌝ -∗
       ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
       cells_load_acc L p e a π (Z.to_nat ErrorState_size)) ∗
    ▷ ( ( ∀ (off : Z) (i : nat) (ls save' : list LWord),
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          ⌜length save' = 21%nat⌝ -∗
          csp ↦ᵣ wcsp ∗
          cra ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt n ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] ∗
          switcher_code ∗
          L i ls -∗
          trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ∀ ls : list LWord,
          ⌜length ls = Z.to_nat ErrorState_size⌝ -∗
          ⌜exp_tbl_cap b_tbl wcell.(lw)⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lcommon_context_install" ∗
          csp ↦ᵣ tstack_cap ∗
          cra ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ tstack_cap ∗
          ct2 ↦ᵣ resumed_pc wpcc (get_a (ls !!! 0%nat).(lw)) ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca2 ↦ᵣ - ∗
          ca3 ↦ᵣ - ∗
          ca4 ↦ᵣ - ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt (n + 1) ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ save !!! 0%nat :: drop 1 ls ++ drop 16 save ]] ∗
          switcher_code ∗
          L (Z.to_nat ErrorState_size) ls -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_tbl_cell a_cnt_cell.
    iIntros (Ha_tstk Ha_tstk_end Hlen Hwcell)
      "(HPC & Hcsp & Hcra & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca2 & Hca3 & Hca4
       & Hmtdc & Hframeoffset & Hcell & Hcnt & #Hpcc & Hsave & #Hswitcher & HL & Hacc & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error_install_context") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_35_spec_aux _ d a_tstk b_tbl n save wpcc
              _ _ _ _ _ _ _ _ _ _ _ _ _ L
             with "[- $HPC $Hcsp $Hcra $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca2 $Hca3 $Hca4
                      $Hmtdc $Hframeoffset $Hcell $Hcnt $Hpcc $Hsave $Hcode $HL $Hacc]");
      [done | offsets_compute; solve_addr+Hsize | done | done | done | done |].
    iNext; iSplit.
    - iIntros (k i ls save' Hk Hsave')
        "(Hcsp & Hcra & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca2 & Hca3 & Hca4
         & Hmtdc & Hframeoffset & Hcell & Hcnt & Hsave & HL)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[Hfailed _]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 35) ^+ k)%a =
                   (a_switcher_call ^+ (switcher_block_offset 35 + k))%a);
        last (destruct Hk as [-> | [-> | ->] ]; offsets_compute; solve_addr+Hsize).
      iApply ("Hfailed" with "[] [//] [-]").
      { iPureIntro. apply trap_no_resume_switcher_pc.
        destruct Hk as [-> | [-> | ->] ]; by vm_compute. }
      iFrame "∗ Hswitcher".
    - iIntros (ls Hls Htbl)
        "(HPC & Hcsp & Hcra & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca2 & Hca3 & Hca4
         & Hmtdc & Hframeoffset & Hcell & Hcnt & Hsave & HL)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      switcher_change_pc (switcher_label_offset ".Lcommon_context_install").
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//] [//]"). iFrame "∗ Hswitcher".
  Qed.

End Switcher_Exception_Blocks_8.
