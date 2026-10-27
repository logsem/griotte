From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state
  copy_context_spec.

(** * Exception path: the installation of the handler's context

    [.Lhandle_error_install_context] installs the context that the error
    handler returns, its [ErrorState], read at the handler's stack pointer
    [csp]. The resumed PC is the PCC of the export table of the topmost
    frame, with the address of word 0 of the [ErrorState]: the handler
    chooses an address, not the bounds or permissions. Words 1-15 of the
    [ErrorState] are copied to the register save area ([copy_context_asm]),
    the error handler count of the topmost frame is incremented, and the
    block jumps to [.Lcommon_context_install] with the resumed PC in
    [ct2].

    Three loads may fault: the load of the PCC of the table when the cell
    of the export table in the frame is cleared, the load of word 0 of the
    [ErrorState] through [csp], and a load of the copy past the end of
    [csp]. *)

Section Handle_Error_Install_Context.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The code of [.Lhandle_error_install_context], around the copy. *)
  #[local] Definition handle_error_install_context_instrs : list Word :=
      encodeInstrsW [ SpecialRW ct1 MTDC (inr cnull);
                      CLoad ctp ct1 TrustedStack_offset_frameoffset;
                      machine_instructions.Add ctp (inr ctp) (inl (- TrustedStackFrame_size)%Z);
                      Lea ctp ct1 (inr ctp);
                      CLoad ct0 ctp TrustedStackFrame_offset_calleeExportTable;
                      GetB cs0 ct0;
                      SetA ct0 ct0 (inr cs0);
                      CLoad ct0 ct0 ExportTable_offset_pcc;
                      CLoad cra csp TrustedStack_offset_mepcc;
                      GetA cra cra;
                      SetA ct2 ct0 (inr cra);
                      Lea ca2 csp (inl TrustedStack_offset_cra);
                      Lea ca3 ct1 (inl TrustedStack_offset_cra) ] ++
      copy_context_instrs ca3 ca2 cs1 ca4 ++
      encodeInstrsW [ CLoad cs1 ctp TrustedStackFrame_offset_errorHandlerCount;
                      machine_instructions.Add cs1 (inr cs1) (inl 1%Z);
                      Store ctp (inr cs1) TrustedStackFrame_offset_errorHandlerCount;
                      Mov csp (inr ct1);
                      Jmp (inl (-130)%Z) ].

  (** The loads of the [ErrorState] succeed through a tagged readable
      capability, with the [ErrorState] in bounds from its cursor. *)
  #[local] Lemma error_state_loads_ok_inv (wcsp : LWord) :
    error_state_loads_ok wcsp →
    ∃ (p : Perm) (g : Locality) (b e a : Addr),
      wcsp.(lw) = WCap true p g b e a ∧
      readAllowed p = true ∧ (b <= a)%a ∧ (a + ErrorState_size <= e)%Z.
  Proof.
    rewrite /error_state_loads_ok.
    destruct wcsp as [w π]; cbn.
    destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | ot sb]; cbn; try done.
    destruct t; last done.
    intros (Hra & Hb & He). by exists p, g, b, e, a.
  Qed.

  (** From [.Lhandle_error_install_context]. [d] is the depth of
      the call stack, [a_tstk] its topmost frame, whose cell of the export
      table holds [wcell] (cleared, or a capability to the table at
      [b_tbl], whose PCC is [wpcc]) and whose error handler count is [n].
      [L i ls] holds once the first [i] words [ls] of the [ErrorState] are
      loaded, through the accessor given for the [ErrorState] at the
      handler's stack pointer [wcsp]. Outcomes:
      - a load faults at a switcher PC that does not resume, for one of two
        reasons: the cell of the export table is cleared, or [wcsp] does not
        allow the loads of the [ErrorState];
      - the 16 words [ls] of the [ErrorState] are loaded: words 1-15 are
        in the register save area, the count is incremented, [ct2] holds
        the PCC of the table with the address of word 0, and the PC is at
        the context install. *)
  Lemma handle_error_install_context_spec
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

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_install_context" ∗
    csp ↦ᵣ[th] wcsp ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ca3 ↦ᵣ[th] wca3 ∗
    ca4 ↦ᵣ[th] wca4 ∗
    mtdc ↦ₜ[th] TStack tstack_cap ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    a_cnt_cell ↦ₐ WInt n ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₐ□ wpcc) ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] ∗
    switcher_code ∗
    L 0 [] ∗
    (∀ (p : Perm) (g : Locality) (b e a : Addr) (π : option AId),
       ⌜wcsp = WCap true p g b e a @@? π⌝ -∗
       ⌜readAllowed p = true ∧ (b <= a)%a⌝ -∗
       cells_load_acc L p e a π (Z.to_nat ErrorState_size)) ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0) ∨ ¬ error_state_loads_ok wcsp⌝ -∗
          ∀ (off : Z) (i : nat) (ls save' : list LWord),
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          ⌜length save' = 21%nat⌝ -∗
          ⌜save' !! Z.to_nat TrustedStack_offset_hazardPointers
           = save !! Z.to_nat TrustedStack_offset_hazardPointers⌝ -∗
          csp ↦ᵣ[th] wcsp ∗
          cra ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ca2 ↦ᵣ[th] - ∗
          ca3 ↦ᵣ[th] - ∗
          ca4 ↦ᵣ[th] - ∗
          mtdc ↦ₜ[th] TStack tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt n ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save' ]] ∗
          L i ls -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) ∧
        ( ∀ (g_tstk : Locality) (ls : list LWord),
          ⌜length ls = Z.to_nat ErrorState_size⌝ -∗
          ⌜exp_tbl_cap b_tbl wcell.(lw)⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_context_install" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          cra ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ct2 ↦ᵣ[th] resumed_pc wpcc (get_a (ls !!! 0%nat).(lw)) ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ca2 ↦ᵣ[th] - ∗
          ca3 ↦ᵣ[th] - ∗
          ca4 ↦ᵣ[th] - ∗
          mtdc ↦ₜ[th] TStack tstack_cap ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          a_cnt_cell ↦ₐ WInt (n + 1) ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ save !!! 0%nat :: drop 1 ls ++ drop 16 save ]] ∗
          L (Z.to_nat ErrorState_size) ls -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_frameoffset a_tbl_cell a_cnt_cell.
    iIntros (Ha_tstk Ha_tstk_end Hlen Hwcell)
      "(HPC & Hcsp & Hcra & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca2 & Hca3 & Hca4
       & Hmtdc & Hframeoffset & Hcell & Hcnt & #Hpcc & Hsave & #Hswitcher & HL & Hacc & Hpost)".
    pose proof trusted_stack_frames_fit as [nfit Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    switcher_open_label ".Lhandle_error_install_context" "Hswitcher" as "Hcode" pc_a Hpc_a.
    (* The exits of the block, from its start: the jump to
       [.Lcommon_context_install], and the faulting loads *)
    switcher_jump_in_block ".Lhandle_error_install_context" ".Lcommon_context_install"
      as Hjmp.
    assert (∀ k : Z, k = 7%Z ∨ k = 8%Z ∨ k = 14%Z →
              (pc_a ^+ k)%a =
                (a_switcher_call ^+ (switcher_label_offset ".Lhandle_error_install_context" + k))%a ∧
              trap_no_resume (switcher_pc (switcher_label_offset ".Lhandle_error_install_context" + k)))
      as Hfault.
    { intros k Hk. split.
      - destruct Hk as [-> | [-> | ->] ]; switcher_addr_eq.
      - apply trap_no_resume_switcher_pc. destruct Hk as [-> | [-> | ->] ]; by vm_compute. }
    clear Hpc_a.
    (* The labels are not needed anymore: they would slow the proof down *)
    set (off_cci := switcher_label_offset ".Lcommon_context_install") in *.
    set (off_eic := switcher_label_offset ".Lhandle_error_install_context") in *.
    clearbody off_cci off_eic.
    (* [trap_no_resume] mentions a label: [simplify_map_eq] unfolds it *)
    set (tnr := trap_no_resume) in *.
    clearbody tnr.
    iAssert (codefrag_pers pc_a handle_error_install_context_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hcopy _]".
    iEval (simpl length) in "Hcopy".
    rewrite /tstack_cap.
    (* SpecialRW ct1 mtdc cnull *)
    iInstrApply "Hcode" wp_readsr_mtdc with "[$HPC $Hct1 $Hmtdc]"
      as (vm) "(%Hvm & HPC & Hct1 & Hmtdc)".
    destruct (mtdc_match_TStack_cap _ _ _ _ _ _ Hvm) as [g_tstk ->].
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
      iDestruct (map_of_regs_1 with "Hct0") as "Hmap".
      iInstrApply "Hcode" (wp_load_fail_const_imm _ _ _ _ _ _ _ _ ct0 ct0 _ _ (WInt 0))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
      { done. }
      iDestruct (regs_of_map_1 with "Hmap") as "Hct0".
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]"); first by left.
      destruct (Hfault 7%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iTrap with ("Hfailed" $! (off_eic + 7)%Z 0%nat (@nil LWord) save with "[//] [//] [//] [-]"). }
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
    { (* CLoad cra csp TrustedStack_offset_mepcc *)
      iInstrApply "Hcode" (wp_load_fail_not_cap_imm _ cra csp) with "[$HPC $Hcra $Hcsp]"
        as "(HPC & Hcra & Hcsp)".
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { right. intros (p' & g' & b' & e' & a' & Hw' & Hra' & Hb' & He')
          %error_state_loads_ok_inv.
        cbn in Hw'; by subst wsp. }
      destruct (Hfault 8%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iTrap with ("Hfailed" $! (off_eic + 8)%Z 0%nat (@nil LWord) save with "[//] [//] [//] [-]"). }
    destruct wsp as [|[tag p g b e a|] | |]; try done.
    destruct tag; cycle 1.
    { iDestruct (map_of_regs_2 with "Hcra Hcsp") as "[Hmap %Hne]".
      (* CLoad cra csp TrustedStack_offset_mepcc *)
      iInstrApply "Hcode"
        (wp_load_fail_tag_imm _ _ _ _ _ _ _ _ _ _ _ _ (WCap false p g b e a @@? π))
        with "[$HPC $Hmap]" as "(HPC & Hmap)".
      { rewrite llookup_reg_not_cnull //; by simplify_map_eq. }
      { done. }
      iDestruct (regs_of_map_2 with "Hmap") as "[Hcra Hcsp]"; first done.
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { right. intros (p' & g' & b' & e' & a' & Hw' & Hra' & Hb' & He')
          %error_state_loads_ok_inv.
        by cbn in Hw'. }
      destruct (Hfault 8%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iTrap with ("Hfailed" $! (off_eic + 8)%Z 0%nat (@nil LWord) save with "[//] [//] [//] [-]"). }
    assert ((a + TrustedStack_offset_mepcc)%a = Some a) as Hea
      by (rewrite /TrustedStack_offset_mepcc; solve_addr).
    destruct (readAllowed p) eqn:Hra; cycle 1.
    { (* CLoad cra csp TrustedStack_offset_mepcc *)
      iInstrApply "Hcode" (wp_load_fail_not_ra_imm _ cra csp) with "[$HPC $Hcra $Hcsp]"
        as "(HPC & Hcra & Hcsp)".
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { right. intros (p' & g' & b' & e' & a' & Hw' & Hra' & Hb' & He')
          %error_state_loads_ok_inv.
        cbn in Hw'; simplify_eq. congruence. }
      destruct (Hfault 8%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iTrap with ("Hfailed" $! (off_eic + 8)%Z 0%nat (@nil LWord) save with "[//] [//] [//] [-]"). }
    destruct (decide (b <= a < e)%a) as [Hin | Hout]; cycle 1.
    { (* CLoad cra csp TrustedStack_offset_mepcc *)
      iInstrApply "Hcode" (wp_load_fail_not_withinbounds_imm _ cra csp)
        with "[$HPC $Hcra $Hcsp]" as "(HPC & Hcra & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { right. intros (p' & g' & b' & e' & a' & Hw' & Hra' & Hb' & He')
          %error_state_loads_ok_inv.
        cbn in Hw'; simplify_eq.
        rewrite /ErrorState_size in He'. solve_addr. }
      destruct (Hfault 8%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iTrap with ("Hfailed" $! (off_eic + 8)%Z 0%nat (@nil LWord) save with "[//] [//] [//] [-]"). }
    (* The accessor of the [ErrorState], at [csp] *)
    iPoseProof ("Hacc" $! p g b e a π with "[%] [%]") as "#Hacc_es".
    { done. }
    { split; [done | solve_addr]. }
    iMod ("Hacc_es" $! 0%nat [] with "[%] [%] HL")
      as (v dqv wit dw) "(%Hsh & %Hπ & Hes0 & Hwit & Hdw & Hclose)".
    { rewrite /ErrorState_size; lia. }
    { solve_addr. }
    rewrite (_ : (a ^+ 0%nat)%a = a) in Hsh |- *; last solve_addr.
    (* CLoad cra csp TrustedStack_offset_mepcc *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds_deref _ _ _ _ _ _ _ cra csp
         TrustedStack_offset_mepcc)
      with "[$HPC $Hcra $Hcsp $Hes0 $Hwit $Hdw]"
      as (v0) "(%Hload & HPC & Hcra & Hcsp & Hes0 & Hwit & Hdw)".
    { rewrite /withinBounds; solve_addr. }
    iMod ("Hclose" $! v0 with "[//] Hes0 Hwit Hdw") as "HL".
    (* GetA cra cra *)
    iInstr "Hcode".
    destruct (lea_result_is_Some wpcc (get_a v0.(lw) - get_a wpcc.(lw))) as [wpc Hwpc].
    (* SetA ct2 ct0 cra *)
    iInstrApply "Hcode" (wp_seta_success_reg_any_src _ _ _ _ _ _ _ _ _ _ _ _ _ wpc)
      with "[$HPC $Hct0 $Hcra $Hct2]" as "(HPC & Hct0 & Hcra & Hct2)".
    { by rewrite seta_result_lea_result. }
    assert (resumed_pc wpcc (get_a v0.(lw)) = wpc) as Hresumed
      by (by rewrite /resumed_pc Hwpc).
    (* Lea ca2 csp TrustedStack_offset_cra *)
    iInstr "Hcode".
    { transitivity (Some (a ^+ 1)%a); solve_addr. }
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
    iDestruct (cells_load_acc_tail L p e a π 15 v0 with "[]") as "Hacc_tail".
    { rewrite /cells_load_acc. iModIntro. iExact "Hacc_es". }
    (* copy_context_asm ca3 ca2 cs1 ca4 *)
    iApply (copy_context_load_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (take 15 (drop 1 save)) _ _ (λ i ls, L (S i) (v0 :: ls))
             with "[- $HPC $Hcopy $Hca2 $Hca3 $Hcs1 $Hca4 $HL $Hacc_tail $Hdst]").
    all: try done.
    all: try (rewrite length_take length_drop Hlen; done).
    all: try (lazymatch goal with
              | |- environments.envs_entails _ _ => fail
              | |- disjoint_from_shadow _ _ => fail
              | |- _ ∉ _ => fail
              | _ => cbn; solve_addr
              end).
    { rewrite /disjoint_from_shadow elem_of_disjoint in Hts_shadow |- *.
      intros x Hx HR. eapply Hts_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    { clear; set_solver. }
    iNext. iSplit.
    - iIntros (j ls wd' Hj Hls Hwd' Hout) "Hca2 Hca3 Hcs1 Hca4 Hdst HL".
      iDestruct "Hpost" as "[Hfailed _]".
      iSpecialize ("Hfailed" with "[%]").
      { right. intros (p' & g' & b' & e' & a' & Hw' & Hra' & Hb' & He')
          %error_state_loads_ok_inv.
        cbn in Hw'; simplify_eq.
        rewrite /ErrorState_size in He'. solve_addr. }
      rewrite (_ : ((pc_a ^+ 13%nat) ^+ 1)%a = (pc_a ^+ 14)%a); last solve_addr.
      destruct (Hfault 14%Z ltac:(lia)) as [Hpc_k Htnr].
      rewrite Hpc_k.
      iApply ("Hfailed" $! (off_eic + 14)%Z (S j) (v0 :: ls) (w0 :: wd' ++ drop 16 save)
               with "[//] [%] [%] [-]").
      { rewrite /= length_app length_drop Hwd' Hlen. lia. }
      { rewrite /TrustedStack_offset_hazardPointers /= lookup_app_r Hwd' // lookup_drop //. }
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
      { transitivity (Some (a_switcher_call ^+ off_cci)%a); [solve_addr | done]. }
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" $! g_tstk (v0 :: ls) with "[%] [%] [-]").
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

End Handle_Error_Install_Context.
