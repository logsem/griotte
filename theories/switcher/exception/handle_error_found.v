From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state.

(** * Exception path: the handler found

    [.Lhandle_error_found] counts the fault in the error handler count of
    the topmost frame. An even count (the fault of a running handler) or
    more than [MAX_FAULTS_PER_COMPARTMENT_CALL] faults force the unwind.
    Otherwise, it computes the handler's PC in [cra] from the PCC of the
    export table and the handler offset in [cs0], and its CGP in [cgp];
    [ca0] selects the setup: [.Lhandle_error_stackless_setup] sets the
    arguments and the stack of a stackless handler;
    [.Lhandle_error_stack_setup], the setup of a stackful handler, is in
    [handle_error_stack_setup]. *)

Section Handle_Error_Found.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lhandle_error_found]: the handler of offset [off] was found in
      the export table at [b_tbl], for the topmost frame at [a_tstk], whose
      error handler count is [n]; [ca0] is 0 for a stackful handler, 1 for a
      stackless one. The count becomes [n + 1]. Outcomes:
      - [n] is odd (a fault of a running handler), or [n + 1] exceeds
        [MAX_FAULTS_PER_COMPARTMENT_CALL]: the unwind is forced;
      - otherwise, [cra] holds the handler's PC computed from the PCC of the
        table, [cgp] its CGP, and the PC is at the setup of the handler,
        stackless or stackful. *)
  Lemma handle_error_found_spec
    (d : nat) (a_tstk b_tbl e_tbl : Addr) (p : Perm) (g : Locality) (n off z0 : Z)
    (wpcc wcgp wcra wcgp0 wct2 wcs1 : LWord) :
    let a_cnt_cell := (a_tstk ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    exp_tbl_cap b_tbl (WCap true p g b_tbl e_tbl b_tbl) ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_found" ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct1 ↦ᵣ WCap true p g b_tbl e_tbl b_tbl ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ WInt off ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp0 ∗
    ca0 ↦ᵣ WInt z0 ∗
    a_cnt_cell ↦ₐ WInt n ∗
    (⌜Z.even n = true⌝ → b_tbl ↦ₐ□ wpcc ∗ (b_tbl ^+ ExportTable_offset_cgp)%a ↦ₐ□ wcgp) ∗
    switcher_code ∗
    ▷ ( ( ⌜Z.even n = false ∨ (MAX_FAULTS_PER_COMPARTMENT_CALL < n + 1)%Z⌝ -∗
          ∀ wcra' : LWord,
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ WCap true p g b_tbl e_tbl b_tbl ∗
          ct2 ↦ᵣ wct2 ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ WInt (n + 1) ∗
          cra ↦ᵣ wcra' ∗
          cgp ↦ᵣ wcgp0 ∗
          ca0 ↦ᵣ WInt z0 ∗
          a_cnt_cell ↦ₐ WInt (n + 1) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜Z.even n = true ∧ (n + 1 <= MAX_FAULTS_PER_COMPARTMENT_CALL)%Z⌝ -∗
          ⌜z0 ≠ 0⌝ -∗
          ∀ (wct2' wcs1' : LWord),
          PC ↦ₚ switcher_label_pc ".Lhandle_error_stackless_setup" ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ WCap true p g b_tbl e_tbl b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ wcs1' ∗
          cra ↦ᵣ handler_word (lload_word p wpcc) off ∗
          cgp ↦ᵣ lload_word p wcgp ∗
          ca0 ↦ᵣ WInt z0 ∗
          a_cnt_cell ↦ₐ WInt (n + 1) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜Z.even n = true ∧ (n + 1 <= MAX_FAULTS_PER_COMPARTMENT_CALL)%Z⌝ -∗
          ⌜z0 = 0⌝ -∗
          ∀ (wct2' wcs1' : LWord),
          PC ↦ₚ switcher_label_pc ".Lhandle_error_stack_setup" ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ WCap true p g b_tbl e_tbl b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ wcs1' ∗
          cra ↦ᵣ handler_word (lload_word p wpcc) off ∗
          cgp ↦ᵣ lload_word p wcgp ∗
          ca0 ↦ᵣ WInt z0 ∗
          a_cnt_cell ↦ₐ WInt (n + 1) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_cnt_cell.
    iIntros (Ha_tstk Ha_tstk_end Htbl)
      "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcra & Hcgp & Hca0 & Hcell & #Hheader
       & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [nfit Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_tstk + TrustedStackFrame_offset_errorHandlerCount)%a = Some a_cnt_cell) as Ha_cell
      by (subst a_cnt_cell; tstack_unfold; solve_addr).
    assert (withinBounds b_trusted_stack e_trusted_stack a_cnt_cell = true) as Hcell_bounds
      by (subst a_cnt_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
    assert (is_shadow_address a_cnt_cell = false) as Hcell_shadow.
    { eapply disjoint_from_shadow_not_in; [exact Hts_shadow | exact Hcell_bounds]. }
    switcher_open_label ".Lhandle_error_found" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs1 ctp TrustedStackFrame_offset_errorHandlerCount *)
    iInstr "Hcode".
    { done. }
    { done. }
    rewrite lload_word_RWL.
    (* Add cs1 cs1 1 *)
    iInstr "Hcode".
    (* Store ctp cs1 TrustedStackFrame_offset_errorHandlerCount *)
    iInstr "Hcode".
    iEval (rewrite lstore_word_isWL //) in "Hcell".
    (* LAnd cra cs1 1 *)
    iInstr "Hcode".
    assert (Z.land (n + 1) 1 = if Z.even n then 1 else 0)%Z as Hland.
    { rewrite (Z.land_ones _ 1) // Zmod_even Z.even_add Z.even_1. by destruct (Z.even n). }
    iEval (rewrite Hland) in "Hcra".
    destruct (Z.even n) eqn:Hev.
    2: { (* Jne 2 cra 0 *)
         iInstr "Hcode".
         (* Jmp .Lcommon_force_unwind *)
         iInstr "Hcode".
         { switcher_jump_label ".Lcommon_force_unwind". }
         subst hpost.
         iDestruct "Hpost" as "[Hpost _]".
         iApply ("Hpost" with "[] [-]"); first (iPureIntro; by left).
         iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcra Hcgp Hca0 Hcell". }
    (* Jne 2 cra 0 *)
    iInstr "Hcode".
    (* Mov cra MAX_FAULTS_PER_COMPARTMENT_CALL *)
    iInstr "Hcode".
    destruct (decide (cra = cnull)) as [Hcra_null|_]; first done.
    (* Le cra cs1 cra *)
    iInstr "Hcode".
    rewrite /MAX_FAULTS_PER_COMPARTMENT_CALL.
    destruct (Z.leb_spec (n + 1) 1024) as [Hmax | Hmax].
    2: { (* Jne 2 cra 0 *)
         iInstr "Hcode".
         (* Jmp .Lcommon_force_unwind *)
         iInstr "Hcode".
         { switcher_jump_label ".Lcommon_force_unwind". }
         subst hpost.
         iDestruct "Hpost" as "[Hpost _]".
         iApply ("Hpost" with "[] [-]"); first (iPureIntro; by right).
         iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcra Hcgp Hca0 Hcell". }
    (* Jne 2 cra 0 *)
    iInstr "Hcode".
    destruct Htbl as (p' & g' & e' & a' & Hw & Hread & Hbnd & Hshadow & _).
    injection Hw as <- <- <- _.
    rewrite /ExportTable_offset_errorHandlerStackless in Hbnd.
    iDestruct ("Hheader" with "[//]") as "[Hpcc Hcgp_cell]".
    iEval (rewrite /ExportTable_offset_cgp) in "Hcgp_cell".
    (* CLoad cra ct1 ExportTable_offset_pcc *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ cra ct1 0)
      with "[$HPC $Hcra $Hct1 $Hpcc]" as "(HPC & Hcra & Hct1 & _)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; [exact Hshadow | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp ct1 ExportTable_offset_cgp *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ cgp ct1 1)
      with "[$HPC $Hcgp $Hct1 $Hcgp_cell]" as "(HPC & Hcgp & Hct1 & _)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; [exact Hshadow | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    (* GetB cs1 cra *)
    iInstr "Hcode".
    destruct (lea_result_is_Some (lload_word p wpcc)
                (get_b (lload_word p wpcc).(lw) - get_a (lload_word p wpcc).(lw)))
      as [wr1 Hwr1].
    destruct (lea_result_is_Some wr1 off) as [wr2 Hwr2].
    (* SetA cra cra cs1 *)
    iInstrApply "Hcode" (wp_seta_success_reg_any _ _ _ _ _ _ _ _ _ _ _ _ wr1)
      with "[$HPC $Hcra $Hcs1]" as "(HPC & Hcs1 & Hcra)".
    { by rewrite seta_result_lea_result. }
    (* Lea cra cra cs0 *)
    iInstrApply "Hcode" (wp_lea_success_reg_any _ _ _ _ _ _ _ _ _ _ _ _ wr2)
      with "[$HPC $Hcra $Hcs0]" as "(HPC & Hcs0 & Hcra)".
    assert (handler_word (lload_word p wpcc) off = wr2) as Hhw.
    { by rewrite /handler_word Hwr1 /= Hwr2. }
    rewrite -Hhw.
    destruct (decide (z0 = 0)) as [-> | Hz0].
    - (* Jne 2 ca0 0 *)
      iInstr "Hcode".
      (* Jmp .Lhandle_error_stack_setup *)
      iInstr "Hcode".
      { switcher_jump_label ".Lhandle_error_stack_setup". }
      subst hpost.
      iDestruct "Hpost" as "(_ & _ & Hpost)".
      iApply ("Hpost" with "[//] [//]").
      iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcra Hcgp Hca0 Hcell".
    - (* Jne 2 ca0 0 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      switcher_change_pc_label ".Lhandle_error_stackless_setup".
      subst hpost.
      iDestruct "Hpost" as "(_ & Hpost & _)".
      iApply ("Hpost" with "[//] [//]").
      iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcra Hcgp Hca0 Hcell".
  Qed.

  (** From [.Lhandle_error_stackless_setup]: [ca0] receives the cause of the
      trap (word 18 of the register save area), [ca1] some value of the
      trap, [ca2] 0 and [csp] the handler's stack, from [ct0]. *)
  Lemma handle_error_stackless_setup_spec
    (save_area : list LWord) (wct0 wca0 wca1 wca2 : LWord) :
    length save_area = 21%nat ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_stackless_setup" ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    switcher_code ∗
    ▷ ( ∀ mtval : Z,
        PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_invoke" ∗
        csp ↦ᵣ wct0 ∗
        ct0 ↦ᵣ wct0 ∗
        ca0 ↦ᵣ (save_area !!! 18%nat) ∗
        ca1 ↦ᵣ WInt mtval ∗
        ca2 ↦ᵣ WInt 0 ∗
        [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hlen) "(HPC & Hcsp & Hct0 & Hca0 & Hca1 & Hca2 & Hsave & #Hswitcher & Hpost)".
    destruct (lookup_lt_is_Some_2 save_area 18%nat) as [w18 Hw18]; first lia.
    rewrite (list_lookup_total_correct _ _ _ Hw18).
    iDestruct (tstack_save_area_acc _ _ _ Hw18 with "Hsave") as "[Hs18 Hsave]".
    pose proof (tstack_save_cell_ok 18 ltac:(lia)) as (Hts_18 & Hts_18_bounds & Hts_18_shadow).
    switcher_open_label ".Lhandle_error_stackless_setup" "Hswitcher" as "Hcode".
    rewrite /tstack_cap.
    (* CLoad ca0 csp TrustedStack_offset_mcause *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ca0 csp 18)
      with "[$HPC $Hca0 $Hcsp $Hs18]" as "(HPC & Hca0 & Hcsp & Hs18)".
    rewrite lload_word_RWL.
    (* SpecialRW ca1 mtval cnull *)
    iInstrApply "Hcode" wp_csrr_mtval with "[$HPC $Hca1]" as (mtval) "(HPC & Hca1)".
    (* Mov ca2 0 *)
    iInstr "Hcode".
    (* Mov csp ct0 *)
    iInstr "Hcode".
    (* Jmp .Lhandle_error_handler_invoke *)
    iInstr "Hcode".
    { switcher_jump_label ".Lhandle_error_handler_invoke". }
    iApply "Hpost". iFrame "HPC Hcsp Hct0 Hca0 Hca1 Hca2". by iApply "Hsave".
  Qed.

End Handle_Error_Found.
