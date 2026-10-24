From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state.

(** * Exception path, blocks 25-29: the lookup of an error handler

    The lookup reads the export table of the topmost frame of the trusted
    stack ([ctp]), through the capability that the frame stores, moved to
    the base of the table.

    Block 25 ([.Lhandle_error_stack_oob]) tests whether the faulting stack
    pointer has room for the [ErrorState] of a stackful handler: [ct0],
    the stack pointer moved down to the base of the [ErrorState], is
    tagged and its cursor is not below its base. A sealing range passes
    the test (its first store then faults), and so does a capability whose
    cursor is past its end (a store of the [ErrorState] then faults). The
    tag is read as the machine sees it: a capability whose tag may have
    been stripped (for instance, by the revocation of its heap object) may
    fail the test.
    With room, block 26 ([.Lhandle_error_try_stackful]) reads the offset of
    the stackful handler. Without room, or without a stackful handler, block
    27 ([.Lhandle_error_try_stackless]) reads the offset of the stackless
    handler: with none, it forces the unwind. The stackless handler runs on
    the stack of the caller of the topmost frame: block 28
    ([.Lhandle_stack_rebound]) restricts it to the part below the cursor,
    with the cursor at its base; for the entry frame, the thread's stack is
    kept. Block 29 ([.Lhandle_stack_recovered]) sets [ca0] for a stackless
    handler.

    The loads of the header fault when the cell of the export table in the
    frame is cleared: the unseal of the callee's entry failed before the
    frame was popped. *)

Section Switcher_Exception_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 25: the room for the [ErrorState], on the stack pointer [wct0]
      moved down to its base from the faulting one [wcsp]. The test fails on
      a word that has not the room, or whose tag may have been stripped. *)
  #[local] Lemma switcher_exception_block_25_spec_aux
    (pc_a : Addr) (wcsp wct0 wct1 wct2 wcs1 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 25))%a ->
    (pc_a + 15)%a = Some (pc_a ^+ 15)%a ->
    lea_result wcsp (- ErrorState_size) = Some wct0 ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs1 ↦ᵣ wcs1 ∗
    codefrag_pers pc_a (switcher_instrs_n 25) ∗
    ▷ ( ∀ (wct1' wct2' : LWord) (off : Z),
          ⌜(error_state_fits wcsp ∧ off = 9%Z) ∨
           ((¬ error_state_fits wcsp ∨ tag_strippable wcsp) ∧ off = 15%Z)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ off)%a ∗
          ct0 ↦ᵣ wct0 ∗
          ct1 ↦ᵣ wct1' ∗
          ct2 ↦ᵣ wct2' ∗
          cs1 ↦ᵣ WInt ExportTable_no_handler ∗
          codefrag_pers pc_a (switcher_instrs_n 25) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hstackless Hlea) "(HPC & Hct0 & Hct1 & Hct2 & Hcs1 & #Hcode & Hpost)".
    pose proof (error_state_fits_lea _ _ Hlea) as Hfits_iff.
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* GetTag ct1 ct0 *)
    iInstrApply "Hcode" wp_gettag_lax with "[$HPC $Hct0 $Hct1]"
      as (ztag) "(HPC & Hct0 & Hct1 & %Hztag)".
    (* Mov cs1 ExportTable_no_handler *)
    iInstr "Hcode".
    destruct (decide (cs1 = cnull)) as [Hcs1_null|_]; first done.
    destruct (decide (ztag = 0%Z)) as [-> | Hztag_nz].
    { (* Jne 2 ct1 0 *)
      iInstr "Hcode".
      (* Jmp .Lhandle_error_try_stackless *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ 15)%a); solve_addr. }
      iApply ("Hpost" $! _ _ 15%Z). iFrame "∗ Hcode". iPureIntro. right. split; last done.
      destruct Hztag as [Htag | [_ Hstrip] ]; last (right; by eapply tag_strippable_lea).
      left. intros [Htag_true _]%Hfits_iff. by rewrite Htag_true in Htag. }
    (* Jne 2 ct1 0 *)
    iInstr "Hcode".
    { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
    assert (get_tag (lw wct0) = true) as Htag.
    { destruct Hztag as [Hz | [Hz _] ]; last done. destruct (get_tag (lw wct0)); done. }
    (* GetA ct1 ct0 *)
    iInstr "Hcode".
    (* GetB ct2 ct0 *)
    iInstr "Hcode".
    (* Le ct1 ct2 ct1 *)
    iInstr "Hcode".
    destruct (Z.leb_spec (get_b (lw wct0)) (get_a (lw wct0))) as [Hbase | Hnot_base]; cbn.
    - (* Jne 2 ct1 0 *)
      iInstr "Hcode".
      iApply ("Hpost" $! _ _ 9%Z). iFrame "∗ Hcode". iPureIntro. left.
      split; last done. by apply Hfits_iff.
    - (* Jne 2 ct1 0 *)
      iInstr "Hcode".
      (* Jmp .Lhandle_error_try_stackless *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ 15)%a); solve_addr. }
      iApply ("Hpost" $! _ _ 15%Z). iFrame "∗ Hcode". iPureIntro. right.
      split; last done. left. intros (_ & Hle)%Hfits_iff. lia.
  Qed.

  (** The first instructions of blocks 26 and 27: load the cell of the
      export table of the frame at [a_tstk], move the capability to its
      base, and load the word at offset [off_eh] of the header, [eh]. The
      load faults when the cell is cleared. *)
  #[local] Lemma switcher_exception_header_load_spec
    (pc_a a_tstk b_tbl : Addr) (instrs : list Word) (off_eh eh : Z)
    (wcell wct1 wct2 wcs0 : LWord) (dq : dfrac) φ :
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    (0 <= off_eh <= ExportTable_offset_errorHandlerStackless)%Z ->
    take 4 instrs =
      encodeInstrsW [ machine_instructions.CLoad ct1 ctp TrustedStackFrame_offset_calleeExportTable;
                      GetB cs0 ct1; SetA ct1 ct1 (inr cs0);
                      machine_instructions.CLoad cs0 ct1 off_eh ] ->
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length instrs)%a ->
    (4 <= length instrs)%nat ->
    (a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell ->
    withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → (b_tbl ^+ off_eh)%a ↦ₐ□ WInt eh) ∗
    codefrag_pers pc_a instrs ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
        ct1 ↦ᵣ - ∗
        ct2 ↦ᵣ - ∗
        cs0 ↦ᵣ - ∗
        a_tbl_cell ↦ₐ{dq} wcell -∗
        trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 3)%a) ⊤ φ ) ∧
      ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' : LWord),
        ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ ∗
        PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 4)%a ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
        ct1 ↦ᵣ WCap true p g b_tbl e b_tbl ∗
        ct2 ↦ᵣ wct2' ∗
        cs0 ↦ᵣ WInt eh ∗
        a_tbl_cell ↦ₐ{dq} wcell -∗
        WP Seq (Instr Executable) {{ φ }} ) )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    intros a_tbl_cell.
    iIntros (Hoff Hinstrs Hsub Hlen Ha_cell Hcell_bounds Hwcell)
      "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcell & #Hheader & #Hcode_all & Hpost)".
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    iAssert (codefrag_pers pc_a (take 4 instrs)) as "Hcode".
    { rewrite -{1}(take_drop 4 instrs).
      by iDestruct (codefrag_app_pers with "Hcode_all") as "[$ _]". }
    rewrite Hinstrs.
    codefrag_facts "Hcode".
    assert (SubBounds b_switcher e_switcher pc_a (pc_a ^+ 4)%a) as Hsub4.
    { revert Hsub. rewrite /SubBounds. solve_addr. }
    (* CLoad ct1 ctp TrustedStackFrame_offset_calleeExportTable *)
    iInstrApply "Hcode"
      (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ct1 ctp
         TrustedStackFrame_offset_calleeExportTable)
      with "[$HPC $Hct1 $Hctp $Hcell]" as "(HPC & Hct1 & Hctp & Hcell)".
    { eapply disjoint_from_shadow_not_in; [exact Hts_shadow | exact Hcell_bounds]. }
    rewrite lload_word_RWL.
    destruct Hwcell as [-> | (Htbl & Hprov)].
    - (* GetB cs0 ct1 *)
      iInstr "Hcode".
      (* SetA ct1 ct1 cs0 *)
      iInstr "Hcode".
      (* CLoad cs0 ct1 off_eh *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with "Hfailed". done.
    - iDestruct ("Hheader" with "[//]") as "Heh".
      destruct Htbl as (p & g & e & a & Hw & Hread & Hbnd & Hshadow & _).
      destruct wcell as [w π]; cbn in Hw, Hprov; subst w π.
      (* GetB cs0 ct1 *)
      iInstr "Hcode".
      (* SetA ct1 ct1 cs0 *)
      iInstr "Hcode".
      (* CLoad cs0 ct1 off_eh *)
      iInstrApply "Hcode"
        (wp_load_success_notinstr_imm _ cs0 ct1 _ _ _ _ _ _ _ _ _ _ _ _ _ _
           (b_tbl ^+ off_eh)%a _ _ _ _ _ 1%Qp)
        with "[$HPC $Hcs0 $Hct1 $Heh]" as "(HPC & Hcs0 & Hct1 & _)".
      { eapply disjoint_from_shadow_not_in; [exact Hshadow | rewrite /withinBounds; solve_addr]. }
      { done. }
      { split; first done. rewrite /withinBounds; solve_addr. }
      { solve_addr. }
      { iApply deref_res_none. }
      iDestruct "Hpost" as "[_ Hpost]".
      iEval (rewrite /lload_word /lift_word /= load_word_int) in "Hcs0".
      iApply ("Hpost" $! p g e a). iFrame. done.
  Qed.

  (** Block 26: the stackful handler. *)
  #[local] Lemma switcher_exception_block_26_spec_aux
    (pc_a a_tstk b_tbl : Addr) (eh : Z) (wcell wct1 wct2 wcs0 : LWord) (dq : dfrac) :
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 26))%a ->
    (pc_a + 25)%a = Some (pc_a ^+ 25)%a ->
    (a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell ->
    withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ WInt ExportTable_no_handler ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh) ∗
    codefrag_pers pc_a (switcher_instrs_n 26) ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ WInt ExportTable_no_handler ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 3)%a) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off : Z) (wct2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ ∗
          ⌜(eh ≠ ExportTable_no_handler ∧ off = 25%Z) ∨
           (eh = ExportTable_no_handler ∧ off = 6%Z)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ off)%a ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt eh ∗
          cs1 ↦ᵣ WInt ExportTable_no_handler ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_tbl_cell.
    iIntros (Hsub Hfound Ha_cell Hcell_bounds Hwcell)
      "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell & #Hheader & #Hcode & Hpost)".
    iApply (switcher_exception_header_load_spec _ _ b_tbl _ ExportTable_offset_errorHandler eh
             with "[$HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcell $Hcode Hpost Hcs1]");
      [rewrite /ExportTable_offset_errorHandler /ExportTable_offset_errorHandlerStackless; lia
      | reflexivity | done | cbn; lia | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". iDestruct ("Hheader" with "[//]") as "Heh".
      by iApply handler_stackful_elim. }
    iNext. iSplit.
    - iIntros "(%Hz & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      iDestruct "Hpost" as "[Hfailed _]". iApply "Hfailed". by iFrame.
    - iIntros (p g e a wct2') "(%Hw & HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      codefrag_facts "Hcode".
      rewrite /switcher_instrs_n /assembled_switcher_n.
      (* Sub ct2 cs0 cs1 *)
      iInstr "Hcode".
      iDestruct "Hpost" as "[_ Hpost]".
      destruct (decide (eh = ExportTable_no_handler)) as [-> | Hhandler].
      + rewrite Z.sub_diag.
        (* Jne .Lhandle_error_found ct2 0 *)
        iInstr "Hcode".
        iApply ("Hpost" $! p g e a 6%Z). iFrame. iPureIntro. split; first done. by right.
      + (* Jne .Lhandle_error_found ct2 0 *)
        iInstr "Hcode".
        { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
        { transitivity (Some (pc_a ^+ 25)%a); solve_addr. }
        iApply ("Hpost" $! p g e a 25%Z). iFrame. iPureIntro. split; first done. by left.
  Qed.

  (** Block 27: the stackless handler, and the stack of the topmost frame:
      for a pushed frame, the block falls through to the rebound; for the
      entry frame, it goes to [.Lhandle_stack_recovered]. *)
  #[local] Lemma switcher_exception_block_27_spec_aux
    (pc_a a_tstk b_tbl : Addr) (d : nat) (ehs : Z)
    (wfcsp wcell wct0 wct1 wct2 wcs0 : LWord) (dq : dfrac) :
    let a_csp_cell := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 27))%a ->
    (pc_a + (-75))%a = Some (pc_a ^+ (-75))%a ->
    (pc_a + 18)%a = Some (pc_a ^+ 18)%a ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ tstack_cap ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ WInt ExportTable_no_handler ∗
    a_csp_cell ↦ₐ wfcsp ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackless} ehs) ∗
    codefrag_pers pc_a (switcher_instrs_n 27) ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0 ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ WInt ExportTable_no_handler ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 3)%a) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off : Z) (wct0' wct2' wcs1' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ ∗
          ⌜(ehs = ExportTable_no_handler ∧ off = (-75)%Z ∧ wct0' = wct0) ∨
           (ehs ≠ ExportTable_no_handler ∧ d = 0 ∧ off = 18%Z ∧ wct0' = wfcsp) ∨
           (ehs ≠ ExportTable_no_handler ∧ d ≠ 0 ∧ off = 14%Z ∧ wct0' = wfcsp)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ off)%a ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt ehs ∗
          cs1 ↦ᵣ wcs1' ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_csp_cell a_tbl_cell.
    iIntros (Hsub Hunwind Hrecovered Ha_tstk Ha_tstk_end Hwcell)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell
       & #Hheader & #Hcode & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell)
      as Ha_cell by (subst a_tbl_cell; tstack_unfold; solve_addr).
    assert (withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true) as Hcell_bounds
      by (subst a_tbl_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
    iApply (switcher_exception_header_load_spec _ _ b_tbl _
              ExportTable_offset_errorHandlerStackless ehs
             with "[$HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcell $Hcode Hpost Hcs1 Hcsp Hct0 Hcsp_cell]");
      [rewrite /ExportTable_offset_errorHandlerStackless; lia
      | reflexivity | done | cbn; lia | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". iDestruct ("Hheader" with "[//]") as "Hehs".
      by iApply handler_stackless_elim. }
    iNext. iSplit.
    - iIntros "(%Hz & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      iDestruct "Hpost" as "[Hfailed _]". iApply "Hfailed". by iFrame.
    - iIntros (p g e a wct2') "(%Hw & HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      codefrag_facts "Hcode".
      rewrite /switcher_instrs_n /assembled_switcher_n.
      (* Sub ct2 cs0 cs1 *)
      iInstr "Hcode".
      iDestruct "Hpost" as "[_ Hpost]".
      destruct (decide (ehs = ExportTable_no_handler)) as [-> | Hhandler].
      { rewrite Z.sub_diag.
        (* Jne 2 ct2 0 *)
        iInstr "Hcode".
        (* Jmp .Lcommon_force_unwind *)
        iInstr "Hcode".
        { transitivity (Some (pc_a ^+ (-75))%a); solve_addr. }
        iApply ("Hpost" $! p g e a (-75)%Z). iFrame. iPureIntro. split; first done. by left. }
      (* Jne 2 ct2 0 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      (* CLoad ct0 ctp TrustedStackFrame_offset_csp *)
      iInstrApply "Hcode"
        (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ ct0 ctp TrustedStackFrame_offset_csp)
        with "[$HPC $Hct0 $Hctp $Hcsp_cell]" as "(HPC & Hct0 & Hctp & Hcsp_cell)".
      { subst a_csp_cell; tstack_unfold; solve_addr. }
      { subst a_csp_cell; tstk_not_shadow Hts_shadow. }
      { subst a_csp_cell; rewrite /withinBounds; tstack_unfold; solve_addr. }
      rewrite lload_word_RWL.
      rewrite /tstack_cap.
      (* Lea cs1 csp TrustedStack_offset_frames *)
      iInstr "Hcode".
      { transitivity (Some (b_trusted_stack ^+ TrustedStack_offset_frames)%a);
          tstack_unfold; solve_addr. }
      (* GetA cs1 cs1 *)
      iInstr "Hcode".
      (* GetA ct2 ctp *)
      iInstr "Hcode".
      (* Sub cs1 cs1 ct2 *)
      iInstr "Hcode".
      destruct (decide (d = 0)) as [-> | Hd].
      + assert ((b_trusted_stack ^+ TrustedStack_offset_frames)%a = a_tstk) as Hentry
          by (tstack_unfold; solve_addr).
        rewrite Hentry Z.sub_diag.
        (* Jne 2 cs1 0 *)
        iInstr "Hcode".
        (* Jmp .Lhandle_stack_recovered *)
        iInstr "Hcode".
        { transitivity (Some (pc_a ^+ 18)%a); solve_addr. }
        iApply ("Hpost" $! p g e a 18%Z). iFrame. iPureIntro. split; first done.
        right; left. done.
      + (* Jne 2 cs1 0 *)
        iInstr "Hcode".
        { apply negb_true_iff, Z.eqb_neq. cbn. tstack_unfold. solve_addr. }
        iApply ("Hpost" $! p g e a 14%Z). iFrame. iPureIntro. split; first done.
        right; right. done.
  Qed.

  (** Block 28: the stack of the caller of a pushed frame, below its
      cursor, with the cursor at its base. *)
  #[local] Lemma switcher_exception_block_28_spec_aux
    (pc_a : Addr) (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (wca1 wca2 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 28))%a ->
    (b <= a)%a ->
    (a <= e)%a ->
    ((b < a)%a → is_heap_address b = false) ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ct0 ↦ᵣ WCap true p g b e a @@? π ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    codefrag_pers pc_a (switcher_instrs_n 28) ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 4)%a ∗
        ct0 ↦ᵣ WCap true p g b a b @@? π ∗
        ca1 ↦ᵣ WInt a ∗
        ca2 ↦ᵣ WInt b ∗
        codefrag_pers pc_a (switcher_instrs_n 28) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hba Hae Hheap) "(HPC & Hct0 & Hca1 & Hca2 & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* GetA ca1 ct0 *)
    iInstr "Hcode".
    (* GetB ca2 ct0 *)
    iInstr "Hcode".
    (* SetA ct0 ct0 ca2 *)
    iInstr "Hcode".
    (* Subseg ct0 ct0 ca2 ca1 *)
    iInstr "Hcode".
    { rewrite /isWithin. solve_addr. }
    { intros _ Hlt. by apply Hheap. }
    iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Block 29: a stackless handler. *)
  #[local] Lemma switcher_exception_block_29_spec_aux (pc_a : Addr) (wca0 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 29))%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ca0 ↦ᵣ wca0 ∗
    codefrag_pers pc_a (switcher_instrs_n 29) ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
        ca0 ↦ᵣ WInt 1 ∗
        codefrag_pers pc_a (switcher_instrs_n 29) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* Mov ca0 1 *)
    iInstr "Hcode".
    iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Blocks 27-29, from [.Lhandle_error_try_stackless], reached when the
      stackful handler is not invoked. The continuations are those of
      [switcher_handler_lookup_spec]. *)
  #[local] Lemma switcher_handler_try_stackless_spec
    (cstk : CSTK) (a_tstk b_tbl : Addr) (eh ehs : Z)
    (wcsp wcell wct0 wct1 wct2 wcs0 wca1 wca2 : LWord) (dq : dfrac) :
    let tf := top_tframe cstk in
    let a_csp_cell := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    (b_trusted_stack + tstack_frame_offset (length cstk.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (cstk.(cstk_frames) ≠ [] →
     ∃ (p : Perm) (g : Locality) (b e a : Addr),
       tf.(tf_csp) = lword_of_word (WCap true p g b e a) ∧
       (b <= a)%a ∧ (a <= e)%a ∧
       disjoint_from_heap b e) ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->
    (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp) ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_try_stackless" ∗
    csp ↦ᵣ tstack_cap ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ WInt ExportTable_no_handler ∗
    ca0 ↦ᵣ WInt 0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    a_csp_cell ↦ₐ tf.(tf_csp) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh ∗ b_tbl ↦ₕ□{stackless} ehs) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ⌜ehs = ExportTable_no_handler ∧
           (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp)⌝ -∗
          ∀ (wct0' wct1' wct2' wcs0' wcs1' : LWord),
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ wcs0' ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off n : Z)
            (wct0' wct2' wcs1' wca1' wca2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜(n = 0 ∧ off = eh ∧ wct0' = wct0 ∧
            error_state_fits wcsp ∧ eh ≠ ExportTable_no_handler) ∨
           (n = 1 ∧ off = ehs ∧ wct0' = stackless_csp cstk ∧
            ehs ≠ ExportTable_no_handler ∧
            (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp))⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lhandle_error_found" ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ WInt n ∗
          ca1 ↦ᵣ wca1' ∗
          ca2 ↦ᵣ wca2' ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros tf a_csp_cell a_tbl_cell.
    iIntros (Ha_tstk Ha_tstk_end Hframe_csp Hwcell Hcond)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
       & Hcsp_cell & Hcell & #Hheader & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    (* Block 27 *)
    switcher_focus_block (switcher_block ".Lhandle_error_try_stackless") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_27_spec_aux _ _ b_tbl (length cstk.(cstk_frames)) ehs
             with "[- $HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcsp_cell $Hcell $Hcode]");
      [done | offsets_compute; solve_addr+Hsize | offsets_compute; solve_addr+Hsize
      | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". by iDestruct ("Hheader" with "[//]") as "[_ $]". }
    iNext; iSplit.
    - iIntros "(%Hz & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[Hfailed _]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 27) ^+ 3)%a =
                   (a_switcher_call ^+ (switcher_block_offset 27 + 3))%a);
        last (offsets_compute; solve_addr+Hsize).
      iApply ("Hfailed" with "[//] []").
      { iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute. }
      iFrame "∗ Hswitcher".
    - iIntros (p g e a off wct0' wct2' wcs1')
        "(%Hw & %Hoff & HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      destruct Hoff as [(-> & -> & ->) | [(Hehs & Hd & -> & ->) | (Hehs & Hd & -> & ->)] ].
      + (* No stackless handler *)
        iDestruct "Hpost" as "[_ [Hunwind _] ]".
        switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
        iApply ("Hunwind" with "[] [-]"); first (iPureIntro; split; [done | exact Hcond]).
        iFrame "∗ Hswitcher".
      + (* The entry frame: its stack as is *)
        iDestruct "Hpost" as "[_ [_ Hfound] ]".
        assert (stackless_csp cstk = tf.(tf_csp)) as Hcsp_entry.
        { destruct cstk as [ef [|frm frms] ]; cbn in Hd |- *; [done | lia]. }
        switcher_change_pc (switcher_label_offset ".Lhandle_stack_recovered").
        switcher_focus_block (switcher_block ".Lhandle_stack_recovered") "Hswitcher"
          as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
        iApply (switcher_exception_block_29_spec_aux with "[- $HPC $Hca0 $Hcode]"); first done.
        iNext; iIntros "(HPC & Hca0 & _)".
        unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
        switcher_change_pc (switcher_label_offset ".Lhandle_error_found").
        iApply ("Hfound" $! p g e a ehs 1%Z (stackless_csp cstk) with "[//] [] [-]").
        { iPureIntro. right. split_and!; done. }
        rewrite Hcsp_entry. iFrame "∗ Hswitcher".
      + (* A pushed frame: the rebound *)
        iDestruct "Hpost" as "[_ [_ Hfound] ]".
        destruct Hframe_csp as (p' & g' & b' & e' & a' & Htf_csp & Hba & Hae & Hheap).
        { destruct cstk as [ef [|frm frms] ]; cbn in Hd |- *; [lia | done]. }
        assert (stackless_csp cstk = lword_of_word (WCap true p' g' b' a' b')) as Hcsp_frame.
        { destruct cstk as [ef [|frm frms] ]; cbn in Hd, Htf_csp |- *; first lia.
          rewrite /tf /top_tframe /= in Htf_csp. by rewrite Htf_csp. }
        rewrite Htf_csp.
        switcher_change_pc (switcher_label_offset ".Lhandle_stack_rebound").
        switcher_focus_block (switcher_block ".Lhandle_stack_rebound") "Hswitcher"
          as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
        iApply (switcher_exception_block_28_spec_aux with "[- $HPC $Hct0 $Hca1 $Hca2 $Hcode]");
          [done | done | done | |].
        { intros Hlt. eapply disjoint_from_heap_not_in; first exact Hheap.
          rewrite /withinBounds; solve_addr. }
        iNext; iIntros "(HPC & Hct0 & Hca1 & Hca2 & _)".
        unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
        switcher_change_pc (switcher_label_offset ".Lhandle_stack_recovered").
        switcher_focus_block (switcher_block ".Lhandle_stack_recovered") "Hswitcher"
          as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
        iApply (switcher_exception_block_29_spec_aux with "[- $HPC $Hca0 $Hcode]"); first done.
        iNext; iIntros "(HPC & Hca0 & _)".
        unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
        switcher_change_pc (switcher_label_offset ".Lhandle_error_found").
        iApply ("Hfound" $! p g e a ehs 1%Z (stackless_csp cstk) with "[//] [] [-]").
        { iPureIntro. right. split_and!; done. }
        rewrite Hcsp_frame. iFrame "∗ Hswitcher".
  Qed.

  (** Blocks 25-29, from [.Lhandle_error_stack_oob]: the lookup of an error
      handler in the export table of the topmost frame of [cstk], at
      [a_tstk], whose cell of the export table holds [wcell], cleared or a
      capability to the table at [b_tbl] (without identifier), whose header
      declares the handler offsets [eh] and [ehs]. [wcsp] is the faulting
      stack pointer and [ct0] holds [wct0], [wcsp] moved down to the base
      of the [ErrorState]. Outcomes:
      - the cell is cleared: the load of the header faults;
      - no handler is invoked: the stackless handler is absent, and the
        stackful one is absent or has no room;
      - a handler is found, at offset [off] of the PCC of the table: the
        stackful one ([ca0] is 0), with [wct0] in [ct0], or the stackless
        one ([ca0] is 1), on [stackless_csp cstk]. *)
  Lemma switcher_handler_lookup_spec
    (cstk : CSTK) (a_tstk b_tbl : Addr) (eh ehs : Z)
    (wcsp wct0 wcell wct1 wct2 wcs0 wcs1 wca1 wca2 : LWord) (dq : dfrac) :
    let tf := top_tframe cstk in
    let a_csp_cell := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    (b_trusted_stack + tstack_frame_offset (length cstk.(cstk_frames)))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    (cstk.(cstk_frames) ≠ [] →
     ∃ (p : Perm) (g : Locality) (b e a : Addr),
       tf.(tf_csp) = lword_of_word (WCap true p g b e a) ∧
       (b <= a)%a ∧ (a <= e)%a ∧
       disjoint_from_heap b e) ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->
    lea_result wcsp (- ErrorState_size) = Some wct0 ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_stack_oob" ∗
    csp ↦ᵣ tstack_cap ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ WInt 0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    a_csp_cell ↦ₐ tf.(tf_csp) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh ∗ b_tbl ↦ₕ□{stackless} ehs) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          cs0 ↦ᵣ - ∗
          cs1 ↦ᵣ - ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          trap_safe (switcher_pc off) ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) ∧
        ( ⌜ehs = ExportTable_no_handler ∧
           (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp)⌝ -∗
          ∀ (wct0' wct1' wct2' wcs0' wcs1' : LWord),
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ wcs0' ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off n : Z)
            (wct0' wct2' wcs1' wca1' wca2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜(n = 0 ∧ off = eh ∧ wct0' = wct0 ∧
            error_state_fits wcsp ∧ eh ≠ ExportTable_no_handler) ∨
           (n = 1 ∧ off = ehs ∧ wct0' = stackless_csp cstk ∧
            ehs ≠ ExportTable_no_handler ∧
            (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp))⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lhandle_error_found" ∗
          csp ↦ᵣ tstack_cap ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ wct2' ∗
          cs0 ↦ᵣ WInt off ∗
          cs1 ↦ᵣ wcs1' ∗
          ca0 ↦ᵣ WInt n ∗
          ca1 ↦ᵣ wca1' ∗
          ca2 ↦ᵣ wca2' ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros tf a_csp_cell a_tbl_cell.
    iIntros (Ha_tstk Ha_tstk_end Hframe_csp Hwcell Hlea)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
       & Hcsp_cell & Hcell & #Hheader & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    pose proof trusted_stack_frames_fit as [nfit Hfit].
    switcher_unfold_code "Hswitcher".
    (* Block 25 *)
    switcher_focus_block (switcher_block ".Lhandle_error_stack_oob") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_25_spec_aux with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcs1 $Hcode]");
      [done | offsets_compute; solve_addr+Hsize | exact Hlea |].
    iNext; iIntros (wct1' wct2' off) "(%Hroom & HPC & Hct0 & Hct1 & Hct2 & Hcs1 & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    destruct Hroom as [(Hfits & ->) | (Hno_room & ->)].
    2: { switcher_change_pc (switcher_label_offset ".Lhandle_error_try_stackless").
         iApply (switcher_handler_try_stackless_spec with
                  "[$HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                    $Hcsp_cell $Hcell $Hheader $Hswitcher $Hpost]"); try done.
         intros Hfits. right. destruct Hno_room as [Hno_room | Hstrip]; [done | done]. }
    (* Block 26 *)
    switcher_change_pc (switcher_label_offset ".Lhandle_error_try_stackful").
    switcher_focus_block (switcher_block ".Lhandle_error_try_stackful") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    assert ((a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell)
      as Ha_cell by (subst a_tbl_cell; tstack_unfold; solve_addr).
    assert (withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true) as Hcell_bounds
      by (subst a_tbl_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
    iApply (switcher_exception_block_26_spec_aux _ _ b_tbl eh
             with "[- $HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcell $Hcode]");
      [done | offsets_compute; solve_addr+Hsize | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". by iDestruct ("Hheader" with "[//]") as "[$ _]". }
    iNext; iSplit.
    - iIntros "(%Hz & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[Hfailed _]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 26) ^+ 3)%a =
                   (a_switcher_call ^+ (switcher_block_offset 26 + 3))%a);
        last (offsets_compute; solve_addr+Hsize).
      iApply ("Hfailed" with "[//] []").
      { iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute. }
      iFrame "∗ Hswitcher".
    - iIntros (p g e a off wct2'')
        "(%Hw & %Hoff & HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      destruct Hoff as [(Heh & ->) | (Heh & ->)].
      + (* The stackful handler *)
        switcher_change_pc (switcher_label_offset ".Lhandle_error_found").
        iDestruct "Hpost" as "[_ [_ Hfound] ]".
        iApply ("Hfound" $! p g e a eh 0%Z wct0 with "[//] [] [-]").
        { iPureIntro. left. split_and!; done. }
        iFrame "∗ Hswitcher".
      + (* No stackful handler *)
        switcher_change_pc (switcher_label_offset ".Lhandle_error_try_stackless").
        iApply (switcher_handler_try_stackless_spec with
                 "[$HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                   $Hcsp_cell $Hcell $Hheader $Hswitcher $Hpost]"); try done.
        intros _. by left.
  Qed.

End Switcher_Exception_Blocks_4.
