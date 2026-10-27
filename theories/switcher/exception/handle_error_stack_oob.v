From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state.

(** * Exception path: the lookup of an error handler

    From [.Lhandle_error_stack_oob] to [.Lhandle_error_found]. The lookup
    reads the export table of the topmost frame of the trusted stack
    ([ctp]), through the capability that the frame stores, moved to the
    base of the table.

    [.Lhandle_error_stack_oob] tests whether the faulting stack pointer has
    room for the [ErrorState] of a stackful handler: [ct0], the stack
    pointer moved down to the base of the [ErrorState], is tagged and its
    cursor is not below its base. A sealing range passes the test (its
    first store then faults), and so does a capability whose cursor is past
    its end (a store of the [ErrorState] then faults). The tag is read as
    the machine sees it: a capability whose tag may have been stripped (for
    instance, by the revocation of its heap object) may fail the test.
    With room, [.Lhandle_error_try_stackful] reads the offset of the
    stackful handler. Without room, or without a stackful handler,
    [.Lhandle_error_try_stackless] reads the offset of the stackless
    handler: with none, it forces the unwind. The stackless handler runs on
    the stack of the caller of the topmost frame: [.Lhandle_stack_rebound]
    restricts it to the part below the cursor, with the cursor at its base;
    for the entry frame, the thread's stack is kept.
    [.Lhandle_stack_recovered] sets [ca0] for a stackless handler.

    The loads of the header fault when the cell of the export table in the
    frame is cleared: the unseal of the callee's entry failed before the
    frame was popped. *)

Section Handle_Error_Stack_Oob.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** [.Lhandle_error_stack_oob]: the room for the [ErrorState], on the
      stack pointer [wct0] moved down to its base from the faulting one
      [wcsp]. The test fails on a word that has not the room, or whose tag
      may have been stripped. *)
  #[local] Lemma handle_error_stack_oob_block_spec (wcsp wct0 wct1 wct2 wcs1 : LWord) :
    lea_result wcsp (- ErrorState_size) = Some wct0 ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_stack_oob" ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    switcher_code ∗
    ▷ ( ( ⌜error_state_fits wcsp⌝ -∗
          ∀ (wct1' wct2' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackful" ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜¬ error_state_fits wcsp ∨ tag_strippable wcsp⌝ -∗
          ∀ (wct1' wct2' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackless" ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hlea) "(HPC & Hct0 & Hct1 & Hct2 & Hcs1 & #Hswitcher & Hpost)".
    pose proof (error_state_fits_lea _ _ Hlea) as Hfits_iff.
    switcher_open_label ".Lhandle_error_stack_oob" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* GetTag ct1 ct0 *)
    iInstrApply "Hcode" wp_gettag_lax with "[$HPC $Hct0 $Hct1]"
      as (ztag) "(HPC & Hct0 & Hct1 & %Hztag)".
    (* Mov cs1 ExportTable_no_handler *)
    iInstr "Hcode".
    destruct (decide (cs1 = cnull)) as [Hcs1_null|_]; first done.
    destruct (decide (ztag = 0%Z)) as [-> | Hztag_nz].
    { (* Jeq .Lhandle_error_try_stackless ct1 0 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_z with "[$HPC $Hct1]" as "(HPC & Hct1)".
      { reflexivity. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_try_stackless")%a
          by switcher_addr_eq. }
      subst hpost.
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[]"); last iFrame "HPC Hct0 Hct1 Hct2 Hcs1".
      iPureIntro.
      destruct Hztag as [Htag | [_ Hstrip] ]; last (right; by eapply tag_strippable_lea).
      left. intros [Htag_true _]%Hfits_iff. by rewrite Htag_true in Htag. }
    (* Jeq .Lhandle_error_try_stackless ct1 0 *)
    iInstrApply "Hcode" wp_jcond_success_next_r_z with "[$HPC $Hct1]" as "(HPC & Hct1)".
    { cbn [jcond_test get_a lw]; apply Z.eqb_neq; lia. }
    assert (get_tag (lw wct0) = true) as Htag.
    { destruct Hztag as [Hz | [Hz _] ]; last done. destruct (get_tag (lw wct0)); done. }
    (* GetB ct2 ct0 *)
    iInstr "Hcode".
    destruct (Z.leb_spec (get_b (lw wct0)) (get_a (lw wct0))) as [Hbase | Hnot_base].
    - (* Jlt .Lhandle_error_try_stackless ct0 ct2 *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct0 $Hct2]"
        as "(HPC & Hct0 & Hct2)".
      { cbn [jcond_test get_a lw]; apply Z.ltb_ge; lia. }
      switcher_change_pc_label ".Lhandle_error_try_stackful".
      subst hpost.
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[]"); last iFrame "HPC Hct0 Hct1 Hct2 Hcs1".
      iPureIntro. by apply Hfits_iff.
    - (* Jlt .Lhandle_error_try_stackless ct0 ct2 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct0 $Hct2]"
        as "(HPC & Hct0 & Hct2)".
      { cbn [jcond_test get_a lw]; apply Z.ltb_lt; lia. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_try_stackless")%a
          by switcher_addr_eq. }
      subst hpost.
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[]"); last iFrame "HPC Hct0 Hct1 Hct2 Hcs1".
      iPureIntro. left. intros (_ & Hle)%Hfits_iff. lia.
  Qed.

  (** The first instructions of [.Lhandle_error_try_stackful] and
      [.Lhandle_error_try_stackless]: load the cell of the export table of
      the frame at [a_tstk], move the capability to its base, and load the
      word at offset [off_eh] of the header, [eh]. The load faults when the
      cell is cleared. *)
  #[local] Lemma export_table_header_load_spec (g_tstk : Locality)
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

    PC ↦ₚ[th] WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → (b_tbl ^+ off_eh)%a ↦ₐ□ WInt eh) ∗
    codefrag_pers pc_a instrs ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ ∗
        ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
        ct1 ↦ᵣ[th] - ∗
        ct2 ↦ᵣ[th] - ∗
        cs0 ↦ᵣ[th] - ∗
        a_tbl_cell ↦ₐ{dq} wcell -∗
        trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 3)%a) ⊤ φ ) ∧
      ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' : LWord),
        ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ ∗
        PC ↦ₚ[th] WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 4)%a ∗
        ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
        ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
        ct2 ↦ᵣ[th] wct2' ∗
        cs0 ↦ᵣ[th] WInt eh ∗
        a_tbl_cell ↦ₐ{dq} wcell -∗
        WP Seq (Instr Executable) @[th] {{ φ }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ φ }}.
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
      iApply ("Hpost" $! p g e a). iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcell". done.
  Qed.

  (** [.Lhandle_error_try_stackful]: the stackful handler. *)
  #[local] Lemma handle_error_try_stackful_spec (g_tstk : Locality)
    (a_tstk b_tbl : Addr) (eh : Z) (wcell wct1 wct2 wcs0 : LWord) (dq : dfrac) :
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    (a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell ->
    withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackful" ∗
    ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜eh ≠ ExportTable_no_handler⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_found" ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt eh ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜eh = ExportTable_no_handler⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackless" ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt eh ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_tbl_cell.
    iIntros (Ha_cell Hcell_bounds Hwcell)
      "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell & #Hheader & #Hswitcher & Hpost)".
    switcher_open_label ".Lhandle_error_try_stackful" "Hswitcher" as "Hcode".
    iApply (export_table_header_load_spec _ _ _ b_tbl _ ExportTable_offset_errorHandler eh
             with "[$HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcell $Hcode Hpost Hcs1]");
      [rewrite /ExportTable_offset_errorHandler /ExportTable_offset_errorHandlerStackless; lia
      | reflexivity | done | cbn; lia | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". iDestruct ("Hheader" with "[//]") as "Heh".
      by iApply handler_stackful_elim. }
    iNext. iSplit.
    - iIntros "(%Hz & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      iDestruct "Hpost" as "[Hfailed _]".
      switcher_merge_pc.
      iApply ("Hfailed" with "[//] []").
      { iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute. }
      iFrame "Hctp Hct1 Hct2 Hcs0 Hcs1 Hcell".
    - iIntros (p g e a wct2') "(%Hw & HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      switcher_hide "Hpost" as hpost.
      destruct (decide (eh = ExportTable_no_handler)) as [-> | Hhandler].
      + (* Jne .Lhandle_error_found cs0 cs1 *)
        iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hcs0 $Hcs1]"
          as "(HPC & Hcs0 & Hcs1)".
        { cbn [jcond_test get_a lw]; apply negb_false_iff, Z.eqb_eq; reflexivity. }
        switcher_change_pc_label ".Lhandle_error_try_stackless".
        subst hpost.
        iDestruct "Hpost" as "(_ & _ & Hpost)".
        iApply ("Hpost" with "[//] [//]").
        iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcell".
      + (* Jne .Lhandle_error_found cs0 cs1 *)
        iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hcs0 $Hcs1]"
          as "(HPC & Hcs0 & Hcs1)".
        { cbn [jcond_test get_a lw]; apply negb_true_iff, Z.eqb_neq; lia. }
        { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_found")%a
            by switcher_addr_eq. }
        subst hpost.
        iDestruct "Hpost" as "(_ & Hpost & _)".
        iApply ("Hpost" with "[//] [//]").
        iFrame "HPC Hctp Hct1 Hct2 Hcs0 Hcs1 Hcell".
  Qed.

  (** [.Lhandle_error_try_stackless]: the stackless handler, and the stack
      of the topmost frame: for a pushed frame, the block falls through to
      [.Lhandle_stack_rebound]; for the entry frame, it goes to
      [.Lhandle_stack_recovered]. *)
  #[local] Lemma handle_error_try_stackless_block_spec (g_tstk : Locality)
    (a_tstk b_tbl : Addr) (d : nat) (ehs : Z)
    (wfcsp wcell wct0 wct1 wct2 wcs0 : LWord) (dq : dfrac) :
    let a_csp_cell := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let a_tbl_cell := (a_tstk ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    wcell = lword_of_word (WInt 0) ∨ (exp_tbl_cap b_tbl wcell.(lw) ∧ wcell.(lprov) = None) ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackless" ∗
    csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
    a_csp_cell ↦ₐ wfcsp ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackless} ehs) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' wcs1' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜ehs = ExportTable_no_handler⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt ehs ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' wcs1' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜ehs ≠ ExportTable_no_handler⌝ -∗
          ⌜d = 0⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_stack_recovered" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wfcsp ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt ehs ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (wct2' wcs1' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜ehs ≠ ExportTable_no_handler⌝ -∗
          ⌜d ≠ 0⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_stack_rebound" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wfcsp ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt ehs ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          a_csp_cell ↦ₐ wfcsp ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_csp_cell a_tbl_cell.
    iIntros (Ha_tstk Ha_tstk_end Hwcell)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell
       & #Hheader & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell)
      as Ha_cell by (subst a_tbl_cell; tstack_unfold; solve_addr).
    assert (withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true) as Hcell_bounds
      by (subst a_tbl_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
    switcher_open_label ".Lhandle_error_try_stackless" "Hswitcher" as "Hcode".
    iApply (export_table_header_load_spec _ _ _ b_tbl _
              ExportTable_offset_errorHandlerStackless ehs
             with "[$HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcell $Hcode Hpost Hcs1 Hcsp Hct0 Hcsp_cell]");
      [rewrite /ExportTable_offset_errorHandlerStackless; lia
      | reflexivity | done | cbn; lia | done | done | done |].
    iSplitR.
    { iIntros "%Hexp". iDestruct ("Hheader" with "[//]") as "Hehs".
      by iApply handler_stackless_elim. }
    iNext. iSplit.
    - iIntros "(%Hz & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      iDestruct "Hpost" as "[Hfailed _]".
      switcher_merge_pc.
      iApply ("Hfailed" with "[//] []").
      { iPureIntro. apply trap_no_resume_switcher_pc. by vm_compute. }
      iFrame "Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hcsp_cell Hcell".
    - iIntros (p g e a wct2') "(%Hw & HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcell)".
      switcher_hide "Hpost" as hpost.
      destruct (decide (ehs = ExportTable_no_handler)) as [-> | Hhandler].
      { (* Jeq .Lcommon_force_unwind cs0 cs1 *)
        iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hcs0 $Hcs1]"
          as "(HPC & Hcs0 & Hcs1)".
        { cbn [jcond_test get_a lw]; apply Z.eqb_eq; reflexivity. }
        { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
            by switcher_addr_eq. }
        subst hpost.
        iDestruct "Hpost" as "(_ & Hpost & _)".
        iApply ("Hpost" with "[//] [//]").
        iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hcsp_cell Hcell". }
      (* Jeq .Lcommon_force_unwind cs0 cs1 *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hcs0 $Hcs1]"
        as "(HPC & Hcs0 & Hcs1)".
      { cbn [jcond_test get_a lw]; apply Z.eqb_neq; lia. }
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
      destruct (decide (d = 0)) as [-> | Hd].
      + assert ((b_trusted_stack ^+ TrustedStack_offset_frames)%a = a_tstk) as Hentry
          by (tstack_unfold; solve_addr).
        (* Jeq .Lhandle_stack_recovered cs1 ctp *)
        iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hcs1 $Hctp]"
          as "(HPC & Hcs1 & Hctp)".
        { cbn [jcond_test get_a lw get_a_sealable]; apply Z.eqb_eq; rewrite Hentry; reflexivity. }
        { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_stack_recovered")%a
            by switcher_addr_eq. }
        subst hpost.
        iDestruct "Hpost" as "(_ & _ & Hpost & _)".
        iApply ("Hpost" with "[//] [//] [//]").
        iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hcsp_cell Hcell".
      + (* Jeq .Lhandle_stack_recovered cs1 ctp *)
        iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hcs1 $Hctp]"
          as "(HPC & Hcs1 & Hctp)".
        { cbn [jcond_test get_a lw get_a_sealable]; apply Z.eqb_neq.
          tstack_unfold. solve_addr. }
        switcher_change_pc_label ".Lhandle_stack_rebound".
        subst hpost.
        iDestruct "Hpost" as "(_ & _ & _ & Hpost)".
        iApply ("Hpost" with "[//] [//] [//]").
        iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hcsp_cell Hcell".
  Qed.

  (** [.Lhandle_stack_rebound]: the stack of the caller of a pushed frame,
      below its cursor, with the cursor at its base. *)
  #[local] Lemma handle_stack_rebound_spec
    (p : Perm) (g : Locality) (b e a : Addr) (π : option AId) (wca1 wca2 : LWord) :
    (b <= a)%a ->
    (a <= e)%a ->
    ((b < a)%a → is_heap_address b = false) ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_stack_rebound" ∗
    ct0 ↦ᵣ[th] WCap true p g b e a @@? π ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_label_pc ".Lhandle_stack_recovered" ∗
        ct0 ↦ᵣ[th] WCap true p g b a b @@? π ∗
        ca1 ↦ᵣ[th] WInt a ∗
        ca2 ↦ᵣ[th] WInt b -∗
        WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hba Hae Hheap) "(HPC & Hct0 & Hca1 & Hca2 & #Hswitcher & Hpost)".
    switcher_open_label ".Lhandle_stack_rebound" "Hswitcher" as "Hcode".
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
    switcher_change_pc_label ".Lhandle_stack_recovered".
    iApply "Hpost". iFrame "HPC Hct0 Hca1 Hca2".
  Qed.

  (** [.Lhandle_stack_recovered]: a stackless handler. *)
  #[local] Lemma handle_stack_recovered_spec (wca0 : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_stack_recovered" ∗
    ca0 ↦ᵣ[th] wca0 ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_found" ∗
        ca0 ↦ᵣ[th] WInt 1 -∗
        WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros "(HPC & Hca0 & #Hswitcher & Hpost)".
    switcher_open_label ".Lhandle_stack_recovered" "Hswitcher" as "Hcode".
    (* Mov ca0 1 *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lhandle_error_found".
    iApply "Hpost". iFrame "HPC Hca0".
  Qed.

  (** From [.Lhandle_error_try_stackless], reached when the stackful
      handler is not invoked. The continuations are those of
      [handle_error_stack_oob_spec]. *)
  #[local] Lemma handle_error_try_stackless_spec (g_tstk : Locality)
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

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_try_stackless" ∗
    csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] WInt ExportTable_no_handler ∗
    ca0 ↦ᵣ[th] WInt 0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    a_csp_cell ↦ₐ tf.(tf_csp) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh ∗ b_tbl ↦ₕ□{stackless} ehs) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ca2 ↦ᵣ[th] wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) ∧
        ( ⌜ehs = ExportTable_no_handler ∧
           (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp)⌝ -∗
          ∀ (wct0' wct1' wct2' wcs0' wcs1' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ca2 ↦ᵣ[th] wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off n : Z)
            (wct0' wct2' wcs1' wca1' wca2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜(n = 0 ∧ off = eh ∧ wct0' = wct0 ∧
            error_state_fits wcsp ∧ eh ≠ ExportTable_no_handler) ∨
           (n = 1 ∧ off = ehs ∧ wct0' = stackless_csp cstk ∧
            ehs ≠ ExportTable_no_handler ∧
            (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp))⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_found" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt off ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          ca0 ↦ᵣ[th] WInt n ∗
          ca1 ↦ᵣ[th] wca1' ∗
          ca2 ↦ᵣ[th] wca2' ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros tf a_csp_cell a_tbl_cell.
    iIntros (Ha_tstk Ha_tstk_end Hframe_csp Hwcell Hcond)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
       & Hcsp_cell & Hcell & #Hheader & #Hswitcher & Hpost)".
    iApply (handle_error_try_stackless_block_spec _ _ _ (length cstk.(cstk_frames)) ehs
             with "[- $HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcsp_cell $Hcell
                     $Hswitcher]");
      [done | done | done |].
    iSplitR.
    { iIntros "%Hexp". by iDestruct ("Hheader" with "[//]") as "[_ $]". }
    iNext; iSplit; [|iSplit; [|iSplit] ].
    - iIntros (Hz off Hoff)
        "(Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      iDestruct "Hpost" as "[Hfailed _]".
      iApply ("Hfailed" with "[//] [//]").
      iFrame "Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
    - (* No stackless handler *)
      iIntros (p g e a wct2' wcs1' Hw Hehs)
        "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      iDestruct "Hpost" as "[_ [Hunwind _] ]".
      iApply ("Hunwind" with "[]"); first (iPureIntro; split; [done | exact Hcond]).
      iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
    - (* The entry frame: its stack as is *)
      iIntros (p g e a wct2' wcs1' Hw Hehs Hd)
        "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      iDestruct "Hpost" as "[_ [_ Hfound] ]".
      assert (stackless_csp cstk = tf.(tf_csp)) as Hcsp_entry.
      { destruct cstk as [ef [|frm frms] ]; cbn in Hd |- *; [done | lia]. }
      iApply (handle_stack_recovered_spec with "[- $HPC $Hca0 $Hswitcher]").
      iNext; iIntros "(HPC & Hca0)".
      iApply ("Hfound" $! p g e a ehs 1%Z (stackless_csp cstk) with "[//] [] [-]").
      { iPureIntro. right. split_and!; done. }
      rewrite Hcsp_entry.
      iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
    - (* A pushed frame: the rebound *)
      iIntros (p g e a wct2' wcs1' Hw Hehs Hd)
        "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcsp_cell & Hcell)".
      iDestruct "Hpost" as "[_ [_ Hfound] ]".
      destruct Hframe_csp as (p' & g' & b' & e' & a' & Htf_csp & Hba & Hae & Hheap).
      { destruct cstk as [ef [|frm frms] ]; cbn in Hd |- *; [lia | done]. }
      assert (stackless_csp cstk = lword_of_word (WCap true p' g' b' a' b')) as Hcsp_frame.
      { destruct cstk as [ef [|frm frms] ]; cbn in Hd, Htf_csp |- *; first lia.
        rewrite /tf /top_tframe /= in Htf_csp. by rewrite Htf_csp. }
      rewrite Htf_csp.
      iApply (handle_stack_rebound_spec with "[- $HPC $Hct0 $Hca1 $Hca2 $Hswitcher]");
        [done | done | |].
      { intros Hlt. eapply disjoint_from_heap_not_in; first exact Hheap.
        rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hct0 & Hca1 & Hca2)".
      iApply (handle_stack_recovered_spec with "[- $HPC $Hca0 $Hswitcher]").
      iNext; iIntros "(HPC & Hca0)".
      iApply ("Hfound" $! p g e a ehs 1%Z (stackless_csp cstk) with "[//] [] [-]").
      { iPureIntro. right. split_and!; done. }
      rewrite Hcsp_frame.
      iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
  Qed.

  (** From [.Lhandle_error_stack_oob]: the lookup of an error handler in the
      export table of the topmost frame of [cstk], at [a_tstk], whose cell
      of the export table holds [wcell], cleared or a capability to the
      table at [b_tbl] (without identifier), whose header declares the
      handler offsets [eh] and [ehs]. [wcsp] is the faulting stack pointer
      and [ct0] holds [wct0], [wcsp] moved down to the base of the
      [ErrorState]. Outcomes:
      - the cell is cleared: the load of the header faults;
      - no handler is invoked: the stackless handler is absent, and the
        stackful one is absent or has no room;
      - a handler is found, at offset [off] of the PCC of the table: the
        stackful one ([ca0] is 0), with [wct0] in [ct0], or the stackless
        one ([ca0] is 1), on [stackless_csp cstk]. *)
  Lemma handle_error_stack_oob_spec (g_tstk : Locality)
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

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_stack_oob" ∗
    csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] WInt 0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    a_csp_cell ↦ₐ tf.(tf_csp) ∗
    a_tbl_cell ↦ₐ{dq} wcell ∗
    (⌜exp_tbl_cap b_tbl wcell.(lw)⌝ → b_tbl ↦ₕ□{stackful} eh ∗ b_tbl ↦ₕ□{stackless} ehs) ∗
    switcher_code ∗
    ▷ ( ( ⌜wcell = lword_of_word (WInt 0)⌝ -∗
          ∀ off : Z,
          ⌜trap_no_resume (switcher_pc off)⌝ -∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          cs0 ↦ᵣ[th] - ∗
          cs1 ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ca2 ↦ᵣ[th] wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) ∧
        ( ⌜ehs = ExportTable_no_handler ∧
           (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp)⌝ -∗
          ∀ (wct0' wct1' wct2' wcs0' wcs1' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ca2 ↦ᵣ[th] wca2 ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ∀ (p : Perm) (g : Locality) (e a : Addr) (off n : Z)
            (wct0' wct2' wcs1' wca1' wca2' : LWord),
          ⌜wcell = lword_of_word (WCap true p g b_tbl e a)⌝ -∗
          ⌜(n = 0 ∧ off = eh ∧ wct0' = wct0 ∧
            error_state_fits wcsp ∧ eh ≠ ExportTable_no_handler) ∨
           (n = 1 ∧ off = ehs ∧ wct0' = stackless_csp cstk ∧
            ehs ≠ ExportTable_no_handler ∧
            (error_state_fits wcsp → eh = ExportTable_no_handler ∨ tag_strippable wcsp))⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_found" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ctp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] WCap true p g b_tbl e b_tbl ∗
          ct2 ↦ᵣ[th] wct2' ∗
          cs0 ↦ᵣ[th] WInt off ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          ca0 ↦ᵣ[th] WInt n ∗
          ca1 ↦ᵣ[th] wca1' ∗
          ca2 ↦ᵣ[th] wca2' ∗
          a_csp_cell ↦ₐ tf.(tf_csp) ∗
          a_tbl_cell ↦ₐ{dq} wcell -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros tf a_csp_cell a_tbl_cell.
    iIntros (Ha_tstk Ha_tstk_end Hframe_csp Hwcell Hlea)
      "(HPC & Hcsp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1 & Hca0 & Hca1 & Hca2
       & Hcsp_cell & Hcell & #Hheader & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [nfit Hfit].
    iApply (handle_error_stack_oob_block_spec with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcs1 $Hswitcher]");
      first exact Hlea.
    iNext; iSplit.
    - (* Room for the [ErrorState]: the stackful handler *)
      iIntros (Hfits wct1' wct2') "(HPC & Hct0 & Hct1 & Hct2 & Hcs1)".
      assert ((a_tstk + TrustedStackFrame_offset_calleeExportTable)%a = Some a_tbl_cell)
        as Ha_cell by (subst a_tbl_cell; tstack_unfold; solve_addr).
      assert (withinBounds b_trusted_stack e_trusted_stack a_tbl_cell = true) as Hcell_bounds
        by (subst a_tbl_cell; rewrite /withinBounds; tstack_unfold; solve_addr).
      iApply (handle_error_try_stackful_spec _ _ b_tbl eh
               with "[- $HPC $Hctp $Hct1 $Hct2 $Hcs0 $Hcs1 $Hcell $Hswitcher]");
        [done | done | done |].
      iSplitR.
      { iIntros "%Hexp". by iDestruct ("Hheader" with "[//]") as "[$ _]". }
      iNext; iSplit; [|iSplit].
      + iIntros (Hz off Hoff) "(Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell)".
        iDestruct "Hpost" as "[Hfailed _]".
        iApply ("Hfailed" with "[//] [//]").
        iFrame "Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
      + (* The stackful handler *)
        iIntros (p g e a wct2'' Hw Heh)
          "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell)".
        iDestruct "Hpost" as "[_ [_ Hfound] ]".
        iApply ("Hfound" $! p g e a eh 0%Z wct0 with "[//] [] [-]").
        { iPureIntro. left. split_and!; done. }
        iFrame "HPC Hcsp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hcsp_cell Hcell".
      + (* No stackful handler *)
        iIntros (p g e a wct2'' Hw Heh)
          "(HPC & Hctp & Hct1 & Hct2 & Hcs0 & Hcs1 & Hcell)".
        iApply (handle_error_try_stackless_spec with
                 "[$HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                   $Hcsp_cell $Hcell $Hheader $Hswitcher $Hpost]"); try done.
        intros _. by left.
    - (* No room for the [ErrorState] *)
      iIntros (Hno_room wct1' wct2') "(HPC & Hct0 & Hct1 & Hct2 & Hcs1)".
      iApply (handle_error_try_stackless_spec with
               "[$HPC $Hcsp $Hctp $Hct0 $Hct1 $Hct2 $Hcs0 $Hcs1 $Hca0 $Hca1 $Hca2
                 $Hcsp_cell $Hcell $Hheader $Hswitcher $Hpost]"); try done.
      intros Hfits. right. destruct Hno_room as [Hno_room | Hstrip]; [done | done].
  Qed.

End Handle_Error_Stack_Oob.
