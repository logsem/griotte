From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states.

(** * Exception path: [.Lhandle_error]

    [.Lhandle_error] restores mtdc, then tests whether the trap comes from
    the switcher: the PC spilled in the register save area has the base of
    the switcher's PC. A fault of the switcher goes to
    [.Lhandle_error_in_switcher]. Any other trap reloads the interrupted
    stack pointer, tests that the trusted stack has a frame (otherwise the
    thread exits; [frameoffset] always points after the entry frame, so the
    test never succeeds), points [ctp] to the topmost frame, clears [ca0],
    moves the stack pointer [ct0] down by the room for the [ErrorState] of
    a stackful handler, and goes on with the lookup of an error handler, at
    [.Lhandle_error_stack_oob].

    [.Lhandle_error_in_switcher] tests whether the fault is one of the first
    spill of the call path ([.Lswitch_entry_first_spill]): the spilled PC
    has its address. If so, it overwrites the saved return values with
    [-ENOTENOUGHSTACK] and 0, and goes to [.Lcommon_context_install], which
    resumes the interrupted context at [.Lswitch_just_return]; otherwise,
    it forces the unwind. *)

Section Handle_Error.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** [.Lhandle_error]: restore mtdc, then go to [.Lhandle_error_in_switcher]
      for a fault of the switcher, or on with the lookup of an error
      handler. *)
  #[local] Lemma handle_error_block_spec
    (d : nat) (a_tstk : Addr) (save_area : list LWord)
    (wmepcc wmtdc wct0 wct1 wctp wca0 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    length save_area = 21%nat ->
    save_area !! 0%nat = Some wmepcc ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
    csp ↦ᵣ[th] tstack_cap ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ctp ↦ᵣ[th] wctp ∗
    ca0 ↦ᵣ[th] wca0 ∗
    mtdc ↦ₛᵣ wmtdc ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    switcher_code ∗
    ▷ ( ( ⌜get_b wmepcc.(lw) = b_switcher⌝ -∗
          ∀ (wct0' wctp' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_in_switcher" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wmepcc ∗
          ctp ↦ᵣ[th] wctp' ∗
          ca0 ↦ᵣ[th] wca0 ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜get_b wmepcc.(lw) ≠ b_switcher⌝ -∗
          ∀ (wct0' wct1' : LWord),
          ⌜lea_result (save_area !!! 2%nat) (- ErrorState_size) = Some wct0'⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_stack_oob" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_frameoffset.
    iIntros (Ha_tstk Hlen Hmepcc)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hmtdc & Hsave & Hframeoffset & #Hswitcher
       & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    destruct save_area as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    injection Hmepcc as ->.
    rewrite /tstack_save_end /tstack_cap.
    assert ((b_trusted_stack + 21%nat)%a = Some (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a)
      as Hsave_end by (tstack_unfold; solve_addr).
    iRegionSplit "Hsave" as
      "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs16 & Hs17 & Hs18 & Hs19 & Hs20)".
    switcher_open_label ".Lhandle_error" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.

    (* SpecialRW cnull mtdc csp *)
    iInstr "Hcode".
    (* Auipcc ct0 0 *)
    iInstr "Hcode".
    assert ((b_trusted_stack + 0)%a = Some b_trusted_stack) as Hts_0 by solve_addr.
    (* The saved words may be heap capabilities: they are loaded exactly *)
    iAssert (load_witness_res LoadPlain) as "Hwit"; first done.
    (* CLoad ct1 csp 0 *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ct1 csp 0)
      with "[$HPC $Hct1 $Hcsp $Hs0 $Hwit]"
      as (wload) "(%Hload & HPC & Hct1 & Hcsp & Hs0 & _)".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    destruct Hload as (_ & _ & _ & Hload). rewrite lload_word_RWL in Hload. subst wload.
    (* GetB ct0 ct0 *)
    iInstr "Hcode".
    (* GetB ctp ct1 *)
    iInstr "Hcode".
    destruct (decide ((b_switcher : Z) = get_b (lw wmepcc))) as [Hin | Hnot_in].
    - (* A fault of the switcher *)
      (* Jeq .Lhandle_error_in_switcher ct0 ctp *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct0 $Hctp]"
        as "(HPC & Hct0 & Hctp)".
      { cbn [jcond_test get_a lw]; apply Z.eqb_eq; lia. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_in_switcher")%a
          by switcher_addr_eq. }
      subst hpost.
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[]"); first (iPureIntro; lia).
      iFrame "HPC Hcsp Hct0 Hct1 Hctp Hca0 Hmtdc Hframeoffset".
      iRegionMerge. iFrame.
    - (* Jeq .Lhandle_error_in_switcher ct0 ctp *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct0 $Hctp]"
        as "(HPC & Hct0 & Hctp)".
      { cbn [jcond_test get_a lw]; apply Z.eqb_neq; lia. }
      assert ((b_trusted_stack + 2)%a = Some (b_trusted_stack ^+ 2)%a) as Hts_2
        by (tstack_unfold; solve_addr).
      (* CLoad ct0 csp 2 *)
      iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ct0 csp 2)
        with "[$HPC $Hct0 $Hcsp $Hs2 $Hwit]"
        as (wcsp) "(%Hload_csp & HPC & Hct0 & Hcsp & Hs2 & _)".
      { tstk_not_shadow Hts_shadow. }
      { rewrite /withinBounds; tstack_unfold; solve_addr. }
      destruct Hload_csp as (_ & _ & _ & Hload_csp).
      rewrite lload_word_RWL in Hload_csp. subst wcsp.
      assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a = Some a_frameoffset) as Hfo
        by (subst a_frameoffset; tstack_unfold; solve_addr).
      (* CLoad ctp csp TrustedStack_offset_frameoffset *)
      iInstr "Hcode".
      { subst a_frameoffset; tstk_not_shadow Hts_shadow. }
      { done. }
      { split; auto. subst a_frameoffset; rewrite /withinBounds; tstack_unfold; solve_addr. }
      rewrite lload_word_RWL.
      (* Mov ct1 TrustedStack_offset_frames *)
      iInstr "Hcode".
      destruct (decide (ct1 = cnull)) as [Hct1_null|_]; first done.
      (* The trusted stack always has a frame: the thread does not exit *)
      (* Jeq .Lcommon_thread_exit ctp ct1 *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hctp $Hct1]"
        as "(HPC & Hctp & Hct1)".
      { cbn [jcond_test get_a lw]; apply Z.eqb_neq; tstack_unfold; lia. }
      (* Add ctp ctp (- TrustedStackFrame_size) *)
      iInstr "Hcode".
      assert ((b_trusted_stack + (tstack_frameoffset d + - TrustedStackFrame_size))%a = Some a_tstk)
        as Ha_tstk'.
      { rewrite -Ha_tstk. f_equal. tstack_unfold. lia. }
      (* Lea ctp csp ctp *)
      iInstr "Hcode".
      (* Mov ca0 0 *)
      iInstr "Hcode".
      destruct (lea_result_is_Some s2 (- ErrorState_size)) as [wct0' Hlea].
      (* Lea ct0 ct0 (- ErrorState_size) *)
      iInstrApply "Hcode" (wp_lea_success_z_any _ _ _ _ _ _ _ _ _ ct0 s2 wct0')
        with "[$HPC $Hct0]" as "(HPC & Hct0)".
      switcher_change_pc_label ".Lhandle_error_stack_oob".
      subst hpost.
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[] [//]"); first (iPureIntro; lia).
      iFrame "HPC Hcsp Hct0 Hct1 Hctp Hca0 Hmtdc Hframeoffset".
      iRegionMerge. iFrame.
  Qed.

  (** [.Lhandle_error_in_switcher]: a fault at the first spill of the call
      path sets the return values, overwrites them in the register save
      area, and goes to the context install with the PC of
      [.Lswitch_just_return] in [ct2]; any other fault of the switcher
      forces the unwind. *)
  #[local] Lemma handle_error_in_switcher_spec (wmepcc wctp wca0 wca1 wct2 w10 w11 : LWord) :
    let a_first_spill := (a_switcher_call ^+ switcher_label_offset ".Lswitch_entry_first_spill")%a in

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_in_switcher" ∗
    csp ↦ᵣ[th] tstack_cap ∗
    ct1 ↦ᵣ[th] wmepcc ∗
    ctp ↦ᵣ[th] wctp ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ w10 ∗
    (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ w11 ∗
    switcher_code ∗
    ▷ ( ( ⌜get_a wmepcc.(lw) ≠ (a_first_spill : Z)⌝ -∗
          ∀ (wct1' wctp' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] wctp' ∗
          ca0 ↦ᵣ[th] wca0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ct2 ↦ᵣ[th] wct2 ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ w10 ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ w11 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜get_a wmepcc.(lw) = (a_first_spill : Z)⌝ -∗
          ∀ (wct1' wctp' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_context_install" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] wctp' ∗
          ca0 ↦ᵣ[th] WInt ENOTENOUGHSTACK ∗
          ca1 ↦ᵣ[th] WInt 0 ∗
          ct2 ↦ᵣ[th] switcher_label_pc ".Lswitch_just_return" ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ WInt ENOTENOUGHSTACK ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ WInt 0 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_first_spill.
    iIntros "(HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11 & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    rewrite /tstack_cap.
    switcher_open_label ".Lhandle_error_in_switcher" "Hswitcher" as "Hcode".
    (* Auipcc ctp .Lswitch_entry_first_spill *)
    iInstr "Hcode".
    { jump_to (a_switcher_call ^+ switcher_label_offset ".Lswitch_entry_first_spill")%a
        by switcher_addr_eq. }
    destruct (decide (get_a wmepcc.(lw) = (a_first_spill : Z))) as [Hfirst | Hnot_first].
    - (* A fault of the first spill: resume the caller *)
      iDestruct "Hpost" as "[_ Hpost]".
      switcher_hide "Hpost" as hpost.
      (* Jne .Lcommon_force_unwind ct1 ctp *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct1 $Hctp]"
        as "(HPC & Hct1 & Hctp)".
      { cbn [jcond_test get_a lw]. rewrite Hfirst. apply negb_false_iff, Z.eqb_eq.
        reflexivity. }
      (* Mov ca0 ENOTENOUGHSTACK *)
      iInstr "Hcode".
      (* Mov ca1 0 *)
      iInstr "Hcode".
      (* Auipcc ct2 .Lswitch_just_return *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lswitch_just_return")%a
          by switcher_addr_eq. }
      assert ((b_trusted_stack + TrustedStack_offset_ca0)%a =
                Some (b_trusted_stack ^+ TrustedStack_offset_ca0)%a) as Hts_10
        by (rewrite /TrustedStack_offset_ca0; tstack_unfold; solve_addr).
      assert ((b_trusted_stack + TrustedStack_offset_ca1)%a =
                Some (b_trusted_stack ^+ TrustedStack_offset_ca1)%a) as Hts_11
        by (rewrite /TrustedStack_offset_ca1; tstack_unfold; solve_addr).
      (* Store csp ca0 TrustedStack_offset_ca0 *)
      iInstr "Hcode".
      { rewrite /TrustedStack_offset_ca0; tstk_not_shadow Hts_shadow. }
      { rewrite /withinBounds /TrustedStack_offset_ca0; tstack_unfold; solve_addr. }
      (* Store csp ca1 TrustedStack_offset_ca1 *)
      iInstr "Hcode".
      { rewrite /TrustedStack_offset_ca1; tstk_not_shadow Hts_shadow. }
      { rewrite /withinBounds /TrustedStack_offset_ca1; tstack_unfold; solve_addr. }
      (* Jmp .Lcommon_context_install *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_context_install")%a
          by switcher_addr_eq. }
      subst hpost.
      iApply ("Hpost" with "[//]").
      iFrame "HPC Hcsp Hct1 Hctp Hca0 Hca1 Hct2 Hs10 Hs11".
    - (* Any other fault of the switcher: force the unwind *)
      iDestruct "Hpost" as "[Hpost _]".
      (* Jne .Lcommon_force_unwind ct1 ctp *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct1 $Hctp]"
        as "(HPC & Hct1 & Hctp)".
      { cbn [jcond_test get_a lw]. apply negb_true_iff, Z.eqb_neq.
        intros Heq; apply Hnot_first; rewrite Heq; reflexivity. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      iApply ("Hpost" with "[//]").
      iFrame "HPC Hcsp Hct1 Hctp Hca0 Hca1 Hct2 Hs10 Hs11".
  Qed.

  (** From [.Lhandle_error]: restore mtdc, then force the unwind or resume
      the caller of a call path whose first spill faulted, for a fault of
      the switcher, or go on with the lookup of an error handler. The first
      word of the register save area holds the PC of the fault, [wmepcc].
      The trusted stack holds [d] frames above the entry frame, the topmost
      at [a_tstk]. *)
  Lemma handle_error_spec
    (d : nat) (a_tstk : Addr) (save_area : list LWord)
    (wmepcc wmtdc wct0 wct1 wctp wca0 wca1 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_first_spill := (a_switcher_call ^+ switcher_label_offset ".Lswitch_entry_first_spill")%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    length save_area = 21%nat ->
    save_area !! 0%nat = Some wmepcc ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
    csp ↦ᵣ[th] tstack_cap ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ctp ↦ᵣ[th] wctp ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    mtdc ↦ₛᵣ wmtdc ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    switcher_code ∗
    ▷ ( ( ⌜get_b wmepcc.(lw) = b_switcher ∧ get_a wmepcc.(lw) ≠ a_first_spill⌝ -∗
          ∀ (wct0' wct1' wctp' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] wctp' ∗
          ca0 ↦ᵣ[th] wca0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ct2 ↦ᵣ[th] wct2 ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜get_b wmepcc.(lw) = b_switcher ∧ get_a wmepcc.(lw) = a_first_spill⌝ -∗
          ∀ (wct0' wct1' wctp' : LWord),
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_context_install" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] wctp' ∗
          ca0 ↦ᵣ[th] WInt ENOTENOUGHSTACK ∗
          ca1 ↦ᵣ[th] WInt 0 ∗
          ct2 ↦ᵣ[th] switcher_label_pc ".Lswitch_just_return" ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ <[ Z.to_nat TrustedStack_offset_ca0 := (WInt ENOTENOUGHSTACK : LWord) ]>
                 (<[ Z.to_nat TrustedStack_offset_ca1 := (WInt 0 : LWord) ]> save_area) ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜get_b wmepcc.(lw) ≠ b_switcher⌝ -∗
          ∀ (wct0' wct1' : LWord),
          ⌜lea_result (save_area !!! 2%nat) (- ErrorState_size) = Some wct0'⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_stack_oob" ∗
          csp ↦ᵣ[th] tstack_cap ∗
          ct0 ↦ᵣ[th] wct0' ∗
          ct1 ↦ᵣ[th] wct1' ∗
          ctp ↦ᵣ[th] WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
          ca0 ↦ᵣ[th] WInt 0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ct2 ↦ᵣ[th] wct2 ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    intros a_frameoffset a_first_spill.
    iIntros (Ha_tstk Hlen Hmepcc)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave & Hframeoffset
       & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    iApply (handle_error_block_spec with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hca0 $Hmtdc $Hsave $Hframeoffset $Hswitcher]");
      [done | done | done |].
    iNext; iSplit.
    - (* A fault of the switcher *)
      iIntros (Hin wct0' wctp')
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hmtdc & Hsave & Hframeoffset)".
      destruct save_area as
        [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
        [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
        try done.
      rewrite /tstack_save_end.
      assert ((b_trusted_stack + 21%nat)%a = Some (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a)
        as Hsave_end by (tstack_unfold; solve_addr).
      iRegionSplit "Hsave" as
        "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
         & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs16 & Hs17 & Hs18 & Hs19 & Hs20)".
      iApply (handle_error_in_switcher_spec with
               "[- $HPC $Hcsp $Hct1 $Hctp $Hca0 $Hca1 $Hct2 $Hs10 $Hs11 $Hswitcher]").
      iNext; iSplit.
      + iIntros (Hnot_first wct1'' wctp'')
          "(HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11)".
        iDestruct "Hpost" as "[Hpost _]".
        iApply ("Hpost" with "[]"); first (iPureIntro; split; [done | exact Hnot_first]).
        iFrame "HPC Hcsp Hct0 Hct1 Hctp Hca0 Hca1 Hct2 Hmtdc Hframeoffset".
        iRegionMerge. iFrame.
      + iIntros (Hfirst wct1'' wctp'')
          "(HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11)".
        iDestruct "Hpost" as "[_ [Hpost _] ]".
        iApply ("Hpost" with "[]"); first (iPureIntro; split; [done | exact Hfirst]).
        iFrame "HPC Hcsp Hct0 Hct1 Hctp Hca0 Hca1 Hct2 Hmtdc Hframeoffset".
        iClear "Hswitcher". cbn. iRegionMerge. iFrame.
    - (* Any other trap: the lookup of an error handler *)
      iIntros (Hnot_in wct0' wct1' Hlea)
        "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hmtdc & Hsave & Hframeoffset)".
      iDestruct "Hpost" as "[_ [_ Hpost] ]".
      iApply ("Hpost" with "[//] [//]").
      iFrame "HPC Hcsp Hct0 Hct1 Hctp Hca0 Hca1 Hct2 Hmtdc Hsave Hframeoffset".
  Qed.

End Handle_Error.
