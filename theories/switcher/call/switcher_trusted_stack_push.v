From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_hazard_slots_spec.

(** * Call routine: push on the trusted stack

    [.Lswitch_trusted_stack_load] reads the trusted stack and clears the
    hazard slots of the thread ([clear_hazard_slots_asm]).
    [.Lswitch_trusted_stack_push] checks that the trusted stack has room
    for a frame at [frameoffset]. If not, it jumps to
    [.Lswitch_trusted_stack_exhausted]. Otherwise, it pushes a
    frame holding the caller's stack pointer, with a cleared error handler
    count and export table, increments [frameoffset], and falls through to
    [.Lswitch_stack_chop]. *)

Section Switcher_Trusted_Stack_Push.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_trusted_stack_load]: read the trusted stack into [ct2]
      and clear the hazard slots of the thread. *)
  Lemma switcher_trusted_stack_load_spec (wctp wct2 : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_load" ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    switcher_hazard ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_push" ∗
        ctp ↦ᵣ hazard_slots_cap ∗
        ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        tstack_hazard_cell ↦ₐ hazard_slots_cap ∗
        [[ b_hazard_slots, e_hazard_slots ]] ↦ₐ
          [[ region_addrs_zeroes b_hazard_slots e_hazard_slots ]] -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hctp & Hct2 & Hmtdc & Hhazard & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    switcher_open_label ".Lswitch_trusted_stack_load" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_hide "Hpost" as hpost.
    (* ReadSR ct2 mtdc *)
    iInstr "Hcode".
    (* clear_hazard_slots_asm ct2 ctp *)
    iDestruct "Hhazard" as "[Hhazard_cell [%ws Hslots]]".
    iDestruct (codefrag_pers_clear_hazard_slots _ _ 1 ct2 ctp with "Hcode") as "Hcode_hz";
      [done | cbn; lia |].
    iEval (rewrite /tstack_hazard_cell /hazard_slots_cap) in "Hhazard_cell".
    iEval (rewrite (_ : (a_block ^+ 1%nat)%a = (a_block ^+ 1)%a); last done) in "Hcode_hz".
    pose proof hazard_slots_size as Hhz_size.
    pose proof hazard_slots_disjoint_from_shadow as Hhz_shadow.
    pose proof hazard_slots_not_heap as Hhz_heap.
    iApply (clear_hazard_slots_spec with "[- $HPC $Hct2 $Hctp $Hhazard_cell $Hslots $Hcode_hz]");
      try done.
    { rewrite clear_hazard_slots_instrs_length; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /withinBounds /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers. tstk_not_shadow Hts_shadow. }
    iNext; iIntros "(HPC & Hct2 & Hctp & Hhazard_cell & Hslots)".
    rewrite clear_hazard_slots_instrs_length.
    switcher_change_pc_label ".Lswitch_trusted_stack_push".
    subst hpost.
    iApply "Hpost".
    rewrite /tstack_hazard_cell /hazard_slots_cap.
    iFrame "HPC Hctp Hct2 Hmtdc Hhazard_cell Hslots".
  Qed.

  (** From [.Lswitch_trusted_stack_push]: when [frameoffset] is below the
      length of the trusted stack, push a frame at [frameoffset], holding
      the stack pointer [wstk] of the caller, and increment [frameoffset].
      The call-stack has [d] frames, the topmost one at [a_tstk]. *)
  Lemma switcher_trusted_stack_push_spec
    (d : nat) (a_tstk : Addr) (tstk_next : list LWord) (wcs0 wcs1 wctp wstk : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->

    PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_push" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    csp ↦ᵣ wstk ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    ▷ ( ( ∃ tstk_next',
          ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
          ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_stack_chop" ∗
          cs0 ↦ᵣ WInt (e_trusted_stack - b_trusted_stack) ∗
          cs1 ↦ᵣ WInt (tstack_frameoffset (S d)) ∗
          ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_next ∗
          ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
          csp ↦ᵣ wstk ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
          a_csp ↦ₐ wstk ∗
          a_export_table ↦ₐ WInt 0 ∗
          a_error_count ↦ₐ WInt 0 ∗
          [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]] ∗
          £ 2 )
        ∨
        ( PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
          cs0 ↦ᵣ WInt (e_trusted_stack - b_trusted_stack) ∗
          cs1 ↦ᵣ wcs1 ∗
          ctp ↦ᵣ WInt (tstack_frameoffset d) ∗
          ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
          csp ↦ᵣ wstk ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Ha_tstk Ha_tstk_e)
      "(HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hframeoffset & Htstk & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).
    switcher_open_label ".Lswitch_trusted_stack_push" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_hide "Hpost" as hpost.
    (* CLoad ctp ct2 TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* GetLen cs0 ct2 *)
    iInstr "Hcode".
    destruct (decide (tstack_frameoffset d < e_trusted_stack - b_trusted_stack)%Z) as [Hroom|Hroom];
      cycle 1.
    { (* Jle .Lswitch_trusted_stack_exhausted cs0 ctp *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hcs0 $Hctp]"
        as "(HPC & Hcs0 & Hctp)".
      { cbn [jcond_test get_a lw]; apply Z.leb_le; lia. }
      { switcher_jump_label ".Lswitch_trusted_stack_exhausted". }
      subst hpost.
      iApply "Hpost"; iRight.
      iFrame "HPC Hcs0 Hcs1 Hctp Hct2 Hcsp Hframeoffset Htstk". }
    (* Jle .Lswitch_trusted_stack_exhausted cs0 ctp *)
    iInstrApply "Hcode" with "Hlc" wp_jcond_success_next_r_r with "[$HPC $Hcs0 $Hctp]"
      as "(HPC & Hcs0 & Hctp)".
    { cbn [jcond_test get_a lw]; apply Z.leb_gt; lia. }
    (* Lea ctp ct2 ctp *)
    iInstr "Hcode" with "Hlc'".
    { instantiate (1 := (a_tstk ^+ TrustedStackFrame_size)%a). tstack_unfold; solve_addr. }
    (* Split the new frame off the unused part of the trusted stack *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next as [|w0 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    destruct tstk_next as [|w1 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    destruct tstk_next as [|w2 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_offset_calleeExportTable)%a
                 with "Htstk") as "[Hframe_csp Htstk]"; [tstack_unfold; solve_addr..|].
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_offset_errorHandlerCount)%a
                 with "Htstk") as "[Hframe_export_table Htstk]"; [tstack_unfold; solve_addr..|].
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_size)%a
                 with "Htstk") as "[Hframe_error_count Htstk]"; [tstack_unfold; solve_addr..|].
    assert (((a_tstk ^+ TrustedStackFrame_size) + TrustedStackFrame_offset_calleeExportTable)%a
            = Some ((a_tstk ^+ TrustedStackFrame_size)
                    ^+ TrustedStackFrame_offset_calleeExportTable)%a)
      as Ha_export_table by (tstack_unfold; solve_addr).
    assert (((a_tstk ^+ TrustedStackFrame_size) + TrustedStackFrame_offset_errorHandlerCount)%a
            = Some ((a_tstk ^+ TrustedStackFrame_size)
                    ^+ TrustedStackFrame_offset_errorHandlerCount)%a)
      as Ha_error_count by (tstack_unfold; solve_addr).
    (* Store ctp csp TrustedStackFrame_offset_csp *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    (* Store ctp 0 TrustedStackFrame_offset_errorHandlerCount *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    (* Store ctp 0 TrustedStackFrame_offset_calleeExportTable *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    (* CLoad cs1 ct2 TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* Add cs1 cs1 TrustedStackFrame_size *)
    iInstr "Hcode".
    (* Store ct2 cs1 TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    repeat rewrite lstore_word_isWL; try reflexivity.
    replace (tstack_frameoffset d + _)%Z with (tstack_frameoffset (S d))
      by (tstack_unfold; lia).
    switcher_change_pc_label ".Lswitch_stack_chop".
    iCombine "Hlc Hlc'" as "Hlc".
    subst hpost.
    iApply "Hpost"; iLeft; iExists tstk_next.
    rewrite /TrustedStackFrame_offset_csp finz_add_0_default.
    iFrame "HPC Hcs0 Hcs1 Hctp Hct2 Hcsp Hframeoffset Hframe_csp Hframe_export_table
      Hframe_error_count Htstk Hlc".
    iPureIntro; tstack_unfold; split; solve_addr.
  Qed.

End Switcher_Trusted_Stack_Push.
