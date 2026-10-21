From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states.

(** * Exception path, blocks 24-25: [.Lhandle_error]

    Block 24 restores mtdc, then tests whether the trap comes from the
    switcher: the PC spilled in the register save area has the base of the
    switcher's PC. A fault of the switcher goes to
    [.Lhandle_error_in_switcher] (block 25). Any other trap reloads the
    interrupted stack pointer, tests that the trusted stack has a frame
    (otherwise the thread exits; [frameoffset] always points after the entry
    frame, so the test never succeeds) and forces the unwind (block 18).

    Block 25 tests whether the fault is one of the first spill of the call
    path ([.Lswitcher_entry_first_spill]): the spilled PC has its address.
    If so, it overwrites the saved return values with [-ENOTENOUGHSTACK] and
    0, and goes to the context install (block 28), which resumes the
    interrupted context at [.Lswitch_just_return]; otherwise, it forces the
    unwind. *)

Section Switcher_Exception_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  #[local] Lemma switcher_exception_block_24_spec_aux
    (pc_a : Addr) (d : nat) (save_area : list LWord) (wmepcc wmtdc wct0 wct1 wctp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 24))%a ->
    (pc_a + 15)%a = Some (pc_a ^+ 15)%a ->
    (pc_a + (-42))%a = Some (pc_a ^+ (-42))%a ->
    length save_area = 21%nat ->
    save_area !! 0%nat = Some wmepcc ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ctp ↦ᵣ wctp ∗
    mtdc ↦ₛᵣ wmtdc ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    codefrag_pers pc_a (switcher_instrs_n 24) ∗
    ▷ ( ∀ (wct0' wct1' wctp' : LWord) (off : Z),
          ⌜(off = 15%Z ∧ get_b wmepcc.(lw) = b_switcher ∧ wct1' = wmepcc) ∨
           (off = (-42)%Z ∧ get_b wmepcc.(lw) ≠ b_switcher)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ off)%a ∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          codefrag_pers pc_a (switcher_instrs_n 24) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset.
    iIntros (Hsub Hin_switcher Hunwind Hlen Hmepcc)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave & Hframeoffset & #Hcode & Hpost)".
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
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.

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
    (* Sub ct0 ct0 ctp *)
    iInstr "Hcode".
    destruct (decide ((b_switcher - get_b (lw wmepcc))%Z = 0)) as [Hin | Hnot_in].
    - (* A fault of the switcher *)
      rewrite Hin.
      (* Jnz 2 ct0 *)
      iInstr "Hcode".
      assert ((pc_a ^+ 7 + 8)%a = Some (pc_a ^+ 15)%a) as Hjmp_in by solve_addr.
      (* Jmp .Lhandle_error_in_switcher *)
      iInstr "Hcode".
      iApply ("Hpost" $! _ _ _ 15%Z).
      iSplit; first (iPureIntro; left; split_and!; [done | lia | done]).
      iFrame "∗ Hcode".
      iRegionMerge. iFrame.
    - (* Jnz 2 ct0 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      assert ((b_trusted_stack + 2)%a = Some (b_trusted_stack ^+ 2)%a) as Hts_2
        by (tstack_unfold; solve_addr).
      (* CLoad ct0 csp 2 *)
      iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds _ _ _ _ _ _ _ ct0 csp 2)
        with "[$HPC $Hct0 $Hcsp $Hs2 $Hwit]"
        as (wcsp) "(_ & HPC & Hct0 & Hcsp & Hs2 & _)".
      { tstk_not_shadow Hts_shadow. }
      { rewrite /withinBounds; tstack_unfold; solve_addr. }
      assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a = Some a_frameoffset) as Hfo
        by (subst a_frameoffset; tstack_unfold; solve_addr).
      (* CLoad ctp csp 21 *)
      iInstr "Hcode".
      { subst a_frameoffset; tstk_not_shadow Hts_shadow. }
      { done. }
      { split; auto. subst a_frameoffset; rewrite /withinBounds; tstack_unfold; solve_addr. }
      rewrite lload_word_RWL.
      (* Mov ct1 23 *)
      iInstr "Hcode".
      (* Sub ct1 ctp ct1 *)
      iInstr "Hcode".
      destruct (decide (ct1 = cnull)) as [Hct1_null|_]; first done.
      (* The trusted stack always has a frame: the thread does not exit *)
      (* Jnz 2 ct1 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. tstack_unfold. lia. }
      assert ((pc_a ^+ 14 + (-56))%a = Some (pc_a ^+ (-42))%a) as Hjmp_unwind by solve_addr.
      (* Jmp .Lcommon_force_unwind *)
      iInstr "Hcode".
      iApply ("Hpost" $! _ _ _ (-42)%Z).
      iSplit; first (iPureIntro; right; split; [done | lia]).
      iFrame "∗ Hcode".
      iRegionMerge. iFrame.
  Qed.

  (** Block 25: a fault at the first spill of the call path sets the return
      values, overwrites them in the register save area, and goes to the
      context install with the PC of [.Lswitch_just_return] in [ct2]; any
      other fault of the switcher forces the unwind. *)
  #[local] Lemma switcher_exception_block_25_spec_aux
    (pc_a : Addr) (wmepcc wctp wca0 wca1 wct2 w10 w11 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 25))%a ->
    (pc_a + (-181))%a = Some (pc_a ^+ (-181))%a ->
    (pc_a + (-57))%a = Some (pc_a ^+ (-57))%a ->
    (pc_a + (-69))%a = Some (pc_a ^+ (-69))%a ->
    (pc_a + 11)%a = Some (pc_a ^+ 11)%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ tstack_cap ∗
    ct1 ↦ᵣ wmepcc ∗
    ctp ↦ᵣ wctp ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct2 ↦ᵣ wct2 ∗
    (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ w10 ∗
    (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ w11 ∗
    codefrag_pers pc_a (switcher_instrs_n 25) ∗
    ▷ ( ( ∀ (wct1' wctp' : LWord),
          ⌜get_a wmepcc.(lw) ≠ ((pc_a ^+ (-181))%a : Z)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ (-57))%a ∗
          csp ↦ᵣ tstack_cap ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          ca0 ↦ᵣ wca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ct2 ↦ᵣ wct2 ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ w10 ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ w11 ∗
          codefrag_pers pc_a (switcher_instrs_n 25) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ∀ (wct1' wctp' : LWord),
          ⌜get_a wmepcc.(lw) = ((pc_a ^+ (-181))%a : Z)⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 11)%a ∗
          csp ↦ᵣ tstack_cap ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          ca0 ↦ᵣ WInt ENOTENOUGHSTACK ∗
          ca1 ↦ᵣ WInt 0 ∗
          ct2 ↦ᵣ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ (-69))%a ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca0)%a ↦ₐ WInt ENOTENOUGHSTACK ∗
          (b_trusted_stack ^+ TrustedStack_offset_ca1)%a ↦ₐ WInt 0 ∗
          codefrag_pers pc_a (switcher_instrs_n 25) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hfirst_spill Hunwind Hjust_return Hinstall)
      "(HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11 & #Hcode & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n /tstack_cap.
    (* Auipcc ctp .Lswitcher_entry_first_spill *)
    iInstr "Hcode".
    (* Sub ct1 ct1 ctp *)
    iInstrApply "Hcode" (wp_sub_dst_r_any _ ct1 _ _ _ _ _ _ _ _ ctp)
      with "[$HPC $Hct1 $Hctp]" as "(HPC & Hctp & Hct1)".
    destruct (decide (get_a wmepcc.(lw) = ((pc_a ^+ (-181))%a : Z))) as [Hfirst | Hnot_first].
    - (* A fault of the first spill: resume the caller *)
      iDestruct "Hpost" as "[_ Hpost]".
      iEval (cbn [lw get_a]; rewrite Hfirst Z.sub_diag) in "Hct1".
      (* Jnz .Lcommon_force_unwind ct1 *)
      iInstr "Hcode".
      (* Mov ca0 ENOTENOUGHSTACK *)
      iInstr "Hcode".
      (* Mov ca1 0 *)
      iInstr "Hcode".
      destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
      assert ((pc_a ^+ 5 + (-74))%a = Some (pc_a ^+ (-69))%a) as Hjust_return' by solve_addr.
      (* Auipcc ct2 .Lswitch_just_return *)
      iInstr "Hcode".
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
      assert ((pc_a ^+ 8 + 3)%a = Some (pc_a ^+ 11)%a) as Hinstall' by solve_addr.
      (* Jmp .Lcommon_context_install *)
      iInstr "Hcode".
      iApply "Hpost". iFrame "∗ Hcode". done.
    - (* Any other fault of the switcher: force the unwind *)
      iDestruct "Hpost" as "[Hpost _]".
      assert ((pc_a ^+ 2 + (-59))%a = Some (pc_a ^+ (-57))%a) as Hunwind' by solve_addr.
      (* Jnz .Lcommon_force_unwind ct1 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      iApply "Hpost". iFrame "∗ Hcode". done.
  Qed.

  (** Blocks 24-25, [.Lhandle_error]: restore mtdc, then force the unwind, or
      resume the caller of a call path whose first spill faulted. The first
      word of the register save area holds the PC of the fault, [wmepcc]. *)
  Lemma switcher_exception_blocks_24_25_spec
    (d : nat) (save_area : list LWord) (wmepcc wmtdc wct0 wct1 wctp wca0 wca1 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_first_spill := (a_switcher_call ^+ switcher_label_offset ".Lswitcher_entry_first_spill")%a in
    length save_area = 21%nat ->
    save_area !! 0%nat = Some wmepcc ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error" ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ctp ↦ᵣ wctp ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ wmtdc ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    switcher_code ∗
    ▷ ( ( ⌜get_b wmepcc.(lw) ≠ b_switcher ∨ get_a wmepcc.(lw) ≠ a_first_spill⌝ -∗
          ∀ (wct0' wct1' wctp' : LWord),
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          ca0 ↦ᵣ wca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ct2 ↦ᵣ wct2 ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜get_b wmepcc.(lw) = b_switcher ∧ get_a wmepcc.(lw) = a_first_spill⌝ -∗
          ∀ (wct0' wct1' wctp' : LWord),
          PC ↦ₚ switcher_label_pc ".Lcommon_context_install" ∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          ca0 ↦ᵣ WInt ENOTENOUGHSTACK ∗
          ca1 ↦ᵣ WInt 0 ∗
          ct2 ↦ᵣ switcher_label_pc ".Lswitch_just_return" ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ <[ Z.to_nat TrustedStack_offset_ca0 := (WInt ENOTENOUGHSTACK : LWord) ]>
                 (<[ Z.to_nat TrustedStack_offset_ca1 := (WInt 0 : LWord) ]> save_area) ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_first_spill.
    iIntros (Hlen Hmepcc)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hmtdc & Hsave & Hframeoffset
       & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    pose proof trusted_stack_frames_fit as [n Hfit].
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error") "Hswitcher" as "Hcode" "Hcls";
      iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_24_spec_aux with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hmtdc $Hsave $Hframeoffset $Hcode]");
      [done | offsets_compute; solve_addr | offsets_compute; solve_addr | done | done |].
    iNext; iIntros (wct0' wct1' wctp' off)
      "(%Hoff & HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave & Hframeoffset & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    destruct Hoff as [(-> & Hin & ->) | (-> & Hnot_in)].
    - (* A fault of the switcher: block 25 *)
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
      switcher_focus_block (switcher_block ".Lhandle_error_in_switcher") "Hswitcher"
        as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
      iApply (switcher_exception_block_25_spec_aux with
               "[- $HPC $Hcsp $Hct1 $Hctp $Hca0 $Hca1 $Hct2 $Hs10 $Hs11 $Hcode]");
        [done | offsets_compute; solve_addr.. |].
      iNext; iSplit.
      + iIntros (wct1'' wctp'')
          "(%Hnot_first & HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11 & _)".
        unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
        switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
        iDestruct "Hpost" as "[Hpost _]".
        iApply ("Hpost" with "[] [-]").
        { iPureIntro. right. subst a_first_spill. offsets_compute.
          intros Heq. apply Hnot_first. rewrite Heq. solve_addr. }
        iFrame "∗ Hswitcher". iRegionMerge. iFrame.
      + iIntros (wct1'' wctp'')
          "(%Hfirst & HPC & Hcsp & Hct1 & Hctp & Hca0 & Hca1 & Hct2 & Hs10 & Hs11 & _)".
        unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
        switcher_change_pc (switcher_label_offset ".Lcommon_context_install").
        iDestruct "Hpost" as "[_ Hpost]".
        iApply ("Hpost" with "[] [-]").
        { iPureIntro. split; first done. subst a_first_spill. offsets_compute.
          rewrite Hfirst. solve_addr. }
        rewrite (_ : (a_switcher_call ^+ switcher_block_offset 25 ^+ (-69))%a =
                     (a_switcher_call ^+ switcher_label_offset ".Lswitch_just_return")%a);
          last (offsets_compute; solve_addr).
        iFrame "∗ Hswitcher". cbn. iRegionMerge. iFrame.
    - switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[] [-]"); first (iPureIntro; by left).
      iFrame "∗ Hswitcher".
  Qed.

End Switcher_Exception_Blocks_2.
