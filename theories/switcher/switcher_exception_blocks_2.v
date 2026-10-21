From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states.

(** * Exception path, blocks 24-25: [.Lhandle_error]

    Block 24 restores mtdc, then tests whether the trap comes from the
    switcher: the PC spilled in the register save area has the base of the
    switcher's PC. A fault of the switcher goes to
    [.Lhandle_error_in_switcher] (block 25), which forces the unwind. Any
    other trap reloads the interrupted stack pointer, tests that the trusted
    stack has a frame (otherwise the thread exits; [frameoffset] always
    points after the entry frame, so the test never succeeds) and forces
    the unwind (block 18). *)

Section Switcher_Exception_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  #[local] Lemma switcher_exception_block_24_spec_aux
    (pc_a : Addr) (d : nat) (save_area : list LWord) (wmtdc wct0 wct1 wctp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 24))%a ->
    (pc_a + 15)%a = Some (pc_a ^+ 15)%a ->
    (pc_a + (-42))%a = Some (pc_a ^+ (-42))%a ->
    length save_area = 21%nat ->

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
          ⌜off = 15%Z ∨ off = (-42)%Z⌝ ∗
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
    iIntros (Hsub Hin_switcher Hunwind Hlen)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave & Hframeoffset & #Hcode & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    destruct save_area as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
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
      as (wmepcc) "(_ & HPC & Hct1 & Hcsp & Hs0 & _)".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
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
      iSplit; first (iPureIntro; by left).
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
      iSplit; first (iPureIntro; by right).
      iFrame "∗ Hcode".
      iRegionMerge. iFrame.
  Qed.

  #[local] Lemma switcher_exception_block_25_spec_aux (pc_a : Addr) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 25))%a ->
    (pc_a + (-57))%a = Some (pc_a ^+ (-57))%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    codefrag_pers pc_a (switcher_instrs_n 25) ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ (-57))%a -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hunwind) "(HPC & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* Jmp .Lcommon_force_unwind *)
    iInstr "Hcode".
    iApply ("Hpost" with "HPC").
  Qed.

  (** Blocks 24-25, [.Lhandle_error]: restore mtdc and force the unwind,
      whether the trap comes from the switcher or not. The words of the
      register save area are only read. *)
  Lemma switcher_exception_blocks_24_25_spec
    (d : nat) (save_area : list LWord) (wmtdc wct0 wct1 wctp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    length save_area = 21%nat ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error" ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ctp ↦ᵣ wctp ∗
    mtdc ↦ₛᵣ wmtdc ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    switcher_code ∗
    ▷ ( ∀ (wct0' wct1' wctp' : LWord),
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ wct0' ∗
          ct1 ↦ᵣ wct1' ∗
          ctp ↦ᵣ wctp' ∗
          mtdc ↦ₛᵣ tstack_cap ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
          a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset.
    iIntros (Hlen)
      "(HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave & Hframeoffset & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error") "Hswitcher" as "Hcode" "Hcls";
      iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_24_spec_aux with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hctp $Hmtdc $Hsave $Hframeoffset $Hcode]");
      [done | offsets_compute; solve_addr | offsets_compute; solve_addr | done |].
    iNext; iIntros (wct0' wct1' wctp' off)
      "(%Hoff & HPC & Hcsp & Hct0 & Hct1 & Hctp & Hmtdc & Hsave & Hframeoffset & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    destruct Hoff as [-> | ->].
    - (* A fault of the switcher: block 25 *)
      switcher_focus_block (switcher_block ".Lhandle_error_in_switcher") "Hswitcher"
        as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
      iApply (switcher_exception_block_25_spec_aux with "[- $HPC $Hcode]");
        [done | offsets_compute; solve_addr |].
      iNext; iIntros "HPC".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
      iApply ("Hpost" $! wct0' wct1' wctp'); iFrame "∗ Hswitcher".
    - switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
      iApply ("Hpost" $! wct0' wct1' wctp'); iFrame "∗ Hswitcher".
  Qed.

End Switcher_Exception_Blocks_2.
