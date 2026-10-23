From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states trusted_spill_registers_spec.

(** * Exception path, blocks 21-23: exception entry

    Block 21 swaps the trusted stack in from mtdc (a null mtdc would mean
    that the exception entry is re-entered, which the base of the trusted
    stack, not at address 0, rules out). Block 22 spills the registers of
    the interrupted context in the register save area, but the stack
    pointer. Block 23 spills the stack pointer, from mtdc, which is cleared,
    the PC (MEPCC), mstatus and the cause (mcause), and gives the volatile
    registers back to the state interpretation before the store of the
    cause. A cause of the range of trap entry is handled by the
    compartments: the block jumps to [.Lhandle_error] (block 24). *)

Section Switcher_Exception_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 21: swap the trusted stack in from mtdc; mtdc is not null. *)
  #[local] Lemma switcher_exception_block_21_spec_aux (pc_a : Addr) (wcsp : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 21))%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ wcsp ∗
    mtdc ↦ₛᵣ tstack_cap ∗
    codefrag_pers pc_a (switcher_instrs_n 21) ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 3)%a ∗
        csp ↦ᵣ tstack_cap ∗
        mtdc ↦ₛᵣ wcsp ∗
        codefrag_pers pc_a (switcher_instrs_n 21) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hcsp & Hmtdc & #Hcode & Hpost)".
    pose proof trusted_stack_base_nonzero as Hts_nonzero.
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n /tstack_cap.
    (* SpecialRW csp mtdc csp *)
    iInstr "Hcode".
    rewrite llegalise_mtdc.
    (* Jne 2 csp 0 *)
    iInstr "Hcode".
    { apply negb_true_iff, Z.eqb_neq. exact Hts_nonzero. }
    iApply "Hpost". iFrame "∗ #".
  Qed.

  (** Block 22 is the spill of the registers but the stack pointer. *)
  Lemma switcher_instrs_22_spill :
    switcher_instrs_n 22 = trusted_spill_registers_instrs exception_spill_regs.
  Proof. reflexivity. Qed.

  (** Block 23: the stack pointer, MEPCC, mstatus and mcause, then the
      dispatch on the cause. *)
  #[local] Lemma switcher_exception_block_23_spec_aux
    (pc_a : Addr) (w wcsp wct0 wct1 wca0 ws0 ws2 ws17 ws18 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 23))%a ->
    (pc_a + 17)%a = Some (pc_a ^+ 17)%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ tstack_cap ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca0 ↦ᵣ wca0 ∗
    mtdc ↦ₛᵣ wcsp ∗
    b_trusted_stack ↦ₐ ws0 ∗
    (b_trusted_stack ^+ 2)%a ↦ₐ ws2 ∗
    (b_trusted_stack ^+ 17)%a ↦ₐ ws17 ∗
    (b_trusted_stack ^+ 18)%a ↦ₐ ws18 ∗
    trap_entry_out w ∗
    codefrag_pers pc_a (switcher_instrs_n 23) ∗
    ▷ ( ∀ (wst : LWord) (cause zca0 : Z),
          ⌜mcause_ok cause⌝ ∗
          PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 17)%a ∗
          csp ↦ᵣ tstack_cap ∗
          ct0 ↦ᵣ lmepcc_of_pc w ∗
          ct1 ↦ᵣ WInt cause ∗
          ca0 ↦ᵣ WInt zca0 ∗
          mtdc ↦ₛᵣ WInt 0 ∗
          b_trusted_stack ↦ₐ lmepcc_of_pc w ∗
          (b_trusted_stack ^+ 2)%a ↦ₐ wcsp ∗
          (b_trusted_stack ^+ 17)%a ↦ₐ wst ∗
          (b_trusted_stack ^+ 18)%a ↦ₐ WInt cause ∗
          trap_entry_res ∗
          codefrag_pers pc_a (switcher_instrs_n 23) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hhandle)
      "(HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Hout & #Hcode
       & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     (b_trusted_stack + k)%a = Some (b_trusted_stack ^+ k)%a) as Hts_k
      by (intros; tstack_unfold; solve_addr).
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     is_shadow_address (b_trusted_stack ^+ k)%a = false) as Hts_k_shadow.
    { intros k Hk. tstk_not_shadow Hts_shadow. }
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     withinBounds b_trusted_stack e_trusted_stack (b_trusted_stack ^+ k)%a = true)
      as Hts_k_bounds.
    { intros k Hk. rewrite /withinBounds. tstack_unfold; solve_addr. }
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n /tstack_cap.

    (* The interrupted stack pointer, from mtdc *)
    (* Mov ct1 0 *)
    iInstr "Hcode".
    (* SpecialRW ct1 mtdc ct1 *)
    iInstr "Hcode".
    rewrite !llegalise_mtdc.
    pose proof (Hts_k 2 ltac:(lia)) as Hts_2.
    (* Store csp ct1 2 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].

    (* MEPCC, mstatus and mcause *)
    iDestruct (trap_entry_out_vcsr_frag with "Hout") as "[Hmepcc (%cause & %Hcause & Hmcause)]".
    (* SpecialRW ct0 mepcc cnull *)
    iInstrApply "Hcode" wp_cspecialr_vcsr with "[$HPC $Hct0 $Hmepcc]" as "(HPC & Hct0 & Hmepcc)".
    assert ((b_trusted_stack + 0)%a = Some b_trusted_stack) as Hts_0 by solve_addr.
    (* Store csp ct0 0 *)
    iInstr "Hcode"; [tstk_not_shadow Hts_shadow | rewrite /withinBounds; tstack_unfold; solve_addr |].
    (* SpecialRW ct1 mstatus cnull *)
    iInstrApply "Hcode" wp_csrr_mstatus with "[$HPC $Hct1]" as (wst) "(HPC & Hct1)".
    pose proof (Hts_k 17 ltac:(lia)) as Hts_17.
    (* Store csp ct1 17 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    (* SpecialRW ct1 mcause cnull *)
    iInstrApply "Hcode" wp_cspecialr_vcsr with "[$HPC $Hct1 $Hmcause]" as "(HPC & Hct1 & Hmcause)".
    (* The volatile registers go back to the state interpretation *)
    iApply (wp_vcsr_return with "[Hmepcc Hmcause]"); first done.
    { iApply (vcsr_res_intro with "Hmepcc Hmcause"). }
    iIntros "Htok".
    pose proof (Hts_k 18 ltac:(lia)) as Hts_18.
    (* Store csp ct1 18 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].

    (* Dispatch on the cause *)
    (* Mov ca0 28 *)
    iInstr "Hcode".
    (* Sub ca0 ca0 ct1 *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    repeat rewrite lstore_word_isWL; try reflexivity.
    iAssert (∀ zca0 : Z,
                PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 17)%a -∗
                ca0 ↦ᵣ WInt zca0 -∗
                ct1 ↦ᵣ WInt cause -∗
                WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I
      with "[- Hca0 HPC Hct1]" as "Hpost".
    { iIntros (zca0) "HPC Hca0 Hct1".
      iApply ("Hpost" $! wst cause zca0). iFrame "∗ Hcode %". }
    assert ((pc_a ^+ 12 + 5)%a = Some (pc_a ^+ 17)%a) as Hjmp_handle by solve_addr.
    assert ((pc_a ^+ 15 + 2)%a = Some (pc_a ^+ 17)%a) as Hjnez_handle by solve_addr.
    destruct (decide (cause = 28%Z)) as [-> | Hcause_ne].
    - (* Jne 2 ca0 0 *)
      iInstr "Hcode".
      (* Jmp .Lhandle_error *)
      iInstr "Hcode".
      iApply ("Hpost" with "HPC Hca0 Hct1").
    - (* Jne 2 ca0 0 *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      (* Mov ca0 8 *)
      iInstr "Hcode".
      (* Lt ca0 ct1 ca0 *)
      iInstr "Hcode".
      destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
      assert ((cause <? 8)%Z = true) as -> by (apply Z.ltb_lt; destruct Hcause; lia).
      (* Jne .Lhandle_error ca0 0 *)
      iInstr "Hcode".
      iApply ("Hpost" with "HPC Hca0 Hct1").
  Qed.

  Lemma switcher_exception_blocks_21_23_spec
    (w : LWord) (save_area : list LWord)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    length save_area = 21%nat ->

    PC ↦ₚ switcher_label_pc "exception_entry_asm" ∗
    cra ↦ᵣ wcra ∗
    csp ↦ᵣ wcsp ∗
    cgp ↦ᵣ wcgp ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca3 ↦ᵣ wca3 ∗
    ca4 ↦ᵣ wca4 ∗
    ca5 ↦ᵣ wca5 ∗
    mtdc ↦ₛᵣ tstack_cap ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    trap_entry_out w ∗
    switcher_code ∗
    ▷ ( ∀ (wst : LWord) (cause zca0 : Z),
          ⌜mcause_ok cause⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lhandle_error" ∗
          cra ↦ᵣ wcra ∗
          csp ↦ᵣ tstack_cap ∗
          cgp ↦ᵣ wcgp ∗
          ctp ↦ᵣ wctp ∗
          ct0 ↦ᵣ lmepcc_of_pc w ∗
          ct1 ↦ᵣ WInt cause ∗
          ct2 ↦ᵣ wct2 ∗
          cs0 ↦ᵣ wcs0 ∗
          cs1 ↦ᵣ wcs1 ∗
          ca0 ↦ᵣ WInt zca0 ∗
          ca1 ↦ᵣ wca1 ∗
          ca2 ↦ᵣ wca2 ∗
          ca3 ↦ᵣ wca3 ∗
          ca4 ↦ᵣ wca4 ∗
          ca5 ↦ᵣ wca5 ∗
          mtdc ↦ₛᵣ WInt 0 ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ exception_spill save_area (lmepcc_of_pc w)
                 [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1;
                  wca0; wca1; wca2; wca3; wca4; wca5]
                 wst (WInt cause) ]] ∗
          trap_entry_res ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hlen)
      "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hmtdc & Hsave & Hout & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
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
    switcher_unfold_code "Hswitcher".

    (* Block 21: swap the trusted stack in *)
    switcher_focus_block (switcher_block "exception_entry_asm") "Hswitcher" as "Hcode" "Hcls";
      iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_21_spec_aux with "[- $HPC $Hcsp $Hmtdc $Hcode]");
      first done.
    iNext; iIntros "(HPC & Hcsp & Hmtdc & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 22: spill the registers but the stack pointer *)
    switcher_focus_block (switcher_block ".Lexception_spill_registers") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iAssert (codefrag_pers (a_switcher_call ^+ switcher_block_offset 22)%a
               (trusted_spill_registers_instrs exception_spill_regs)) as "#Hspill";
      first iExact "Hcode".
    iApply (trusted_spill_registers_spec _ _ _ _ _ _ _ _ _ exception_spill_regs
              [wcra; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]
              [s1; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15]
             with "[- $HPC $Hcsp $Hspill]").
    { done. }
    { done. }
    { rewrite -switcher_instrs_22_spill. offsets_compute. solve_addr+Hsub Hsize. }
    { apply trusted_save_cells_ok_exception. }
    { rewrite /exception_spill_regs. set_solver. }
    { rewrite /exception_spill_regs. set_solver. }
    iSplitL "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    { cbn. iFrame. }
    iSplitL "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    { cbn. iFrame. }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    cbn.
    iDestruct "Hregs" as
      "(Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & _)".
    iDestruct "Hcells" as
      "(Hs1 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 23: the stack pointer, MEPCC, mstatus, mcause and the dispatch *)
    switcher_focus_block (switcher_block ".Lexception_exiting_threads_rejoin") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_23_spec_aux with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hca0 $Hmtdc $Hs0 $Hs2 $Hs17 $Hs18 $Hout $Hcode]");
      [done | offsets_compute; solve_addr+Hsize |].
    iNext; iIntros (wst cause zca0)
      "(%Hcause & HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Htok & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lhandle_error").
    iApply ("Hpost" $! wst cause zca0); iFrame "∗ Hswitcher %".
    rewrite /exception_spill /=.
    iRegionMerge. iFrame.
  Qed.

End Switcher_Exception_Blocks_1.
