From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states trusted_spill_registers_spec.

(** * Exception path: the exception entry

    [exception_entry_asm] swaps the trusted stack in from mtdc (a null mtdc
    would mean that the exception entry is re-entered, which the base of
    the trusted stack, not at address 0, rules out), and spills the
    registers of the interrupted context in the register save area, but the
    stack pointer.
    [.Lexception_exiting_threads_rejoin] spills the stack pointer, from
    mtdc, which is cleared, the PC (MEPCC), mstatus and the cause (mcause),
    and gives MEPCC and mcause back to the state interpretation before the
    store of the cause; mtval stays lent until the handler set-up reads it.
    A cause of the range of trap entry is handled by the compartments: the
    block jumps to [.Lhandle_error]. *)

Section Exception_Entry.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** [exception_entry_asm]: swap the trusted stack in from mtdc (mtdc is
      not null), and spill the registers of the interrupted context but the
      stack pointer. *)
  #[local] Lemma exception_entry_block_spec (wcsp : LWord) (wregs wold : list LWord) :
    PC ↦ₚ[th] switcher_label_pc "exception_entry_asm" ∗
    csp ↦ᵣ[th] wcsp ∗
    mtdc ↦ₜ[th] TStack tstack_cap ∗
    ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
    ([∗ list] r;w ∈ exception_spill_regs;wold, (b_trusted_stack ^+ TrustedStack_offset_reg r)%a ↦ₐ w) ∗
    switcher_code ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[th] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
        csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
        mtdc ↦ₜ[th] ExceptionScratch wcsp ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs,
           (b_trusted_stack ^+ TrustedStack_offset_reg r)%a ↦ₐ w) -∗
        WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros "(HPC & Hcsp & Hmtdc & Hregs & Hcells & #Hswitcher & Hpost)".
    pose proof trusted_stack_base_nonzero as Hts_nonzero.
    switcher_open_label "exception_entry_asm" "Hswitcher" as "Hcode" a_entry Ha_entry.
    rewrite /tstack_cap.
    (* SpecialRW csp mtdc csp *)
    iInstr "Hcode".
    { apply mtdc_match_ExceptionScratch. }
    destruct (mtdc_match_TStack_cap _ _ _ _ _ _ Hpost_pure) as [g_tstk ->].
    (* Jeq .Lexception_reentered csp 0 *)
    iInstrApply "Hcode" wp_jcond_success_next_r_z with "[$HPC $Hcsp]" as "(HPC & Hcsp)".
    { cbn; apply Z.eqb_neq; exact Hts_nonzero. }
    iAssert (codefrag_pers (a_entry ^+ 2%nat)%a
               (trusted_spill_registers_instrs exception_spill_regs)) as "#Hspill".
    { iEval (rewrite -(take_drop 2 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iExact "Hcode'". }
    iApply (trusted_spill_registers_spec with "[- $HPC $Hcsp $Hregs $Hcells $Hspill]");
      [done | done | | apply trusted_save_cells_ok_exception
      | rewrite /exception_spill_regs; set_solver | rewrite /exception_spill_regs; set_solver |].
    { rewrite trusted_spill_registers_instrs_length /exception_spill_regs; cbn [length].
      solve_addr. }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    rewrite trusted_spill_registers_instrs_length /exception_spill_regs.
    cbn [length].
    switcher_change_pc_label ".Lexception_exiting_threads_rejoin".
    iApply ("Hpost" $! g_tstk). iFrame "HPC Hcsp Hmtdc Hregs Hcells".
  Qed.

  (** [.Lexception_exiting_threads_rejoin]: the stack pointer, MEPCC,
      mstatus and mcause, then the dispatch on the cause, which satisfies
      the cause predicate [P_mcause] of fault causes. mtval, with a value
      that satisfies the value predicate [P_mtval], stays lent. *)
  #[local] Lemma exception_exiting_threads_rejoin_spec
    (g_tstk : Locality) (P_mcause P_mtval : Z → Prop)
    (w wcsp wct0 wct1 wca0 ws0 ws2 ws17 ws18 : LWord) :
    (∀ c, P_mcause c → mcause_ok c) →
    PC ↦ₚ[th] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
    csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    mtdc ↦ₜ[th] ExceptionScratch wcsp ∗
    b_trusted_stack ↦ₐ ws0 ∗
    (b_trusted_stack ^+ 2)%a ↦ₐ ws2 ∗
    (b_trusted_stack ^+ 17)%a ↦ₐ ws17 ∗
    (b_trusted_stack ^+ 18)%a ↦ₐ ws18 ∗
    trap_entry_out_cause P_mcause P_mtval w ∗
    switcher_code ∗
    ▷ ( ∀ (wst : LWord) (cause zca0 tval : Z),
          ⌜P_mcause cause⌝ -∗
          ⌜P_mtval tval⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ct0 ↦ᵣ[th] lmepcc_of_pc w ∗
          ct1 ↦ᵣ[th] WInt cause ∗
          ca0 ↦ᵣ[th] WInt zca0 ∗
          mtdc ↦ₜ[th] ExceptionScratch (WInt 0) ∗
          b_trusted_stack ↦ₐ lmepcc_of_pc w ∗
          (b_trusted_stack ^+ 2)%a ↦ₐ wcsp ∗
          (b_trusted_stack ^+ 17)%a ↦ₐ wst ∗
          (b_trusted_stack ^+ 18)%a ↦ₐ WInt cause ∗
          trap_vcsr_res ∗
          vcsr_frag MTVAL (lword_of_word (WInt tval)) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (HP_mcause)
      "(HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Hout & #Hswitcher
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
    switcher_open_label ".Lexception_exiting_threads_rejoin" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    rewrite /tstack_cap.

    (* The interrupted stack pointer, from mtdc *)
    (* Mov ct1 0 *)
    iInstr "Hcode".
    (* SpecialRW ct1 mtdc ct1 *)
    iInstr "Hcode".
    { apply mtdc_match_ExceptionScratch. }
    cbn in Hpost_pure; subst vm.
    pose proof (Hts_k 2 ltac:(lia)) as Hts_2.
    (* Store csp ct1 2 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].

    (* MEPCC, mstatus and mcause *)
    iDestruct (trap_entry_out_vcsr_frag with "Hout")
      as "(Hmepcc & (%cause & %Hcause & Hmcause) & (%tval & %Htval & Hmtval))".
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
    (* MEPCC and mcause go back to the state interpretation *)
    iApply (wp_vcsr_return with "[Hmepcc Hmcause]"); first done.
    { iApply (vcsr_res_intro with "Hmepcc Hmcause"). }
    iIntros "Htok".
    pose proof (Hts_k 18 ltac:(lia)) as Hts_18.
    (* Store csp ct1 18 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].

    (* Dispatch on the cause *)
    (* Mov ca0 MCAUSE_CHERI *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    repeat rewrite lstore_word_isWL; try reflexivity.
    iAssert (∀ zca0 : Z,
                PC ↦ₚ switcher_label_pc ".Lhandle_error" -∗
                ca0 ↦ᵣ WInt zca0 -∗
                ct1 ↦ᵣ WInt cause -∗
                WP Seq (Instr Executable) {{ HO th }})%I
      with "[- Hca0 HPC Hct1]" as "Hpost".
    { iIntros (zca0) "HPC Hca0 Hct1".
      subst hpost.
      iApply ("Hpost" $! wst cause zca0 tval with "[//] [//]").
      iFrame "HPC Hcsp Hct0 Hct1 Hca0 Hmtdc Hs0 Hs2 Hs17 Hs18 Htok Hmtval". }
    destruct (decide (cause = 28%Z)) as [-> | Hcause_ne].
    - (* Jeq .Lhandle_error ca0 ct1 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hca0 $Hct1]"
        as "(HPC & Hca0 & Hct1)".
      { reflexivity. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error")%a
          by switcher_addr_eq. }
      iApply ("Hpost" with "HPC Hca0 Hct1").
    - (* Jeq .Lhandle_error ca0 ct1 *)
      iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hca0 $Hct1]"
        as "(HPC & Hca0 & Hct1)".
      { cbn [jcond_test get_a lw]; apply Z.eqb_neq; lia. }
      (* Mov ca0 8 *)
      iInstr "Hcode".
      destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
      (* Jlt .Lhandle_error ct1 ca0 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct1 $Hca0]"
        as "(HPC & Hct1 & Hca0)".
      { cbn [jcond_test get_a lw]; apply Z.ltb_lt; destruct (HP_mcause _ Hcause); lia. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error")%a
          by switcher_addr_eq. }
      iApply ("Hpost" with "HPC Hca0 Hct1").
  Qed.

  (** From [exception_entry_asm]: spill the interrupted context in the
      register save area, give MEPCC and mcause back, and go to
      [.Lhandle_error], with mtval lent. *)
  Lemma exception_entry_asm_spec (P_mcause P_mtval : Z → Prop)
    (w : LWord) (save_area : list LWord)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    (∀ c, P_mcause c → mcause_ok c) ->
    length save_area = 21%nat ->

    PC ↦ₚ[th] switcher_label_pc "exception_entry_asm" ∗
    cra ↦ᵣ[th] wcra ∗
    csp ↦ᵣ[th] wcsp ∗
    cgp ↦ᵣ[th] wcgp ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ca3 ↦ᵣ[th] wca3 ∗
    ca4 ↦ᵣ[th] wca4 ∗
    ca5 ↦ᵣ[th] wca5 ∗
    mtdc ↦ₜ[th] TStack tstack_cap ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    trap_entry_out_cause P_mcause P_mtval w ∗
    switcher_code ∗
    ▷ ( ∀ (g_tstk : Locality) (wst : LWord) (cause zca0 tval : Z),
          ⌜P_mcause cause⌝ ∗
          ⌜P_mtval tval⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
          cra ↦ᵣ[th] wcra ∗
          csp ↦ᵣ[th] WCap true RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          cgp ↦ᵣ[th] wcgp ∗
          ctp ↦ᵣ[th] wctp ∗
          ct0 ↦ᵣ[th] lmepcc_of_pc w ∗
          ct1 ↦ᵣ[th] WInt cause ∗
          ct2 ↦ᵣ[th] wct2 ∗
          cs0 ↦ᵣ[th] wcs0 ∗
          cs1 ↦ᵣ[th] wcs1 ∗
          ca0 ↦ᵣ[th] WInt zca0 ∗
          ca1 ↦ᵣ[th] wca1 ∗
          ca2 ↦ᵣ[th] wca2 ∗
          ca3 ↦ᵣ[th] wca3 ∗
          ca4 ↦ᵣ[th] wca4 ∗
          ca5 ↦ᵣ[th] wca5 ∗
          mtdc ↦ₜ[th] ExceptionScratch (WInt 0) ∗
          [[ b_trusted_stack, tstack_save_end ]] ↦ₐ
            [[ exception_spill save_area (lmepcc_of_pc w)
                 [wcra; wcsp; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1;
                  wca0; wca1; wca2; wca3; wca4; wca5]
                 wst (WInt cause) ]] ∗
          trap_vcsr_res ∗
          vcsr_frag MTVAL (lword_of_word (WInt tval)) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (HP_mcause Hlen)
      "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hmtdc & Hsave & Hout & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
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

    (* Swap the trusted stack in, spill the registers but the stack pointer *)
    iApply (exception_entry_block_spec _
              [wcra; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]
              [s1; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15]
             with "[- $HPC $Hcsp $Hmtdc $Hswitcher]").
    iSplitL "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5".
    { cbn [big_sepL2 exception_spill_regs]. iFrame "Hcra Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5". }
    iSplitL "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    { cbn [big_sepL2 exception_spill_regs]. iFrame "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15". }
    iNext; iIntros (g_tstk) "(HPC & Hcsp & Hmtdc & Hregs & Hcells)".
    iEval (cbn [big_sepL2 exception_spill_regs]) in "Hregs Hcells".
    iDestruct "Hregs" as
      "(Hcra & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & _)".
    iDestruct "Hcells" as
      "(Hs1 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & _)".

    (* The stack pointer, MEPCC, mstatus, mcause and the dispatch *)
    iApply (exception_exiting_threads_rejoin_spec g_tstk P_mcause P_mtval _ _ _ _ _ _ _ _ _
              HP_mcause with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hca0 $Hmtdc $Hs0 $Hs2 $Hs17 $Hs18 $Hout $Hswitcher]").
    iNext; iIntros (wst cause zca0 tval Hcause Htval)
      "(HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Htok & Hmtval)".
    iApply ("Hpost" $! g_tstk wst cause zca0 tval).
    iSplit; first done. iSplit; first done.
    iFrame "HPC Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5
            Hmtdc Htok Hmtval".
    iClear "Hswitcher".
    rewrite /exception_spill /=.
    iRegionMerge.
    iEval (cbn [TrustedStack_offset_reg]) in
      "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    iFrame.
  Qed.

End Exception_Entry.
