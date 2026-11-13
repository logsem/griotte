From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules rules_vcsr proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_exception_states trusted_spill_registers_spec.

(** * Exception path: the exception entry

    [exception_entry_asm] swaps the trusted stack in from mtdc (a null mtdc
    would mean that the exception entry is re-entered, which the base of
    the trusted stack, not at address 0, rules out), and spills the
    registers of the interrupted context in the register save area, but the
    stack pointer. The swap lends mtdc: the thread's mtdc token goes.
    [.Lexception_exiting_threads_rejoin] spills the stack pointer, from
    mtdc, which is cleared, the PC (MEPCC), mstatus (MIE disabled, MPIE the
    posture of the interrupted context) and the cause (mcause). The block
    runs at InterruptDisabled, with the volatile registers of the posture
    of the thread. A cause of the range of trap entry is handled by the
    compartments: the block jumps to [.Lhandle_error]. *)

Section Exception_Entry.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From the test of [exception_entry_asm], after its swap, at any thread
      and any mtdc: the stack pointer holds the trusted stack of [o], which
      is not null, and the registers of the interrupted context but the
      stack pointer are spilled in its register save area. *)
  Lemma exception_entry_spill_spec (o : Thread) (g_tstk : Locality) (wregs wold : list LWord) :
    PC ↦ₚ[th] switcher_pc (switcher_label_offset "exception_entry_asm" + 1) ∗
    csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                 (@b_trusted_stack (tlayout_of o)) ∗
    ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
    ([∗ list] r;w ∈ exception_spill_regs;wold,
       (@b_trusted_stack (tlayout_of o) ^+ TrustedStack_offset_reg r) ↦ₐ w) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
        csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                     (@b_trusted_stack (tlayout_of o)) ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs,
           (@b_trusted_stack (tlayout_of o) ^+ TrustedStack_offset_reg r) ↦ₐ w) -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcsp & Hregs & Hcells & #Hswitcher & Hpost)".
    (* The code at the instance of [th]; a local copy of [th] is found first
       by the instance search, before [o]. *)
    iEval (rewrite (codefrag_pers_thread_indep o th)) in "Hswitcher".
    pose (th_pin := th).
    pose proof (trusted_stack_base_nonzero (tlayout := tlayout_of o)) as Hts_nonzero.
    switcher_open_label "exception_entry_asm" "Hswitcher" as "Hcode" a_entry Ha_entry.
    switcher_hide "Hpost" as hpost.
    iAssert (codefrag_pers (ceriseg := ceriseG_of th) (a_entry ^+ 2%nat)
               (trusted_spill_registers_instrs exception_spill_regs)) as "#Hspill".
    { iEval (rewrite -(take_drop 2 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; [iExact "Hcode'" | cbn; lia]. }
    switcher_set_pc (a_entry ^+ 1%nat)%a.
    (* Jeq .Lexception_reentered csp 0 *)
    iInstr "Hcode".
    { rewrite /nonZero /=; apply negb_true_iff, Z.eqb_neq; exact Hts_nonzero. }
    iApply (trusted_spill_registers_spec (ceriseg := ceriseG_of th) (th := th)
              (CL := crit_link_full th) with "[- $HPC $Hcsp $Hregs $Hcells $Hspill]");
      [done | done | | apply (trusted_save_cells_ok_exception (th := o))
      | rewrite /exception_spill_regs; set_solver | rewrite /exception_spill_regs; set_solver |].
    { rewrite trusted_spill_registers_instrs_length /exception_spill_regs; cbn [length].
      solve_addr. }
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells & _)".
    rewrite trusted_spill_registers_instrs_length /exception_spill_regs; cbn [length].
    switcher_change_pc_label ".Lexception_exiting_threads_rejoin".
    subst hpost; iApply "Hpost"; iFrame "HPC Hcsp Hregs Hcells".
  Qed.

  (** [exception_entry_asm]: swap the trusted stack in from mtdc (mtdc is
      not null; the mtdc token goes), and spill the registers of the
      interrupted context but the stack pointer. *)
  #[local] Lemma exception_entry_block_spec (wcsp : LWord) (wregs wold : list LWord) :
    th ≠ CtxSwitch →
    mtdc_home = Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack →
    PC ↦ₚ[th] switcher_label_pc "exception_entry_asm" ∗
    csp ↦ᵣ[th] wcsp ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    mtdc_lent ∗
    ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
    ([∗ list] r;w ∈ exception_spill_regs;wold, (b_trusted_stack ^+ TrustedStack_offset_reg r) ↦ₐ w) ∗
    switcher_code ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[th] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
        csp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
        mtdc ↦ₜ[th] ExceptionScratch wcsp ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs, r ↦ᵣ[th] w) ∗
        ([∗ list] r;w ∈ exception_spill_regs;wregs,
           (b_trusted_stack ^+ TrustedStack_offset_reg r) ↦ₐ w) -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hth Hhome) "(HPC & Hcsp & Hmtdc & Hlent & Hregs & Hcells & #Hswitcher & Hpost)".
    iPoseProof "Hswitcher" as "#Hswitcher_all".
    switcher_open_label "exception_entry_asm" "Hswitcher" as "Hcode" a_entry Ha_entry.
    (* SpecialRW csp mtdc csp *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_open_full _ _ _ _ _ _ _ _ _ csp wcsp _ (ExceptionScratch wcsp))
      with "[$HPC $Hcsp $Hmtdc $Hlent]" as (vm) "(%Hmatch & HPC & Hcsp & Hmtdc)";
      [by rewrite Hhome | apply mtdc_match_ExceptionScratch |].
    destruct (mtdc_match_TStack_cap _ _ _ _ _ Hmatch) as [g_tstk ->].
    switcher_change_pc (switcher_label_offset "exception_entry_asm" + 1)%Z.
    iApply (exception_entry_spill_spec th g_tstk wregs wold
             with "[$HPC $Hcsp $Hregs $Hcells $Hswitcher_all Hpost Hmtdc]").
    iNext; iIntros "(HPC & Hcsp & Hregs & Hcells)".
    iApply ("Hpost" $! g_tstk). iFrame "HPC Hcsp Hmtdc Hregs Hcells".
  Qed.

  (** [.Lexception_exiting_threads_rejoin] after its mtdc swap, at any thread
      and any mtdc: the interrupted stack pointer [wcsp], MEPCC [wm], mstatus
      (MIE disabled, MPIE [b]) and the cause [cause] are saved in the
      register save area of [o]; the code reaches the dispatch. *)
  Lemma exception_rejoin_save_spec (o : Thread) (g_tstk : Locality) (b : InterruptStatus)
      (cause : Z) (wm wcsp wct0 ws0 ws2 ws17 ws18 : LWord) :
    PC ↦ₚ[th] switcher_pc (switcher_label_offset ".Lexception_exiting_threads_rejoin" + 2) ∗
    csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                 (@b_trusted_stack (tlayout_of o)) ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wcsp ∗
    (@b_trusted_stack (tlayout_of o)) ↦ₐ ws0 ∗
    (@b_trusted_stack (tlayout_of o) ^+ 2) ↦ₐ ws2 ∗
    (@b_trusted_stack (tlayout_of o) ^+ 17) ↦ₐ ws17 ∗
    (@b_trusted_stack (tlayout_of o) ^+ 18) ↦ₐ ws18 ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    MPIE_frag b ∗
    mepcc ↦ₓ wm ∗
    mcause ↦ₓ lword_of_word (WInt cause) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_label_pc ".Lexception_might_handle" ∗
        csp ↦ᵣ[th] Cap RWL g_tstk (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                     (@b_trusted_stack (tlayout_of o)) ∗
        ct0 ↦ᵣ[th] wm ∗
        ct1 ↦ᵣ[th] WInt cause ∗
        (@b_trusted_stack (tlayout_of o)) ↦ₐ wm ∗
        (@b_trusted_stack (tlayout_of o) ^+ 2) ↦ₐ wcsp ∗
        (@b_trusted_stack (tlayout_of o) ^+ 17) ↦ₐ WInt (mstatus_enc InterruptDisabled b) ∗
        (@b_trusted_stack (tlayout_of o) ^+ 18) ↦ₐ WInt cause ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        MPIE_frag b ∗
        mepcc ↦ₓ wm ∗
        mcause ↦ₓ lword_of_word (WInt cause) -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hs0 & Hs2 & Hs17 & Hs18 & Hmie & Hmpie
       & Hmepcc & Hmcause & #Hswitcher & Hpost)".
    (* The code at the instance of [th]; a local copy of [th] is found first
       by the instance search, before [o]. *)
    iEval (rewrite (codefrag_pers_thread_indep o th)) in "Hswitcher".
    pose (th_pin := th).
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of o)) as [n Hfit].
    pose proof (trusted_stack_disjoint_from_shadow (tlayout := tlayout_of o)) as Hts_shadow.
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     (@b_trusted_stack (tlayout_of o) + k)%a =
                       Some (@b_trusted_stack (tlayout_of o) ^+ k)) as Hts_k
      by (intros k Hk; tstack_unfold; solve_addr).
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     is_shadow_address (@b_trusted_stack (tlayout_of o) ^+ k) = false)
      as Hts_k_shadow.
    { intros k Hk. tstk_not_shadow Hts_shadow. }
    assert (∀ k : Z, (0 <= k <= 21)%Z →
                     withinBounds (@b_trusted_stack (tlayout_of o)) (@e_trusted_stack (tlayout_of o))
                       (@b_trusted_stack (tlayout_of o) ^+ k) = true)
      as Hts_k_bounds.
    { intros k Hk. rewrite /withinBounds. tstack_unfold; solve_addr. }
    switcher_open_label ".Lexception_exiting_threads_rejoin" "Hswitcher" as "Hcode" a_rejoin
      Ha_rejoin.
    switcher_hide "Hpost" as hpost.
    switcher_set_pc (a_rejoin ^+ 2%nat)%a.
    pose proof (Hts_k 2 ltac:(lia)) as Hts_2.
    (* Store csp ct1 2 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    iEval (rewrite -!(vcsr_frag_pointsto (ceriseg := ceriseG_of th))) in "Hmepcc Hmcause".
    (* SpecialRW ct0 mepcc cnull *)
    iInstrApply "Hcode" wp_cspecialr_vcsr with "[$HPC $Hct0 $Hmepcc]" as "(HPC & Hct0 & Hmepcc)".
    assert ((@b_trusted_stack (tlayout_of o) + 0)%a = Some (@b_trusted_stack (tlayout_of o)))
      as Hts_0 by solve_addr.
    (* Store csp ct0 0 *)
    iInstr "Hcode"; [tstk_not_shadow Hts_shadow | rewrite /withinBounds; tstack_unfold; solve_addr |].
    (* SpecialRW ct1 mstatus cnull *)
    iInstrApply "Hcode" (wp_csrr_mstatus_frag _ _ _ _ _ _ _ _ _ _ _ InterruptDisabled b)
      with "[$HPC $Hct1 $Hmie $Hmpie]" as "(HPC & Hct1 & Hmie & Hmpie)".
    pose proof (Hts_k 17 ltac:(lia)) as Hts_17.
    (* Store csp ct1 17 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    (* SpecialRW ct1 mcause cnull *)
    iInstrApply "Hcode" wp_cspecialr_vcsr with "[$HPC $Hct1 $Hmcause]" as "(HPC & Hct1 & Hmcause)".
    iEval (rewrite !vcsr_frag_pointsto) in "Hmepcc Hmcause".
    pose proof (Hts_k 18 ltac:(lia)) as Hts_18.
    (* Store csp ct1 18 *)
    iInstr "Hcode"; [by apply Hts_k_shadow; lia | by apply Hts_k_bounds; lia |].
    repeat rewrite lstore_word_isWL; try reflexivity.
    switcher_change_pc_label ".Lexception_might_handle".
    subst hpost; iApply "Hpost".
    iFrame "HPC Hcsp Hct0 Hct1 Hs0 Hs2 Hs17 Hs18 Hmie Hmpie Hmepcc Hmcause".
  Qed.

  (** [.Lexception_exiting_threads_rejoin], at InterruptDisabled with MPIE
      [b]: the stack pointer, MEPCC, mstatus and mcause [cause], a fault
      cause, then the dispatch on the cause. *)
  #[local] Lemma exception_exiting_threads_rejoin_spec
    (g_tstk : Locality) (b : InterruptStatus) (cause : Z)
    (w wcsp wct0 wct1 wca0 ws0 ws2 ws17 ws18 : LWord) :
    mcause_ok cause →
    th ≠ CtxSwitch →
    mtdc_home = Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack →
    PC ↦ₚ[th] switcher_label_pc ".Lexception_exiting_threads_rejoin" ∗
    csp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    mtdc ↦ₜ[th] ExceptionScratch wcsp ∗
    b_trusted_stack ↦ₐ ws0 ∗
    (b_trusted_stack ^+ 2) ↦ₐ ws2 ∗
    (b_trusted_stack ^+ 17) ↦ₐ ws17 ∗
    (b_trusted_stack ^+ 18) ↦ₐ ws18 ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    MPIE_frag b ∗
    mepcc ↦ₓ lmepcc_of_pc w ∗
    mcause ↦ₓ lword_of_word (WInt cause) ∗
    switcher_code ∗
    ▷ ( ∀ zca0 : Z,
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
          csp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
          ct0 ↦ᵣ[th] lmepcc_of_pc w ∗
          ct1 ↦ᵣ[th] WInt cause ∗
          ca0 ↦ᵣ[th] WInt zca0 ∗
          mtdc ↦ₜ[th] ExceptionScratch (WInt 0) ∗
          b_trusted_stack ↦ₐ lmepcc_of_pc w ∗
          (b_trusted_stack ^+ 2) ↦ₐ wcsp ∗
          (b_trusted_stack ^+ 17) ↦ₐ WInt (mstatus_enc InterruptDisabled b) ∗
          (b_trusted_stack ^+ 18) ↦ₐ WInt cause ∗
          MIE ↦ₜ[th] InterruptDisabled ∗
          MPIE_frag b ∗
          mepcc ↦ₓ lmepcc_of_pc w ∗
          mcause ↦ₓ lword_of_word (WInt cause) -∗
          safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hcause Hth Hhome)
      "(HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Hmie & Hmpie
       & Hmepcc & Hmcause & #Hswitcher & Hpost)".
    iPoseProof "Hswitcher" as "#Hswitcher_all".
    switcher_open_label ".Lexception_exiting_threads_rejoin" "Hswitcher" as "Hcode" a_rejoin
      Ha_rejoin.
    switcher_hide "Hpost" as hpost.

    (* The interrupted stack pointer, from mtdc *)
    (* Mov ct1 0 *)
    iInstr "Hcode".
    (* SpecialRW ct1 mtdc ct1 *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_ex_full _ _ _ _ _ _ _ _ _ ct1 _ (ExceptionScratch wcsp)
         (ExceptionScratch (lword_of_word (WInt 0))))
      with "[$HPC $Hct1 $Hmtdc]" as (vm) "(%Hmatch & HPC & Hct1 & Hmtdc)";
      [by rewrite Hhome | apply mtdc_match_ExceptionScratch |].
    cbn in Hmatch; subst vm.

    (* The stack pointer, MEPCC, mstatus and mcause *)
    switcher_change_pc (switcher_label_offset ".Lexception_exiting_threads_rejoin" + 2)%Z.
    iApply (exception_rejoin_save_spec th g_tstk b cause (lmepcc_of_pc w)
             with "[$HPC $Hcsp $Hct0 $Hct1 $Hs0 $Hs2 $Hs17 $Hs18 $Hmie $Hmpie $Hmepcc $Hmcause
                    $Hswitcher_all Hpost Hca0 Hmtdc]").
    iNext; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hs0 & Hs2 & Hs17 & Hs18 & Hmie & Hmpie
                     & Hmepcc & Hmcause)".
    switcher_pc_in_block ".Lexception_exiting_threads_rejoin" ".Lexception_might_handle" "HPC".
    (* Dispatch on the cause *)
    (* Mov ca0 MCAUSE_CHERI *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    repeat rewrite lstore_word_isWL; try reflexivity.
    iAssert (∀ zca0 : Z,
                PC ↦ₚ switcher_label_pc ".Lhandle_error" -∗
                ca0 ↦ᵣ WInt zca0 -∗
                ct1 ↦ᵣ WInt cause -∗
                WP Exec {{ HO th }})%I
      with "[- Hca0 HPC Hct1]" as "Hpost".
    { iIntros (zca0) "HPC Hca0 Hct1".
      subst hpost.
      iApply ("Hpost" $! zca0).
      iFrame "HPC Hcsp Hct0 Hct1 Hca0 Hmtdc Hs0 Hs2 Hs17 Hs18 Hmie Hmpie Hmepcc Hmcause". }
    destruct (decide (cause = 28%Z)) as [-> | Hcause_ne].
    - (* Jeq .Lhandle_error ca0 ct1 *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error")%a
          by switcher_addr_eq. }
      iApply ("Hpost" with "HPC Hca0 Hct1").
    - (* Jeq .Lhandle_error ca0 ct1 *)
      iInstr "Hcode".
      (* Mov ca0 8 *)
      iInstr "Hcode".
      destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
      (* Jlt .Lhandle_error ct1 ca0 *)
      iInstr "Hcode" using jcond_jump_agree_jmp.
      { cbn [jcond_test get_a lw]; apply Z.ltb_lt; destruct Hcause; lia. }
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lhandle_error")%a
          by switcher_addr_eq. }
      iApply ("Hpost" with "HPC Hca0 Hct1").
  Qed.

  (** From [exception_entry_asm], at InterruptDisabled with MPIE [b], for
      a fault at [w] of cause [cause]: lend mtdc, spill the interrupted
      context in the register save area (with mstatus at MIE disabled and
      MPIE [b]), and go to [.Lhandle_error]. *)
  Lemma exception_entry_asm_spec (b : InterruptStatus) (cause : Z)
    (w : LWord) (save_area : list LWord)
    (wcra wcsp wcgp wctp wct0 wct1 wct2 wcs0 wcs1 wca0 wca1 wca2 wca3 wca4 wca5 : LWord) :
    mcause_ok cause ->
    th ≠ CtxSwitch ->
    mtdc_home = Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ->
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
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    mtdc_lent ∗
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save_area ]] ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    MPIE_frag b ∗
    mepcc ↦ₓ lmepcc_of_pc w ∗
    mcause ↦ₓ lword_of_word (WInt cause) ∗
    switcher_code ∗
    ▷ ( ∀ (g_tstk : Locality) (zca0 : Z),
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error" ∗
          cra ↦ᵣ[th] wcra ∗
          csp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
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
                 (WInt (mstatus_enc InterruptDisabled b)) (WInt cause) ]] ∗
          MIE ↦ₜ[th] InterruptDisabled ∗
          MPIE_frag b ∗
          mepcc ↦ₓ lmepcc_of_pc w ∗
          mcause ↦ₓ lword_of_word (WInt cause) -∗
          safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hcause Hth Hhome Hlen)
      "(HPC & Hcra & Hcsp & Hcgp & Hctp & Hct0 & Hct1 & Hct2 & Hcs0 & Hcs1
       & Hca0 & Hca1 & Hca2 & Hca3 & Hca4 & Hca5 & Hmtdc & Hlent & Hsave & Hmie & Hmpie
       & Hmepcc & Hmcause & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    destruct save_area as
      [|s0 [|s1 [|s2 [|s3 [|s4 [|s5 [|s6 [|s7 [|s8 [|s9 [|s10
      [|s11 [|s12 [|s13 [|s14 [|s15 [|s16 [|s17 [|s18 [|s19 [|s20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    rewrite /tstack_save_end.
    assert ((b_trusted_stack + 21%nat)%a = Some (b_trusted_stack ^+ TSTACK_REGFRAME_SZ))
      as Hsave_end by (tstack_unfold; solve_addr).
    iRegionSplit "Hsave" as
      "(Hs0 & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7 & Hs8 & Hs9 & Hs10
       & Hs11 & Hs12 & Hs13 & Hs14 & Hs15 & Hs16 & Hs17 & Hs18 & Hs19 & Hs20)".

    (* Swap the trusted stack in, spill the registers but the stack pointer *)
    iApply (exception_entry_block_spec _
              [wcra; wcgp; wctp; wct0; wct1; wct2; wcs0; wcs1; wca0; wca1; wca2; wca3; wca4; wca5]
              [s1; s3; s4; s5; s6; s7; s8; s9; s10; s11; s12; s13; s14; s15] Hth Hhome
             with "[- $HPC $Hcsp $Hmtdc $Hlent $Hswitcher]").
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
    iApply (exception_exiting_threads_rejoin_spec g_tstk b cause _ _ _ _ _ _ _ _ _
              Hcause Hth Hhome with
             "[- $HPC $Hcsp $Hct0 $Hct1 $Hca0 $Hmtdc $Hs0 $Hs2 $Hs17 $Hs18 $Hmie $Hmpie
                 $Hmepcc $Hmcause $Hswitcher]").
    iNext; iIntros (zca0)
      "(HPC & Hcsp & Hct0 & Hct1 & Hca0 & Hmtdc & Hs0 & Hs2 & Hs17 & Hs18 & Hmie & Hmpie
        & Hmepcc & Hmcause)".
    iApply ("Hpost" $! g_tstk zca0).
    iFrame "HPC Hcra Hcsp Hcgp Hctp Hct0 Hct1 Hct2 Hcs0 Hcs1 Hca0 Hca1 Hca2 Hca3 Hca4 Hca5
            Hmtdc Hmie Hmpie Hmepcc Hmcause".
    iClear "Hswitcher".
    rewrite /exception_spill /=.
    iRegionMerge.
    iEval (cbn [TrustedStack_offset_reg]) in
      "Hs1 Hs3 Hs4 Hs5 Hs6 Hs7 Hs8 Hs9 Hs10 Hs11 Hs12 Hs13 Hs14 Hs15".
    iFrame.
  Qed.

End Exception_Entry.
