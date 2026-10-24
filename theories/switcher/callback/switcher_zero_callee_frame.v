From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_stack_spec clear_registers_spec.

(** * Callback: clear the callee's frame and return to the caller

    [.Lswitcher_zero_callee_frame] clears the stack from its base to the
    cursor ([clear_stack_asm]), [.Lswitch_callee_dead_zeros] clears the
    registers that do not hold return values or the caller's restored state
    ([clear_registers_post_call_asm]), and [.Lswitcher_return_to_caller]
    returns to [cra]. [.Lswitch_callee_dead_zeros] is also the target of
    [.Lswitch_trusted_stack_exhausted]. *)

Section Switcher_Zero_Callee_Frame.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitcher_return_to_caller]: the jump to [wret], which faults
      when [wret] is not a valid target. *)
  Lemma switcher_return_to_caller_spec (wret : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitcher_return_to_caller" ∗
    cra ↦ᵣ wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ lupdatePcPerm wret ∗
          cra ↦ᵣ wret ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ wret -∗
        trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitcher_return_to_caller" "Hswitcher" as "Hcode".
    destruct (jalr_target_ok cnull cra wret.(lw)) eqn:Htgt; cycle 1.
    { (* The label would be unfolded by the simplifications of [iInstr_fail] *)
      set (off := switcher_label_offset ".Lswitcher_return_to_caller") in *.
      clearbody off.
      (* Jalr cnull cra *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[_ Hfailed]".
      iTrap with "Hfailed".
      done. }
    (* Jalr cnull cra *)
    iInstr "Hcode" with "Hlc".
    iDestruct "Hpost" as "[Hpost _]".
    iApply "Hpost". iFrame "HPC Hcra Hlc".
  Qed.

  (** From [.Lswitch_callee_dead_zeros]: clear the registers of [rmap] and
      jump to [wcra]. The jump faults when [wcra] is not a valid target. *)
  Lemma switch_callee_dead_zeros_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
    cra ↦ᵣ wcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        ( PC ↦ₚ lupdatePcPerm wcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_ret"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_callee_dead_zeros" "Hswitcher" as "Hcode".
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & _)".
    switcher_change_pc_label ".Lswitcher_return_to_caller".
    iApply (switcher_return_to_caller_spec with "[- $HPC $Hcra $Hswitcher_ret]").
    iSplit.
    - iNext; iIntros "(HPC & Hcra & Hlc)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[Hpost _]".
      iApply "Hpost"; iFrame "HPC Hlc".
    - iIntros "(%Htgt & Hcra)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[_ Hfailed]".
      by iApply "Hfailed".
  Qed.

  (** From [.Lswitcher_zero_callee_frame]: clear the caller's free part, the
      spill area and the callee's stack, from the base of the stack to the
      cursor [a], clear the registers and jump back to the caller [wcra']. *)
  Lemma switcher_zero_callee_frame_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp' wcra' wcs1' wcs0' wca2 wctp wct0 : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ; ct2 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_zero_callee_frame" ∗
    cgp ↦ᵣ wcgp' ∗
    cra ↦ᵣ wcra' ∗
    cs1 ↦ᵣ wcs1' ∗
    cs0 ↦ᵣ wcs0' ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ WInt a ∗
    ct2 ↦ᵣ WCap true RWL Local b e b ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ wcra' ∗
        cgp ↦ᵣ wcgp' ∗
        cs0 ↦ᵣ wcs0' ∗
        cs1 ↦ᵣ wcs1' ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a ]] ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        ( PC ↦ₚ lupdatePcPerm wcra' ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra'.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hbounds Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hct2 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_dz"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitcher_zero_callee_frame" "Hswitcher" as "Hcode".
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iApply (clear_stack_spec with "[ - $HPC $Hct2 $Hct1 $Hcode $Hstk]");
      [done|done| | | | |done|done|].
    1-3: clear -Hbounds; revert Hbounds; rewrite /switcher_stk_bounds; stk_unfold;
      intros (Hba & Hba3 & Ha4); solve_addr.
    { by apply disjoint_from_mmio_shadow. }
    iNext; iIntros "(HPC & Hct2 & Hct1 & _ & Hstk)".

    iDestruct (big_sepM_insert_2 with "[Hct2] Hrmap") as "Hrmap"; [iFrame "Hct2"|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap"; [iFrame "Hct1"|].
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap"; [iFrame "Hct0"|].
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap"; [iFrame "Hca2"|].
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap"; [iFrame "Hctp"|].
    switcher_change_pc_label ".Lswitch_callee_dead_zeros".
    iApply (switch_callee_dead_zeros_spec with "[- $HPC $Hcra $Hrmap $Hswitcher_dz]").
    { rewrite !dom_insert_L Hdom. clear. set_solver. }
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap)".
    iAssert ([[ stk_free_b b a , stk_free_e e a ]] ↦ₐ
               [[ region_addrs_zeroes (stk_free_b b a) (stk_free_e e a) ]])%I
      with "[Hstk]" as "Hstk"; first done.
    iEval (rewrite (stk_free_split_zeroes _ _ _ Hbounds)) in "Hstk".
    iDestruct (stk_free_split_join with "Hstk") as "[Hstk' Hstk]"; first done.
    { rewrite /region_addrs_zeroes length_replicate.
      clear -Hbounds; revert Hbounds; rewrite /switcher_stk_bounds; stk_unfold;
        intros (Hba & Hba3 & Ha4).
      rewrite /finz.dist. solve_addr. }
    iApply ("Hpost" $! rmap' with "[$Hcra $Hcgp $Hcs0 $Hcs1 $Hcsp $Hstk' $Hstk $Hrmap //]").
  Qed.

End Switcher_Zero_Callee_Frame.
