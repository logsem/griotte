From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_stack_spec clear_registers_spec.

(** * Callback: clear the callee's frame and return to the caller

    [.Lswitch_callee_stack_zero], at the end of the block
    [switcher_after_compartment_call], clears the stack from its base to
    the cursor ([clear_stack_asm]),
    [.Lswitch_callee_dead_zeros] clears the
    registers that do not hold return values or the caller's restored state
    ([clear_registers_post_call_asm]), and [.Lswitch_just_return]
    returns to [cra]. [.Lswitch_callee_dead_zeros] is also the target of
    [.Lswitch_trusted_stack_exhausted]. *)

Section Switcher_Zero_Callee_Frame.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_just_return]: the jump to [wret], which faults
      when [wret] is not a valid target. *)
  Lemma switcher_return_to_caller_spec (wret : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ[th] wret ∗
    switcher_code ∗
    ( ▷ ( PC ↦ₚ[th] lupdatePcPerm wret ∗
          cra ↦ᵣ[th] wret ∗
          £ 1 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ[th] wret -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (HO th) ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros "(HPC & Hcra & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_just_return" "Hswitcher" as "Hcode" a_ret Ha_ret.
    destruct (jalr_target_ok cnull cra wret.(lw)) eqn:Htgt; cycle 1.
    { (* The fault is at the start of the block. The label would be unfolded
         by the simplifications of [iInstr_fail] *)
      rewrite -Ha_ret.
      clear Ha_ret.
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

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
    cra ↦ᵣ[th] wcra ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ[th] wcra ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        ( PC ↦ₚ[th] lupdatePcPerm wcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_ret"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_callee_dead_zeros" "Hswitcher" as "Hcode".
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & _)".
    switcher_change_pc_label ".Lswitch_just_return".
    iApply (switcher_return_to_caller_spec with "[- $HPC $Hcra $Hswitcher_ret]").
    iSplit.
    - iNext; iIntros "(HPC & Hcra & Hlc)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[Hpost _]".
      iApply "Hpost"; iFrame "HPC Hlc".
    - iIntros "(%Htgt & Hcra)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[_ Hfailed]".
      by iApply "Hfailed".
  Qed.

  (** From [.Lswitch_callee_stack_zero]: clear the caller's free part, the
      spill area and the callee's stack, from the base of the stack to the
      cursor [a], clear the registers and jump back to the caller [wcra']. *)
  Lemma switcher_zero_callee_frame_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp' wcra' wcs1' wcs0' wca2 wctp wct0 wct1 wct2 : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ; ct2 ]} ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_stack_zero" ∗
    cgp ↦ᵣ[th] wcgp' ∗
    cra ↦ᵣ[th] wcra' ∗
    cs1 ↦ᵣ[th] wcs1' ∗
    cs0 ↦ᵣ[th] wcs0' ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    ctp ↦ᵣ[th] wctp ∗
    csp ↦ᵣ[th] WCap true RWL Local b e a ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ[th] wcra' ∗
        cgp ↦ᵣ[th] wcgp' ∗
        cs0 ↦ᵣ[th] wcs0' ∗
        cs1 ↦ᵣ[th] wcs1' ∗
        csp ↦ᵣ[th] WCap true RWL Local b e a ∗
        [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a ]] ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        ( PC ↦ₚ[th] lupdatePcPerm wcra' ∗
          £ 1 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra'.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hbounds Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hct2 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & Hrmap & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_dz"; first iFrame "Hswitcher".
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_stack_zero" "HPC".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode".
    iEval (rewrite -(take_drop 19 (encodeInstrsW _))) in "Hcode".
    iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode_zero]".
    rewrite length_take_le; last (cbn; lia).
    iEval (rewrite (_ : (a_block ^+ 19)%a = (a_block ^+ 19%nat)%a); last done) in "HPC".
    assert (SubBounds b_switcher e_switcher (a_block ^+ 19%nat)%a
              ((a_block ^+ 19%nat) ^+ length (clear_stack_instrs ct2 ct1))%a) as Hsub_zero.
    { cbn [length clear_stack_instrs]. clear -H0. solve_addr. }
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iApply (clear_stack_spec with "[ - $HPC $Hct2 $Hct1 $Hcode_zero $Hstk]");
      [done|exact Hsub_zero| | | | |done|done|].
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
