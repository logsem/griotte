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

  (** From [.Lswitch_just_return], at the posture [b]: the jump to [wret],
      which moves the posture to the one [wret] restores, and faults when
      [wret] is not a valid target. *)
  Lemma switcher_return_to_caller_spec (wret : LWord) (b : InterruptStatus) :
    th ≠ CtxSwitch →
    route_pre th b →
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_just_return" ∗
    cra ↦ᵣ[th] wret ∗
    switcher_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ( ▷ ( PC ↦ₚ[th] lupdatePcPerm wret ∗
          cra ↦ᵣ[th] wret ∗
          MIE ↦ₜ[th] default b (jalr_target_mie wret.(lw)) ∗
          held (th := th) (default b (jalr_target_mie wret.(lw))) ∗
          £ 1 -∗
          safe[th] ) ∧
      ( ⌜jalr_target_ok cnull cra wret.(lw) = false⌝ ∗
        cra ↦ᵣ[th] wret ∗
        MIE ↦ₜ[th] b ∗
        held (th := th) b -∗
        trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
          (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hth Hpre) "(HPC & Hcra & #Hswitcher & Hmie & Hheld & Hpost)".
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
    iApply "Hpost". iFrame "HPC Hcra Hmie Hheld Hlc".
  Qed.

  (** From [.Lswitch_callee_dead_zeros]: clear the registers of [rmap] and
      jump to [wcra]. The jump faults when [wcra] is not a valid target. *)
  Lemma switch_callee_dead_zeros_spec (wcra : LWord) (rmap : LReg) (b : InterruptStatus) :
    dom rmap = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ->
    th ≠ CtxSwitch ->
    route_pre th b ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
    cra ↦ᵣ[th] wcra ∗
    regs[th] rmap ∗
    switcher_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ[th] wcra ∗
        regs₀[th] rmap' -∗
        ( PC ↦ₚ[th] lupdatePcPerm wcra ∗
          MIE ↦ₜ[th] default b (jalr_target_mie wcra.(lw)) ∗
          held (th := th) (default b (jalr_target_mie wcra.(lw))) ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜ jalr_target_ok cnull cra wcra.(lw) = false ⌝ -∗
          MIE ↦ₜ[th] b -∗
          held (th := th) b -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hdom Hth Hpre) "(HPC & Hcra & Hrmap & #Hswitcher & Hmie & Hheld & Hpost)".
    iAssert switcher_code as "Hswitcher_ret"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_callee_dead_zeros" "Hswitcher" as "Hcode".
    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]");
      try solve_pure.
    iNext; iIntros "(%rmap' & %Hrmap' & HPC & Hrmap & _)".
    switcher_change_pc_label ".Lswitch_just_return".
    iApply (switcher_return_to_caller_spec _ b with "[- $HPC $Hcra $Hswitcher_ret $Hmie $Hheld]");
      [done | done |].
    iSplit.
    - iNext; iIntros "(HPC & Hcra & Hmie & Hheld & Hlc)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[Hpost _]".
      iApply "Hpost"; iFrame "HPC Hmie Hheld Hlc".
    - iIntros "(%Htgt & Hcra & Hmie & Hheld)".
      iDestruct ("Hpost" $! rmap' with "[$Hcra $Hrmap //]") as "[_ Hfailed]".
      by iApply ("Hfailed" with "[//] Hmie Hheld").
  Qed.

  (** From [.Lswitch_callee_dead_zeros], in [switcher_zero_callee_frame_spec]:
      clear the registers, and go to the continuation. *)
  #[local] Ltac zero_frame_dead_zeros mie Hdom :=
    iDestruct (big_sepM_insert_2 with "[Hct2] Hrmap") as "Hrmap"; [iFrame "Hct2"|];
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap"; [iFrame "Hct1"|];
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap"; [iFrame "Hct0"|];
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap"; [iFrame "Hca2"|];
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap"; [iFrame "Hctp"|];
    switcher_change_pc_label ".Lswitch_callee_dead_zeros";
    iApply (switch_callee_dead_zeros_spec _ _ mie
              with "[- $HPC $Hcra $Hrmap $Hswitcher_dz $Hmie $Hheld]");
    [ rewrite !dom_insert_L Hdom; clear; set_solver | assumption | assumption | ];
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap)";
    iDestruct "Hpost" as "[Hpost _]".

  (** In [switcher_zero_callee_frame_spec], when MSHWM is at or above the
      cursor: the zeroing stores nothing, and the cells are unchanged. *)
  #[local] Ltac zero_frame_skip mie v a mshwmb_v Hdom :=
    (* Jle 4 ct1 ct2 *)
    iInstr "Hcode_zero";
    iAssert ([[ a , a ]] ↦ₐ [[ 0…0 ]])%I as "Hnil";
    [ rewrite /region_pointsto /region_addrs_zeroes finz_seq_between_empty; [|solve_addr];
      rewrite finz_dist_0; [done | solve_addr] | ];
    iAssert (hwm_regs mshwmb_v v) with "[$Hmshwmb $Hmshwm]" as "Hhwm";
    (* SpecialRW cnull MSHWM (inr csp) *)
    iInstrApply "Hcode_csrw" (wp_csrw_mshwm_zeroed _ _ _ _ _ _ _ _ _ _ _ mshwmb_v v a a)
      with "[$HPC $Hcsp $Hhwm $Hnil]" as "Hres";
    [ done | solve_addr | right; split; [done | lia] | lia | ];
    iDestruct "Hres" as "(HPC & Hcsp & Hhwm & _)";
    zero_frame_dead_zeros mie Hdom.

  (** From [.Lswitch_callee_stack_zero]: clear the caller's free part, the
      spill area and the callee's stack, from the value [mshwm_v] of MSHWM to the
      cursor [a], write [a] to MSHWM, clear the registers and jump back to
      the caller [wcra']. The cells below [mshwm_v] are left. When [mshwm_v] is below
      the base of the stack, the first store of the zeroing faults. *)
  Lemma switcher_zero_callee_frame_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp' wcra' wcs1' wcs0' wca2 wctp wct0 wct1 wct2 : LWord)
    (rmap : LReg) (mie : InterruptStatus) (mshwmb_v mshwm_v : Z) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ; ct2 ]} ->
    th ≠ CtxSwitch ->
    route_pre th mie ->
    (0 <= mshwmb_v <= mshwm_v)%Z ->

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
    csp ↦ᵣ[th] Cap RWL Local b e a ∗
    stack_region (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size) [wcs0; wcs1; wcgp; wcra] ∗
    stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
    hwm_regs mshwmb_v mshwm_v ∗
    regs[th] rmap ∗
    switcher_code ∗
    MIE ↦ₜ[th] mie ∗
    held (th := th) mie ∗
    ( ▷ ( ∀ rmap' : LReg,
          (* the zeroing, from the value [mshwm_v] read from MSHWM, did not fault *)
          ⌜(b <= mshwm_v)%Z⌝ -∗
          ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
          cra ↦ᵣ[th] wcra' ∗
          cgp ↦ᵣ[th] wcgp' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          stack_region (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)
            (stack_zeroed_from (stk_spill_a a) mshwm_v [wcs0; wcs1; wcgp; wcra]) ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a)
            (stack_zeroed_from (stk_callee_b b a) mshwm_v stk_mem) ∗
          hwm_regs mshwmb_v a ∗
          regs₀[th] rmap' -∗
          ( PC ↦ₚ[th] lupdatePcPerm wcra' ∗
            MIE ↦ₜ[th] default mie (jalr_target_mie wcra'.(lw)) ∗
            held (th := th) (default mie (jalr_target_mie wcra'.(lw))) ∗
            £ 1 -∗
            safe[th] ) ∧
          ( ⌜ jalr_target_ok cnull cra wcra'.(lw) = false ⌝ -∗
            MIE ↦ₜ[th] mie -∗
            held (th := th) mie -∗
            trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
              (HO th) ) ) ∧
      (* the first store of the zeroing faults: [mshwm_v] is below the base *)
      ( ∀ off : Z,
          ⌜(mshwm_v < b)%Z⌝ -∗
          ⌜ trap_no_resume (switcher_pc off) ⌝ -∗
          cgp ↦ᵣ[th] wcgp' ∗
          cra ↦ᵣ[th] wcra' ∗
          cs1 ↦ᵣ[th] wcs1' ∗
          cs0 ↦ᵣ[th] wcs0' ∗
          ct0 ↦ᵣ[th] wct0 ∗
          ct1 ↦ᵣ[th] WInt a ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          ca2 ↦ᵣ[th] wca2 ∗
          ctp ↦ᵣ[th] WInt mshwm_v ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          stack_region (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size) [wcs0; wcs1; wcgp; wcra] ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
          hwm_regs mshwmb_v mshwm_v ∗
          regs[th] rmap ∗
          MIE ↦ₜ[th] mie ∗
          held (th := th) mie -∗
          trap_safe (switcher_pc off) ⊤ (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hbounds Hstk_mmio Hdom Hth Hpre Hhwm_ok)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hct2 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & [Hmshwmb Hmshwm] & Hrmap & #Hswitcher & Hmie & Hheld & Hpost)".
    iAssert switcher_code as "Hswitcher_dz"; first iFrame "Hswitcher".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_stack_zero" "HPC".
    (* SpecialRW ctp MSHWM (inr cnull) *)
    iInstrApply "Hcode" wp_csrr_mshwm with "[$HPC $Hctp $Hmshwm]"
      as "(HPC & Hctp & Hmshwm)".
    (* GetA ct1 csp *)
    iInstr "Hcode".
    iAssert (codefrag_pers (a_block ^+ 19%nat) (clear_stack_instrs ct2 ct1)) as "Hcode_zero".
    { iEval (rewrite -(take_drop 19 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iEval (rewrite -(take_drop 4 (drop 19 _))) in "Hcode'".
      iDestruct (codefrag_app_pers with "Hcode'") as "[Hcode'' _]".
      iExact "Hcode''". }
    iAssert (codefrag_pers (a_block ^+ 23%nat)
               (encodeInstrsW [SpecialRW cnull mshwm (inr csp)])) as "Hcode_csrw".
    { iEval (rewrite -(take_drop 23 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iExact "Hcode'". }
    assert (0 <= mshwm_v)%Z as Hv0 by lia.
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
    rewrite finz_seq_between_length in Hlen_stk.
    destruct (decide (a <= mshwm_v)%Z) as [Hav | Hva].
    { (* MSHWM is at or above the cursor: nothing is stored *)
      destruct (finz_of_z_spec MemNum mshwm_v) as [ (va & Hva_some & Hvaeq) | [Hnone _] ].
      - (* SetA ct2 csp ctp *)
        iInstr "Hcode".
        zero_frame_skip mie mshwm_v a mshwmb_v Hdom.
        iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
        rewrite (stack_zeroed_from_above (a ^- 4)); last (cbn; solve_addr).
        rewrite (stack_zeroed_from_above b); last (rewrite -Hlen_stk /finz.dist; solve_addr).
        iFrame "∗ %".
      - (* SetA ct2 csp ctp *)
        iInstr "Hcode".
        zero_frame_skip mie mshwm_v a mshwmb_v Hdom.
        iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
        rewrite (stack_zeroed_from_above (a ^- 4)); last (cbn; solve_addr).
        rewrite (stack_zeroed_from_above b); last (rewrite -Hlen_stk /finz.dist; solve_addr).
        iFrame "∗ %". }
    destruct (finz_of_z_spec MemNum mshwm_v) as [ (va & Hva_some & Hvaeq) | [_ Hnone] ];
      last (exfalso; solve_addr).
    subst mshwm_v.
    (* SetA ct2 csp ctp *)
    iInstr "Hcode".
    destruct (decide (b <= va)%a) as [Hbva | Hvab]; cycle 1.
    { (* The first store of the zeroing faults *)
      iPoseProof (hwm_closed_user th Hth) as "Hclosed".
      iApply (clear_stack_below_base_spec with "[- $HPC $Hcode_zero $Hct2 $Hct1 $Hclosed]");
        try solve_pure.
      { cbn [length clear_stack_instrs]; solve_addr. }
      all: try solve_addr.
      iIntros "[Hct2 Hct1] _".
      iDestruct "Hpost" as "[_ Hfailed]".
      rewrite (_ : (a_block ^+ 19%nat) ^+ 1
                   = a_switcher_call
                      ^+ (switcher_label_offset "switcher_after_compartment_call" + 20));
        last (subst a_block; switcher_addr_eq).
      iApply ("Hfailed" with "[%] [%] [$Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2
                $Hctp $Hcsp $Hcells $Hstk $Hmshwmb $Hmshwm $Hrmap $Hmie $Hheld]").
      { solve_addr. }
      { apply trap_no_resume_switcher_pc; by vm_compute. } }
    (* The free part, from [va] to the cursor, is zeroed *)
    iEval (rewrite (_ : (a ^- 4) ^+ SpillSlot_size = a);
           last (rewrite /SpillSlot_size; solve_addr)) in "Hcells".
    iAssert (stack_region b a (stk_mem ++ [wcs0; wcs1; wcgp; wcra])) with "[Hstk Hcells]"
      as "Hfree".
    { erewrite <- (stack_region_app b _ a); [iFrame | solve_addr | solve_addr | by rewrite Hlen_stk]. }
    iDestruct (stack_region_split b va with "Hfree") as "[Hlo Hhi]"; [solve_addr | solve_addr |].
    iApply (clear_stack_spec _ _ _ _ _ _ b e va a ct2 ct1 _ mshwmb_v va
             with "[- $HPC $Hct2 $Hct1 $Hcode_zero $Hhi $Hmshwmb $Hmshwm]");
      try solve_pure.
    { cbn [length clear_stack_instrs]; solve_addr. }
    { solve_addr. }
    { cbn. lia. }
    iIntros "!> (HPC & Hct2 & Hct1 & Hhwm & _ & Hzero)".
    assert ((a_block ^+ 19%nat) ^+ length (clear_stack_instrs ct2 ct1)
            = a_block ^+ 23%nat) as Hpc_csrw by (cbn; solve_addr).
    iEval (rewrite Hpc_csrw) in "HPC".
    (* SpecialRW cnull MSHWM (inr csp) *)
    iInstrApply "Hcode_csrw" (wp_csrw_mshwm_zeroed _ _ _ _ _ _ _ _ _ _ _ mshwmb_v va va a)
      with "[$HPC $Hcsp $Hhwm $Hzero]" as "Hres".
    { done. }
    { solve_addr. }
    { by left. }
    { lia. }
    iDestruct "Hres" as "(HPC & Hcsp & Hhwm & Hzero)".
    zero_frame_dead_zeros mie Hdom.
    iDestruct (stack_region_zeroed_from_cells b va a with "[$Hlo $Hzero]") as "Hfree";
      [solve_addr | solve_addr | rewrite length_app /= -Hlen_stk /finz.dist; solve_addr |].
    rewrite (stack_zeroed_from_app b (a ^- 4)); last (rewrite -Hlen_stk /finz.dist; solve_addr).
    iDestruct (stack_region_app_inv b (a ^- 4) a with "Hfree") as "[Hstk Hcells]";
      [solve_addr | solve_addr | by rewrite stack_zeroed_from_length -Hlen_stk |].
    iApply ("Hpost" $! rmap' with "[%] [-]"); [solve_addr |].
    rewrite (_ : (a ^- 4) ^+ 4 = a); last solve_addr.
    iFrame "∗ %".
  Qed.

End Switcher_Zero_Callee_Frame.
