From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel call_stack switcher_preamble switcher_registers.
From griotte.switcher.callback Require Export
  switcher_after_compartment_call switcher_zero_callee_frame.
From griotte.switcher.failure Require Export common_thread_exit.

(** * Return routine of the switcher: paths

    The compositions of the blocks of the return routine, from its entry
    point [switcher_after_compartment_call] to each of its exits:
    - when the frame to pop is the entry frame, the thread exits
      ([switcher_return_exit_path_spec]);
    - otherwise, the switcher pops the topmost frame, restores the
      callee-save registers of the caller, clears its stack frame and the
      registers, and jumps back to the caller, which faults when the return
      address is not a valid target. The restored registers are loaded
      either from the memory ([switcher_return_path_spec]) or through an
      open world ([switcher_return_path_world_spec]). In the latter, the
      spill area comes from a logical step between the pop and the
      restore, which may use the later credit of the pop.

    The paths take the registers as the callee-save registers, the stack
    pointer, and the register file without them and the return values. *)

Section Callback_Path.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [switcher_after_compartment_call], when the frame to pop is the
      entry frame: the thread exits. *)
  Lemma switcher_return_exit_path_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (rmap : LReg) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    dom rmap = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
    regs[th] rmap ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
    switcher_hazard ∗
    switcher_code ∗
    ▷ ( mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
        switcher_hazard
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Exec @[th] E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros (Hdom) "(HPC & Hrmap & Hmtdc & Hframeoffset & Hhazard & #Hswitcher & Hpost)".
    iDestruct (ret_regs_extract with "Hrmap")
      as "([%wctp Hctp] & [%wct0 Hct0] & _ & [%wct2 Hct2] & _)"; first done.
    iApply (switcher_after_compartment_call_exit_spec with
      "[- $HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hhazard $Hswitcher]").
    iIntros "!>" (g_tstk) "(HPC & _ & _ & _ & Hmtdc & Hframeoffset & Hhazard)".
    iApply (common_defer_irqs_and_thread_exit_spec with
      "[$HPC $Hswitcher Hpost Hmtdc Hframeoffset Hhazard]").
    iIntros "!> _".
    iApply ("Hpost" with "[$Hmtdc $Hframeoffset $Hhazard]").
  Qed.

  (** From [switcher_after_compartment_call], with [S d] frames above the
      entry frame: pop the topmost frame, at [a_tstk], whose stack pointer
      is the one of the caller, with the cursor [a]; restore the
      callee-save registers from the spill area by loads from the memory;
      clear the stack frame and the registers; and jump back to the
      caller. The spill area may come under a later, which the pop
      removes. The continuation has two exits: the jump, and its fault
      when the return address is not a valid target. *)
  Lemma switcher_return_path_spec
    (d : nat) (a_tstk b e a : Addr) (stk_mem : list LWord)
    (wcs0' wcs1' wcgp' wcra' : LWord)
    (wcsp wcgp wcra wcs0 wcs1 : LWord) (rmap : LReg) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp) in
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    dom rmap = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
    csp ↦ᵣ[th] wcsp ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    regs[th] rmap ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    switcher_hazard ∗
    a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
    ▷ switcher_stk_cells (stk_spill_a a) wcs0' wcs1' wcgp' wcra' ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs1 rcs0,
        ⌜ load_heap wcgp' rcgp ∧ load_heap wcra' rcra ∧
          load_heap wcs1' rcs1 ∧ load_heap wcs0' rcs0 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        switcher_hazard ∗
        a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
        cra ↦ᵣ[th] rcra ∗
        cgp ↦ᵣ[th] rcgp ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        csp ↦ᵣ[th] Cap RWL Local b e a ∗
        [[ stk_spill_a a , stk_spill_a a ^+ SpillSlot_size ]] ↦ₐ [[ 0…0 ]] ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ 0…0 ]] ∗
        regs₀[th] rmap' -∗
        ( PC ↦ₚ[th] lupdatePcPerm rcra ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    iIntros (Ha_tstk Ha_tstk_e Hbounds Hstk_mmio Hstk_heap Hdom)
      "(HPC & Hcsp & Hcgp & Hcra & Hcs0 & Hcs1 & Hrmap & Hmtdc & Hframeoffset & Hhazard & Ha_csp
      & Hcells & Hstk & #Hswitcher & Hpost)".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    assert (is_heap_address b = false) as Hb_heap.
    { eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      clear -Hba3; rewrite /withinBounds; solve_addr. }
    assert (stk_spill_a a ^+ SpillSlot_size = a) as Hspill_top
      by (clear -Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size))
      as Hspill4 by (clear -Ha4; stk_unfold; solve_addr).
    iDestruct (ret_regs_extract with "Hrmap")
      as "([%wctp Hctp] & [%wct0 Hct0] & [%wct1 Hct1] & [%wct2 Hct2] & [%wca2 Hca2]
          & %rmap0 & %Hdom0 & Hrmap)"; first done.
    (* [switcher_after_compartment_call]: pop the topmost frame *)
    iApply (switcher_after_compartment_call_spec with
      "[- $HPC $Hctp $Hct0 $Hct1 $Hct2 $Hcsp $Hmtdc $Hframeoffset $Hhazard $Ha_csp $Hswitcher]");
      [done|done|done|].
    iNext; iIntros (g_tstk) "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Hhazard & Ha_csp
                    & _)".
    (* [.Lswitch_callee_save_restore]: restore the callee-save registers *)
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_restore_spill_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hcsp $Hcells $Hswitcher]");
      [done|done|done|clear -Hba3; stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp & Hcells & _)".
    iEval (rewrite Hspill_top) in "Hcsp".
    (* [.Lswitch_callee_stack_zero]: clear the frame and the registers,
       and return *)
    iApply (switcher_zero_callee_frame_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap $Hswitcher]"); [done|done|done|].
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0 with
      "[$Hmtdc $Hframeoffset $Hhazard $Ha_csp $Hcra $Hcgp $Hcs0 $Hcs1 $Hcsp $Hstk' $Hstk $Hrmap]").
    iPureIntro; split; done.
  Qed.

  (** [switcher_return_path_spec], where the restored registers are loaded
      through the open world [Wworld], and observe the heap of the world
      [Wval]. The spill area, the callee's stack and the open world come
      from a logical step after the pop, which receives the later credit of
      the pop. When the caller is untrusted, the saved words are safe, and
      so are the restored registers. *)
  Lemma switcher_return_path_world_spec
    Wworld Wval C (ccrel : caller_callee_relation)
    (d : nat) (a_tstk b e a : Addr)
    (wcsp wcgp wcra wcs0 wcs1 : LWord) (rmap : LReg) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp) in
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    dom rmap = all_registers_s ∖ {[ csp ; cgp ; cra ; cs0 ; cs1 ; ca0 ; ca1 ]} ->

    PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
    csp ↦ᵣ[th] wcsp ∗
    cgp ↦ᵣ[th] wcgp ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    regs[th] rmap ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    switcher_hazard ∗
    a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
    switcher_code ∗
    ▷ ( mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        switcher_hazard ∗
        a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
        £ 1
        ={⊤}=∗
        ∃ opened (wcs0' wcs1' wcgp' wcra' : LWord) (stk_mem : list LWord),
        switcher_stk_cells (stk_spill_a a) wcs0' wcs1' wcgp' wcra' ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
        world_interp_open Wworld C opened ∗
        (if is_untrusted_caller ccrel then
           interp_in_mem RWL Wval C wcgp' ∗
           interp_in_mem RWL Wval C wcra' ∗
           interp_in_mem RWL Wval C wcs1' ∗
           interp_in_mem RWL Wval C wcs0'
         else True) ∗
        ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs1 rcs0,
          ⌜ load_heap_in_world Wval wcgp' rcgp ∧ load_heap_in_world Wval wcra' rcra ∧
            load_heap_in_world Wval wcs1' rcs1 ∧ load_heap_in_world Wval wcs0' rcs0 ⌝ ∗
          world_interp_open Wworld C opened ∗
          (if is_untrusted_caller ccrel then
             interp Wval C rcgp ∗
             interp Wval C rcra ∗
             interp Wval C rcs1 ∗
             interp Wval C rcs0
           else True) ∗
          ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
          cra ↦ᵣ[th] rcra ∗
          cgp ↦ᵣ[th] rcgp ∗
          cs0 ↦ᵣ[th] rcs0 ∗
          cs1 ↦ᵣ[th] rcs1 ∗
          csp ↦ᵣ[th] Cap RWL Local b e a ∗
          [[ stk_spill_a a , stk_spill_a a ^+ SpillSlot_size ]] ↦ₐ [[ 0…0 ]] ∗
          [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ 0…0 ]] ∗
          regs₀[th] rmap' ∗
          £ 2 -∗
          ( PC ↦ₚ[th] lupdatePcPerm rcra ∗
            £ 1 -∗
            safe[th] ) ∧
          ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
            trap_safe (switcher_label_pc ".Lswitch_just_return") ⊤
              (HO th) ) ) )
    ⊢ safe[th].
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    iIntros (Ha_tstk Ha_tstk_e Hbounds Hstk_mmio Hstk_heap Hdom)
      "(HPC & Hcsp & Hcgp & Hcra & Hcs0 & Hcs1 & Hrmap & Hmtdc & Hframeoffset & Hhazard & Ha_csp
      & #Hswitcher & Hmid)".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    assert (is_heap_address b = false) as Hb_heap.
    { eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      clear -Hba3; rewrite /withinBounds; solve_addr. }
    assert (stk_spill_a a ^+ SpillSlot_size = a) as Hspill_top
      by (clear -Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size))
      as Hspill4 by (clear -Ha4; stk_unfold; solve_addr).
    iDestruct (ret_regs_extract with "Hrmap")
      as "([%wctp Hctp] & [%wct0 Hct0] & [%wct1 Hct1] & [%wct2 Hct2] & [%wca2 Hca2]
          & %rmap0 & %Hdom0 & Hrmap)"; first done.
    (* [switcher_after_compartment_call]: pop the topmost frame *)
    iApply (switcher_after_compartment_call_spec with
      "[- $HPC $Hctp $Hct0 $Hct1 $Hct2 $Hcsp $Hmtdc $Hframeoffset $Hhazard $Ha_csp $Hswitcher]");
      [done|done|done|].
    iNext; iIntros (g_tstk) "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Hhazard & Ha_csp
                    & Hlc)".
    (* The logical step: the spill area, the callee's stack, the open world *)
    iMod ("Hmid" with "[$Hmtdc $Hframeoffset $Hhazard $Ha_csp $Hlc]")
      as (opened wcs0' wcs1' wcgp' wcra' stk_mem) "(Hcells & Hstk & Hworld & Hmem & Hpost)".
    (* [.Lswitch_callee_save_restore]: restore the callee-save registers *)
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_restore_spill_world_spec Wworld Wval C opened ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hcsp $Hcells $Hworld $Hmem
        $Hswitcher]");
      [done|done|done|clear -Hba3; stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(Hworld & Hinterps & HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp & Hcells & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp".
    (* [.Lswitch_callee_stack_zero]: clear the frame and the registers,
       and return *)
    iApply (switcher_zero_callee_frame_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap $Hswitcher]"); [done|done|done|].
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0 with
      "[$Hworld $Hinterps $Hcra $Hcgp $Hcs0 $Hcs1 $Hcsp $Hstk' $Hstk $Hrmap $Hlc]").
    iPureIntro; split; done.
  Qed.

End Callback_Path.
