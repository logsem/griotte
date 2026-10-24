From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel call_stack switcher_preamble.
From griotte.switcher.callback Require Export
  switcher_after_compartment_call switcher_zero_callee_frame.
From griotte.switcher.failure Require Export common_thread_exit.

(** * Callback routine of the switcher: paths

    The compositions of the blocks of the callback routine from
    [.Lswitcher_restore_spill] to the return to the caller, and from
    [switcher_after_compartment_call] to the thread exit when there is no
    frame to pop. The pop itself is [switcher_after_compartment_call_spec]. *)

Section Callback_Path.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [switcher_after_compartment_call], when the frame to pop is the
      entry frame: the thread exits. *)
  Lemma switcher_after_compartment_call_exit_path_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (wctp wct0 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    PC ↦ₚ switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
    switcher_code ∗
    ▷ ( mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset 0)
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros "(HPC & Hctp & Hct0 & Hct2 & Hmtdc & Hframeoffset & #Hswitcher & Hpost)".
    iApply (switcher_after_compartment_call_exit_spec with
      "[- $HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hswitcher]").
    iIntros "!> (HPC & _ & _ & _ & Hmtdc & Hframeoffset)".
    iApply (common_defer_irqs_and_thread_exit_spec with "[$HPC $Hswitcher Hpost Hmtdc Hframeoffset]").
    iIntros "!> _".
    iApply ("Hpost" with "[$Hmtdc $Hframeoffset]").
  Qed.

  (** From [.Lswitcher_restore_spill]: restore the callee-save registers
      from the spill area of the caller's stack, clear its free part, clear
      the registers and jump back to the caller. Each restored register is
      the result of a load, which may clear the tag of a saved heap
      capability. *)
  Lemma switcher_restore_spill_path_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 wca2 wctp : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs1 rcs0,
        ⌜ load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs1 rcs1 ∧ load_heap wcs0 rcs0 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ rcra ∗
        cgp ↦ᵣ rcgp ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a ]] ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 2 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hbounds Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & Hrmap & #Hswitcher & Hpost)".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (clear -Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
      as Hspill4 by (clear -Ha4; stk_unfold; solve_addr).
    assert (is_Some (rmap !! ct2)) as [wct2 Hwct2]
      by (apply elem_of_dom; rewrite Hdom; clear; set_solver).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first done.
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_restore_spill_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp $Hcells $Hswitcher]");
      [done|done|done|clear -Hba3; stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp & Hcells & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp Hct1".
    iApply (switcher_zero_callee_frame_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap $Hswitcher]"); [done|done| |].
    { rewrite dom_delete_L Hdom. clear. set_solver. }
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0 with
      "[$Hcra $Hcgp $Hcs0 $Hcs1 $Hcsp $Hstk' $Hstk $Hrmap $Hswitcher $Hlc]").
    iPureIntro; split; done.
  Qed.

  (** Variant of [switcher_restore_spill_path_spec] where the loads observe
      the heap of the world [Wval], through the open world [Wworld]. When
      the caller is untrusted, the restored registers are safe. *)
  Lemma switcher_restore_spill_path_world_spec
    Wworld Wval C opened (ccrel : caller_callee_relation)
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 wca2 wctp : LWord)
    (rmap : LReg) :
    heap_std Wworld = heap_std Wval ->
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_stk_cells (stk_spill_a a) wcs0 wcs1 wcgp wcra ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    world_interp_open Wworld C opened ∗
    (if is_untrusted_caller ccrel then
       interp_in_mem RWL Wval C wcgp ∗
       interp_in_mem RWL Wval C wcra ∗
       interp_in_mem RWL Wval C wcs1 ∗
       interp_in_mem RWL Wval C wcs0
     else True) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg) rcgp rcra rcs1 rcs0,
        ⌜ load_heap_in_world Wval wcgp rcgp ∧ load_heap_in_world Wval wcra rcra ∧
          load_heap_in_world Wval wcs1 rcs1 ∧ load_heap_in_world Wval wcs0 rcs0 ⌝ ∗
        world_interp_open Wworld C opened ∗
        (if is_untrusted_caller ccrel then
           interp Wval C rcgp ∗
           interp Wval C rcra ∗
           interp Wval C rcs1 ∗
           interp Wval C rcs0
         else True) ∗
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ rcra ∗
        cgp ↦ᵣ rcgp ∗
        cs0 ↦ᵣ rcs0 ∗
        cs1 ↦ᵣ rcs1 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ stk_spill_a a , (stk_spill_a a ^+ SpillSlot_size)%a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_spill_a a) (stk_spill_a a ^+ SpillSlot_size)%a ]] ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 2 -∗
        ( PC ↦ₚ lupdatePcPerm rcra ∗
          £ 1 -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜ jalr_target_ok cnull cra rcra.(lw) = false ⌝ -∗
          trap_safe (switcher_label_pc ".Lswitcher_return_to_caller") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hheap Hbounds Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & Hworld & Hmem & Hrmap & #Hswitcher & Hpost)".
    pose proof Hbounds as (Hba & Hba3 & Ha4).
    revert Hba Hba3 Ha4; stk_unfold; intros Hba Hba3 Ha4.
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (clear -Ha4; stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
      as Hspill4 by (clear -Ha4; stk_unfold; solve_addr).
    assert (is_Some (rmap !! ct2)) as [wct2 Hwct2]
      by (apply elem_of_dom; rewrite Hdom; clear; set_solver).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first done.
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_restore_spill_world_spec Wworld Wval C opened ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp $Hcells $Hworld $Hmem
        $Hswitcher]");
      [done|done|done|done|clear -Hba3; stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(Hworld & Hinterps & HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
        & Hcells & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp Hct1".
    iApply (switcher_zero_callee_frame_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap $Hswitcher]"); [done|done| |].
    { rewrite dom_delete_L Hdom. clear. set_solver. }
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0 with
      "[$Hworld $Hinterps $Hcra $Hcgp $Hcs0 $Hcs1 $Hcsp $Hstk' $Hstk $Hrmap $Hswitcher $Hlc]").
    iPureIntro; split; done.
  Qed.

End Callback_Path.
