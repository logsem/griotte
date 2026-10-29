From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel call_stack switcher_preamble switcher_load_spec.
From griotte Require Import clear_hazard_slots_spec switcher_zero_callee_frame.

(** * Callback: pop the trusted stack and restore the caller's registers

    [switcher_after_compartment_call], the return entry point, clears the
    hazard slots of the thread ([clear_hazard_slots_asm]) and reads
    [frameoffset] in the trusted stack. When the frame to pop is the entry
    frame of the thread, the thread exits
    ([.Lcommon_defer_irqs_and_thread_exit]). Otherwise, it reads the
    topmost frame, which contains the stack pointer of the caller, and pops
    it. [.Lswitch_callee_save_restore] restores the callee-save registers of
    the caller from its spill area, and moves the cursor past it. Each restored register is the result of
    a load, which may clear the tag of a saved heap capability. *)

Section Switcher_After_Compartment_Call.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [switcher_after_compartment_call], with [S d] frames above the
      entry frame: pop the topmost frame, at [a_tstk], which contains the
      stack pointer [Cap RWL Local b e (stk_saved_a a)] of the caller,
      and decrement [frameoffset]. *)
  Lemma switcher_after_compartment_call_spec
    (d : nat) (a_tstk b e a : Addr) (wctp wct0 wct1 wct2 wcsp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp) in
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    is_heap_address b = false ->

    PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    csp ↦ᵣ[th] wcsp ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    switcher_hazard ∗
    a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
    switcher_code ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_save_restore" ∗
        ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct0 ↦ᵣ[th] WInt TrustedStack_offset_frames ∗
        ct1 ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack a_tstk ∗
        ct2 ↦ᵣ[th] WInt (tstack_frame_offset (S d)) ∗
        csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
        mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        switcher_hazard ∗
        a_csp ↦ₐ Cap RWL Local b e (stk_saved_a a) ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    iIntros (Ha_tstk Ha_tstk_e Hb_heap)
      "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Hhazard & Ha_tstk
      & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)) as Hfo
      by (tstack_unfold; solve_addr).
    assert (is_heap_cap (Cap RWL Local b e (stk_saved_a a)) = false) as Hstk_nonheap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb_heap //. }
    iEval (rewrite /TrustedStackFrame_offset_csp finz_add_0_default) in "Ha_tstk Hpost".
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_hide "Hpost" as hpost.
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    destruct (mtdc_match_TStack_cap _ _ _ _ _ Hpost_pure) as [g_tstk ->].
    (* clear_hazard_slots_asm ctp ct2 *)
    iDestruct "Hhazard" as "[Hhazard_cell [%ws Hslots]]".
    iDestruct (codefrag_pers_clear_hazard_slots _ _ 1 ctp ct2 with "Hcode") as "Hcode_hz";
      [done | cbn; lia |].
    iEval (rewrite /tstack_hazard_cell /hazard_slots_cap) in "Hhazard_cell".
    iEval (rewrite (_ : a_block ^+ 1%nat = a_block ^+ 1); last done) in "Hcode_hz".
    pose proof hazard_slots_size as Hhz_size.
    pose proof hazard_slots_disjoint_from_shadow as Hhz_shadow.
    pose proof hazard_slots_not_heap as Hhz_heap.
    iApply (clear_hazard_slots_spec with "[- $HPC $Hctp $Hct2 $Hhazard_cell $Hslots $Hcode_hz]");
      try done.
    { rewrite clear_hazard_slots_instrs_length; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /withinBounds /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers. tstk_not_shadow Hts_shadow. }
    iNext; iIntros "(HPC & Hctp & Hct2 & Hhazard_cell & Hslots)".
    iAssert switcher_hazard with "[Hhazard_cell Hslots]" as "Hhazard".
    { rewrite /switcher_hazard /tstack_hazard_cell /hazard_slots_cap.
      iFrame "Hhazard_cell Hslots". }
    rewrite clear_hazard_slots_instrs_length.
    rewrite (_ : (a_block ^+ 1) ^+ 3%nat = a_block ^+ 4); last solve_addr.
    (* CLoad ct2 ctp TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* Mov ct0 TrustedStack_offset_frames *)
    iInstr "Hcode".
    (* Add ct2 ct2 (- TrustedStackFrame_size) *)
    iInstr "Hcode".
    replace (tstack_frameoffset (S d) + _)%Z with (tstack_frame_offset (S d))
      by (tstack_unfold; lia).
    assert (23 < tstack_frame_offset (S d))%Z as Hnonempty by (tstack_unfold; lia).
    destruct (decide (ct0 = cnull)) as [Hct0_null|_]; first done.
    (* Jle .Lcommon_defer_irqs_and_thread_exit ct2 ct0 *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hct2 $Hct0]"
      as "(HPC & Hct2 & Hct0)".
    { cbn; apply Z.leb_gt; lia. }
    (* Lea ct1 ctp ct2 *)
    iInstr "Hcode".
    (* CLoad csp ct1 TrustedStackFrame_offset_csp *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* Store ctp ct2 TrustedStack_offset_frameoffset *)
    iInstr "Hcode" with "Hlc".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    assert (tstack_frame_offset (S d) = tstack_frameoffset d) as Hpopped
      by (tstack_unfold; lia).
    iEval (rewrite Hpopped) in "Hframeoffset".
    switcher_change_pc_label ".Lswitch_callee_save_restore".
    subst hpost.
    iApply ("Hpost" $! g_tstk).
    iFrame "HPC Hctp Hct0 Hct1 Hct2 Hcsp Hmtdc Hframeoffset Hhazard Ha_tstk Hlc".
  Qed.

  (** From [switcher_after_compartment_call], when the frame to pop is the
      entry frame: the PC is at [.Lcommon_defer_irqs_and_thread_exit]. *)
  Lemma switcher_after_compartment_call_exit_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (wctp wct0 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset) in
    PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
    switcher_hazard ∗
    switcher_code ∗
    ▷ ( ∀ g_tstk : Locality,
        PC ↦ₚ[th] switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
        ctp ↦ᵣ[th] Cap RWL g_tstk b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct0 ↦ᵣ[th] WInt TrustedStack_offset_frames ∗
        ct2 ↦ᵣ[th] WInt (tstack_frame_offset 0) ∗
        mtdc ↦ₜ[th] Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
        switcher_hazard -∗
        WP Exec @[th] E {{ Φ }} )
    ⊢ WP Exec @[th] E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros "(HPC & Hctp & Hct0 & Hct2 & Hmtdc & Hframeoffset & Hhazard & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)) as Hfo
      by (tstack_unfold; solve_addr).
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_hide "Hpost" as hpost.
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
    destruct (mtdc_match_TStack_cap _ _ _ _ _ Hpost_pure) as [g_tstk ->].
    (* clear_hazard_slots_asm ctp ct2 *)
    iDestruct "Hhazard" as "[Hhazard_cell [%ws Hslots]]".
    iDestruct (codefrag_pers_clear_hazard_slots _ _ 1 ctp ct2 with "Hcode") as "Hcode_hz";
      [done | cbn; lia |].
    iEval (rewrite /tstack_hazard_cell /hazard_slots_cap) in "Hhazard_cell".
    iEval (rewrite (_ : a_block ^+ 1%nat = a_block ^+ 1); last done) in "Hcode_hz".
    pose proof hazard_slots_size as Hhz_size.
    pose proof hazard_slots_disjoint_from_shadow as Hhz_shadow.
    pose proof hazard_slots_not_heap as Hhz_heap.
    iApply (clear_hazard_slots_spec with "[- $HPC $Hctp $Hct2 $Hhazard_cell $Hslots $Hcode_hz]");
      try done.
    { rewrite clear_hazard_slots_instrs_length; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /withinBounds /TrustedStack_offset_hazardPointers; tstack_unfold; solve_addr. }
    { rewrite /TrustedStack_offset_hazardPointers. tstk_not_shadow Hts_shadow. }
    iNext; iIntros "(HPC & Hctp & Hct2 & Hhazard_cell & Hslots)".
    iAssert switcher_hazard with "[Hhazard_cell Hslots]" as "Hhazard".
    { rewrite /switcher_hazard /tstack_hazard_cell /hazard_slots_cap.
      iFrame "Hhazard_cell Hslots". }
    rewrite clear_hazard_slots_instrs_length.
    rewrite (_ : (a_block ^+ 1) ^+ 3%nat = a_block ^+ 4); last solve_addr.
    (* CLoad ct2 ctp TrustedStack_offset_frameoffset *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.
    (* Mov ct0 TrustedStack_offset_frames *)
    iInstr "Hcode".
    (* Add ct2 ct2 (- TrustedStackFrame_size) *)
    iInstr "Hcode".
    replace (tstack_frameoffset 0 + _)%Z with (tstack_frame_offset 0)
      by (tstack_unfold; lia).
    assert (tstack_frame_offset 0 <= 23)%Z as Hempty by (tstack_unfold; lia).
    destruct (decide (ct0 = cnull)) as [Hct0_null|_]; first done.
    (* Jle .Lcommon_defer_irqs_and_thread_exit ct2 ct0 *)
    iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hct2 $Hct0]"
      as "(HPC & Hct2 & Hct0)".
    { cbn; apply Z.leb_le; lia. }
    { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_defer_irqs_and_thread_exit")%a
        by switcher_addr_eq. }
    subst hpost.
    iApply ("Hpost" $! g_tstk).
    iFrame "HPC Hctp Hct0 Hct2 Hmtdc Hframeoffset Hhazard".
  Qed.

  (** From [.Lswitch_callee_save_restore]: reload the callee-save registers from
      the spill area at the cursor [a_stk], and move the cursor past it. *)
  Lemma switcher_restore_spill_spec
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old : LWord) :
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size) ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_save_restore" ∗
    cgp ↦ᵣ[th] wcgp_old ∗
    cra ↦ᵣ[th] wcra_old ∗
    cs1 ↦ᵣ[th] wcs1_old ∗
    cs0 ↦ᵣ[th] wcs0_old ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap wcgp rcgp ∧
          load_heap wcra rcra ∧
          load_heap wcs1 rcs1 ∧
          load_heap wcs0 rcs0⌝ -∗
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_stack_zero" ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size) ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_save_restore" "HPC".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 csp SpillSlot_cs0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cs0 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp SpillSlot_cs1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cs1 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp SpillSlot_pcc *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cra csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp SpillSlot_cgp *)
    iInstrApply "Hcode" with "Hlc'" (switcher_load_stack_restore _ _ _ _ _ _ _ cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode" with "Hlc".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitch_callee_stack_zero".
    subst hpost.
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "HPC Hcgp Hcra Hcs1 Hcs0 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

  (** [switcher_restore_spill_spec] where the loads observe the heap of the
      world [Wval], through the open world [Wworld], from saved words that
      are safe in [Wval]: the restored registers are safe. *)
  #[local] Lemma switcher_restore_spill_interp_spec
    Wworld Wval C opened
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old : LWord) :
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size) ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_save_restore" ∗
    cgp ↦ᵣ[th] wcgp_old ∗
    cra ↦ᵣ[th] wcra_old ∗
    cs1 ↦ᵣ[th] wcs1_old ∗
    cs0 ↦ᵣ[th] wcs0_old ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    world_interp_open Wworld C opened ∗
    interp_in_mem RWL Wval C wcgp ∗
    interp_in_mem RWL Wval C wcra ∗
    interp_in_mem RWL Wval C wcs1 ∗
    interp_in_mem RWL Wval C wcs0 ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap_in_world Wval wcgp rcgp ∧
          load_heap_in_world Wval wcra rcra ∧
          load_heap_in_world Wval wcs1 rcs1 ∧
          load_heap_in_world Wval wcs0 rcs0⌝ -∗
        world_interp_open Wworld C opened ∗
        (interp Wval C rcgp ∗
         interp Wval C rcra ∗
         interp Wval C rcs1 ∗
         interp Wval C rcs0) ∗
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_stack_zero" ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size) ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & #Hnormal_gp & #Hnormal_ra
      & #Hnormal_s1 & #Hnormal_s0 & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_save_restore" "HPC".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 csp SpillSlot_cs0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ _
      cs0 csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld $Hnormal_s0]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld & #Hactual_s0)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp SpillSlot_cs1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ _
      cs1 csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld $Hnormal_s1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld & #Hactual_s1)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp SpillSlot_pcc *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ _
      cra csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3 $Hworld $Hnormal_ra]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3 & Hworld & #Hactual_ra)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp SpillSlot_cgp *)
    iInstrApply "Hcode" with "Hlc'" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ _
      cgp csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld $Hnormal_gp]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld & #Hactual_gp)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode" with "Hlc".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitch_callee_stack_zero".
    subst hpost.
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "Hworld Hactual_gp Hactual_ra Hactual_s1 Hactual_s0".
    iFrame "HPC Hcgp Hcra Hcs1 Hcs0 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

  (** [switcher_restore_spill_spec] where the loads observe the heap of the
      world [Wval], through the open world [Wworld]. When the caller is
      untrusted, the saved words are safe, and so are the restored
      registers. *)
  Lemma switcher_restore_spill_world_spec
    Wworld Wval C opened (ccrel : caller_callee_relation)
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old : LWord) :
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size) ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_save_restore" ∗
    cgp ↦ᵣ[th] wcgp_old ∗
    cra ↦ᵣ[th] wcra_old ∗
    cs1 ↦ᵣ[th] wcs1_old ∗
    cs0 ↦ᵣ[th] wcs0_old ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    world_interp_open Wworld C opened ∗
    (if is_untrusted_caller ccrel then
       interp_in_mem RWL Wval C wcgp ∗
       interp_in_mem RWL Wval C wcra ∗
       interp_in_mem RWL Wval C wcs1 ∗
       interp_in_mem RWL Wval C wcs0
     else True) ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap_in_world Wval wcgp rcgp ∧
          load_heap_in_world Wval wcra rcra ∧
          load_heap_in_world Wval wcs1 rcs1 ∧
          load_heap_in_world Wval wcs0 rcs0⌝ -∗
        world_interp_open Wworld C opened ∗
        (if is_untrusted_caller ccrel then
           interp Wval C rcgp ∗
           interp Wval C rcra ∗
           interp Wval C rcs1 ∗
           interp Wval C rcs0
         else True) ∗
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_stack_zero" ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size) ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    destruct (is_untrusted_caller ccrel) eqn:Huntrusted.
    { iIntros (Hstk_mmio Ha_stk4 Hb_a He_a3)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp & Hcells & Hworld
        & (Hnormal_gp & Hnormal_ra & Hnormal_s1 & Hnormal_s0) & #Hswitcher & Hpost)".
      iApply (switcher_restore_spill_interp_spec Wworld Wval C opened
        with "[$HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hcsp $Hcells $Hworld
        $Hnormal_gp $Hnormal_ra $Hnormal_s1 $Hnormal_s0 $Hswitcher $Hpost]"); done. }
    iIntros (Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & _ & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode" a_block Heq_block.
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitch_callee_save_restore" "HPC".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 csp SpillSlot_cs0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened _ _ _ _ _ _
      cs0 csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp SpillSlot_cs1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened _ _ _ _ _ _
      cs1 csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp SpillSlot_pcc *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened _ _ _ _ _ _
      cra csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3 $Hworld]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3 & Hworld)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp SpillSlot_cgp *)
    iInstrApply "Hcode" with "Hlc'" (switcher_load_stack_restore_world _ Wworld Wval C opened _ _ _ _ _ _
      cgp csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode" with "Hlc".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitch_callee_stack_zero".
    subst hpost.
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "Hworld HPC Hcgp Hcra Hcs1 Hcs0 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3
      Hlc".
  Qed.

End Switcher_After_Compartment_Call.
