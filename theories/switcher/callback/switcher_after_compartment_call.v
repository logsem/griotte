From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel call_stack switcher_preamble switcher_load_spec.

(** * Callback: pop the trusted stack and restore the caller's registers

    [switcher_after_compartment_call], the return entry point, reads
    [frameoffset] in the trusted stack. When the frame to pop is the entry
    frame of the thread, the thread exits
    ([.Lcommon_defer_irqs_and_thread_exit]). Otherwise, it reads the
    topmost frame, which contains the stack pointer of the caller, and pops
    it. [.Lswitcher_restore_spill] restores the callee-save registers of
    the caller from its spill area, moves the cursor past it, and sets
    [ct2] to the stack with its cursor at the base, for the zeroing at
    [.Lswitcher_zero_callee_frame]. Each restored register is the result of
    a load, which may clear the tag of a saved heap capability. *)

(** Rewrite the PC in [h], at the label [s] inside the block of the
    switcher that starts with the label [sb], to the address
    [a_block ^+ k] of the block [a_block] where [iInstr] looks for the
    instruction. *)
#[local] Ltac switcher_pc_in_block sb s h :=
  let k := eval vm_compute in (switcher_label_offset s - switcher_label_offset sb)%Z in
  let Heq := fresh "Heq_pc" in
  assert ((a_switcher_call ^+ switcher_label_offset s)%a =
          ((a_switcher_call ^+ switcher_label_offset sb) ^+ k)%a) as Heq
    by switcher_addr_eq;
  iEval (rewrite Heq) in h; clear Heq.

Section Switcher_After_Compartment_Call.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [switcher_after_compartment_call], with [S d] frames above the
      entry frame: pop the topmost frame, at [a_tstk], which contains the
      stack pointer [WCap true RWL Local b e (stk_saved_a a)] of the caller,
      and decrement [frameoffset]. *)
  Lemma switcher_after_compartment_call_spec
    (d : nat) (a_tstk b e a : Addr) (wctp wct0 wct1 wct2 wcsp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    is_heap_address b = false ->

    PC ↦ₚ switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ wcsp ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct0 ↦ᵣ WInt 1 ∗
        ct1 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
        ct2 ↦ᵣ WInt (tstack_frame_offset (S d)) ∗
        csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    iIntros (Ha_tstk Ha_tstk_e Hb_heap)
      "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Ha_tstk
      & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).
    assert (is_heap_cap (WCap true RWL Local b e (stk_saved_a a)) = false) as Hstk_nonheap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb_heap //. }
    iEval (rewrite /TrustedStackFrame_offset_csp finz_add_0_default) in "Ha_tstk Hpost".
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode".
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
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
    (* Lt ct0 ct0 ct2 *)
    iInstr "Hcode".
    replace (tstack_frameoffset (S d) + _)%Z with (tstack_frame_offset (S d))
      by (tstack_unfold; lia).
    destruct (_ <? tstack_frame_offset (S d))%Z eqn:Hnonempty; iEval (cbn) in "Hct0";
      destruct (decide (ct0 = cnull)) as [Hct0_null|_] in Hnonempty; [done| |done|].
    2: { exfalso. apply Z.ltb_ge in Hnonempty. tstack_unfold. lia. }
    (* Jne 2 ct0 0 *)
    iInstr "Hcode".
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
    switcher_change_pc_label ".Lswitcher_restore_spill".
    iApply "Hpost".
    iFrame "HPC Hctp Hct0 Hct1 Hct2 Hcsp Hmtdc Hframeoffset Ha_tstk Hlc".
  Qed.

  (** From [switcher_after_compartment_call], when the frame to pop is the
      entry frame: the PC is at [.Lcommon_defer_irqs_and_thread_exit]. *)
  Lemma switcher_after_compartment_call_exit_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (wctp wct0 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    PC ↦ₚ switcher_label_pc "switcher_after_compartment_call" ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt (tstack_frame_offset 0) ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) -∗
        WP Seq (Instr Executable) @ E {{ Φ }} )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros "(HPC & Hctp & Hct0 & Hct2 & Hmtdc & Hframeoffset & #Hswitcher & Hpost)".
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode".
    (* ReadSR ctp mtdc *)
    iInstr "Hcode".
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
    (* Lt ct0 ct0 ct2 *)
    iInstr "Hcode".
    replace (tstack_frameoffset 0 + _)%Z with (tstack_frame_offset 0)
      by (tstack_unfold; lia).
    destruct (_ <? tstack_frame_offset 0)%Z eqn:Hnonempty; iEval (cbn) in "Hct0";
      destruct (decide (ct0 = cnull)) as [Hct0_null|_] in Hnonempty; [done| |done|].
    { exfalso. apply Z.ltb_lt in Hnonempty. tstack_unfold. lia. }
    (* Jne 2 ct0 0 *)
    iInstr "Hcode".
    (* Jmp .Lcommon_defer_irqs_and_thread_exit *)
    iInstr "Hcode".
    { switcher_jump_label ".Lcommon_defer_irqs_and_thread_exit". }
    iApply "Hpost".
    iFrame "HPC Hctp Hct0 Hct2 Hmtdc Hframeoffset".
  Qed.

  (** From [.Lswitcher_restore_spill]: reload the callee-save registers from
      the spill area at the cursor [a_stk], move the cursor past it, and
      set [ct2] to the stack with its cursor at the base, for the
      zeroing. *)
  Lemma switcher_restore_spill_spec
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 : LWord) :
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap wcgp rcgp ∧
          load_heap wcra rcra ∧
          load_heap wcs1 rcs1 ∧
          load_heap wcs0 rcs0⌝ -∗
        PC ↦ₚ switcher_label_pc ".Lswitcher_zero_callee_frame" ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode".
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitcher_restore_spill" "HPC".
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
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode" with "Hlc'".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitcher_zero_callee_frame".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "HPC Hcgp Hcra Hcs1 Hcs0 Hctp Hct1 Hct2 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

  (** [switcher_restore_spill_spec] where the loads observe the heap of the
      world [Wval], through the open world [Wworld], from saved words that
      are safe in [Wval]: the restored registers are safe. *)
  #[local] Lemma switcher_restore_spill_interp_spec
    Wworld Wval C opened
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 : LWord) :
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
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
        PC ↦ₚ switcher_label_pc ".Lswitcher_zero_callee_frame" ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hheap_eq Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & #Hnormal_gp & #Hnormal_ra
      & #Hnormal_s1 & #Hnormal_s0 & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode".
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitcher_restore_spill" "HPC".
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
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ _
      cgp csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld $Hnormal_gp]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld & #Hactual_gp)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode" with "Hlc'".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitcher_zero_callee_frame".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "Hworld Hactual_gp Hactual_ra Hactual_s1 Hactual_s0".
    iFrame "HPC Hcgp Hcra Hcs1 Hcs0 Hctp Hct1 Hct2 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

  (** [switcher_restore_spill_spec] where the loads observe the heap of the
      world [Wval], through the open world [Wworld]. When the caller is
      untrusted, the saved words are safe, and so are the restored
      registers. *)
  Lemma switcher_restore_spill_world_spec
    Wworld Wval C opened (ccrel : caller_callee_relation)
    (b_stk e_stk a_stk : Addr)
    (wcgp wcra wcs1 wcs0 wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 : LWord) :
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_restore_spill" ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
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
        PC ↦ₚ switcher_label_pc ".Lswitcher_zero_callee_frame" ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    destruct (is_untrusted_caller ccrel) eqn:Huntrusted.
    { iIntros (Hheap_eq Hstk_mmio Ha_stk4 Hb_a He_a3)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp & Hcells & Hworld
        & (Hnormal_gp & Hnormal_ra & Hnormal_s1 & Hnormal_s0) & #Hswitcher & Hpost)".
      iApply (switcher_restore_spill_interp_spec Wworld Wval C opened
        with "[$HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp $Hcells $Hworld
        $Hnormal_gp $Hnormal_ra $Hnormal_s1 $Hnormal_s0 $Hswitcher $Hpost]"); done. }
    iIntros (Hheap_eq Hstk_mmio Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & _ & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.
    switcher_open_label "switcher_after_compartment_call" "Hswitcher" as "Hcode".
    switcher_pc_in_block "switcher_after_compartment_call" ".Lswitcher_restore_spill" "HPC".
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
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened _ _ _ _ _ _
      cgp csp _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode" with "Hlc'".
    iCombine "Hlc Hlc'" as "Hlc".
    switcher_change_pc_label ".Lswitcher_zero_callee_frame".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iFrame "Hworld HPC Hcgp Hcra Hcs1 Hcs0 Hctp Hct1 Hct2 Hcsp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3
      Hlc".
  Qed.

End Switcher_After_Compartment_Call.
