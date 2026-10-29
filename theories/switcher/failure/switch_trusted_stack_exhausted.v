From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import logrel call_stack switcher_preamble switcher_load_spec.

(** * Failure: the trusted stack is exhausted

    [.Lswitch_trusted_stack_exhausted] is reached when the trusted stack has
    no room for a new frame. It restores the callee-save registers from the
    spill area at the cursor, moves the cursor past it, sets the return
    values [-ENOTENOUGHTRUSTEDSTACK] and 0, and jumps to
    [.Lswitch_callee_dead_zeros], which clears the registers and returns to
    the caller. As on a regular return, each load may clear the tag of a
    saved heap capability. *)

Section Switch_Trusted_Stack_Exhausted.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_trusted_stack_exhausted]: the saved registers are
      restored from the spill area at [a_stk], each one the result of a
      load, and the PC is at [.Lswitch_callee_dead_zeros]. *)
  Lemma switch_trusted_stack_exhausted_spec
    (wcgp wcra wcs0 wcs1 : LWord) (b_stk e_stk a_stk : Addr) :
    disjoint_from_mmio b_stk e_stk ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ[th] wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ[th] wcgp') ∗
    (∃ wcra', cra ↦ᵣ[th] wcra') ∗
    (∃ wca0, ca0 ↦ᵣ[th] wca0) ∗
    (∃ wca1, ca1 ↦ᵣ[th] wca1) ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap wcgp rcgp ∧ load_heap wcra rcra ∧
          load_heap wcs0 rcs0 ∧ load_heap wcs1 rcs1⌝ -∗
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size) ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Hb_a He_a Ha_spill)
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0]
      & [%wca1 Hca1] & Hcsp & (Ha_stk0 & Ha_stk1 & Ha_stk2 & Ha_stk3) & #Hswitcher & Hpost)".
    rewrite /SpillSlot_size in He_a.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)) as Ha3 by solve_addr.
    switcher_open_label ".Lswitch_trusted_stack_exhausted" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 csp SpillSlot_cs0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cs0 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk0]"
      as (rcs0) "(%Hrcs0 & HPC & Hcs0 & Hcsp & Ha_stk0)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp SpillSlot_cs1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cs1 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1]"
      as (rcs1) "(%Hrcs1 & HPC & Hcs1 & Hcsp & Ha_stk1)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp SpillSlot_pcc *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cra csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3]"
      as (rcra) "(%Hrcra & HPC & Hcra & Hcsp & Ha_stk3)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp SpillSlot_cgp *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ _ cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2]"
      as (rcgp) "(%Hrcgp & HPC & Hcgp & Hcsp & Ha_stk2)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode".
    (* Mov ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    (* Mov ca1 0 *)
    iInstr "Hcode" with "Hlc".
    (* Jmp .Lswitch_callee_dead_zeros *)
    iInstr "Hcode".
    { jump_to (a_switcher_call ^+ switcher_label_offset ".Lswitch_callee_dead_zeros")%a
        by switcher_addr_eq. }
    subst hpost.
    iApply ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done.
    iFrame "HPC Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Ha_stk0 Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

  (** Variant of [switch_trusted_stack_exhausted_spec] in a world [W]: each
      restored register retains its authority in [W]. Saved words may become
      stale if their heap addresses are freed during a callback. *)
  Lemma switch_trusted_stack_exhausted_world_spec
    (W : WORLD) (C : CmptName)
    (wcgp wcra wcs0 wcs1 : LWord) (b_stk e_stk a_stk : Addr) :
    disjoint_from_mmio b_stk e_stk ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
    (∃ wcs0', cs0 ↦ᵣ[th] wcs0') ∗
    (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
    (∃ wcgp', cgp ↦ᵣ[th] wcgp') ∗
    (∃ wcra', cra ↦ᵣ[th] wcra') ∗
    (∃ wca0, ca0 ↦ᵣ[th] wca0) ∗
    (∃ wca1, ca1 ↦ᵣ[th] wca1) ∗
    csp ↦ᵣ[th] Cap RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    world_interp W C ∗
    switcher_code ∗
    ▷ ( ∀ rcgp rcra rcs0 rcs1,
        ⌜load_heap_in_world W wcgp rcgp ∧ load_heap_in_world W wcra rcra ∧
          load_heap_in_world W wcs0 rcs0 ∧ load_heap_in_world W wcs1 rcs1⌝ -∗
        world_interp W C ∗
        PC ↦ₚ[th] switcher_label_pc ".Lswitch_callee_dead_zeros" ∗
        cs0 ↦ᵣ[th] rcs0 ∗
        cs1 ↦ᵣ[th] rcs1 ∗
        cgp ↦ᵣ[th] rcgp ∗
        cra ↦ᵣ[th] rcra ∗
        ca0 ↦ᵣ[th] WInt ENOTENOUGHTRUSTEDSTACK ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        csp ↦ᵣ[th] Cap RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size) ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hstk_mmio Hb_a He_a Ha_spill)
      "(HPC & [%wcs0' Hcs0] & [%wcs1' Hcs1] & [%wcgp' Hcgp] & [%wcra' Hcra] & [%wca0 Hca0]
      & [%wca1 Hca1] & Hcsp & (Ha_stk0 & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & #Hswitcher
      & Hpost)".
    rewrite /SpillSlot_size in He_a.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)) as Ha3 by solve_addr.
    iEval (rewrite open_world_interp_empty) in "Hworld".
    switcher_open_label ".Lswitch_trusted_stack_exhausted" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* CLoad cs0 csp SpillSlot_cs0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ _ cs0 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk0 $Hworld]"
      as (rcs0) "(%Hrcs0 & HPC & Hcs0 & Hcsp & Ha_stk0 & Hworld)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp SpillSlot_cs1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ _ cs1 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld]"
      as (rcs1) "(%Hrcs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp SpillSlot_pcc *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ _ cra csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3 $Hworld]"
      as (rcra) "(%Hrcra & HPC & Hcra & Hcsp & Ha_stk3 & Hworld)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp SpillSlot_cgp *)
    iInstrApply "Hcode" (switcher_load_stack_restore_world _ W W C [] _ _ _ _ _ _ cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld]"
      as (rcgp) "(%Hrcgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact Hstk_shadow.
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp SpillSlot_size *)
    iInstr "Hcode".
    (* Mov ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    (* Mov ca1 0 *)
    iInstr "Hcode" with "Hlc".
    (* Jmp .Lswitch_callee_dead_zeros *)
    iInstr "Hcode".
    { jump_to (a_switcher_call ^+ switcher_label_offset ".Lswitch_callee_dead_zeros")%a
        by switcher_addr_eq. }
    iEval (rewrite -open_world_interp_empty) in "Hworld".
    subst hpost.
    iApply ("Hpost" $! rcgp rcra rcs0 rcs1 with "[%]"); first done.
    iFrame "Hworld HPC Hcs0 Hcs1 Hcgp Hcra Hca0 Hca1 Hcsp Ha_stk0 Ha_stk1 Ha_stk2 Ha_stk3 Hlc".
  Qed.

End Switch_Trusted_Stack_Exhausted.
