From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics logrel switcher_load_spec.
From griotte Require Import switcher_return_states switcher_blocks_15_16.

(** * Return routine, end of block 13 and blocks 14-16

    The end of block 13 restores the callee-save registers of the caller,
    block 14 clears the caller's stack frame, and blocks 15-16 clear the
    registers and jump back to the caller ([switcher_blocks_15_16_spec], see
    [switcher_blocks_15_16]). *)

Section Switcher_Return_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The end of block 13: reload the callee-save registers from the spill
      area at the cursor [a_stk], move the cursor past it, and set [ct2] to
      the stack with its cursor at the base, for the zeroing. *)
  Lemma switcher_return_block_13_restore_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 10)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap wcgp rcgp ∧
          load_heap wcra rcra ∧
          load_heap wcs1 rcs1 ∧
          load_heap wcs0 rcs0⌝ -∗
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 18)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    subst switcher_instrs_13 len_switcher_13.
    iIntros (Hstk_shadow Hsub_reg Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & #Hcode & Hpost)".
    rewrite /SpillSlot_size in He_a3. change (4 - 1)%Z with 3%Z in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.

    (* CLoad cs0 csp 0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 11)%a cs0 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp 1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 12)%a cs1 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp 3 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 13)%a cra csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp 2 *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 14)%a cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp 4 *)
    iInstr "Hcode".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iAssert (switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done. iFrame "∗ Hcode".
  Qed.

  Lemma switcher_return_block_13_restore_interp_spec
    Wworld Wval C opened
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 10)%a ∗
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
    codefrag_pers pc_a switcher_instrs_13 ∗
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
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 18)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    subst switcher_instrs_13 len_switcher_13.
    iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a He_a3)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hworld & #Hnormal_gp & #Hnormal_ra & #Hnormal_s1 & #Hnormal_s0 & #Hcode & Hpost)".
    rewrite /SpillSlot_size in He_a3. change (4 - 1)%Z with 3%Z in He_a3.
    unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
    assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.

    (* CLoad cs0 csp 0 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 11)%a cs0 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld $Hnormal_s0]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld & #Hactual_s0)".
    { exact Ha0. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cs1 csp 1 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 12)%a cs1 csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld $Hnormal_s1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld & #Hactual_s1)".
    { exact Ha1. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cra csp 3 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 13)%a cra csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk3 $Hworld $Hnormal_ra]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3 & Hworld & #Hactual_ra)".
    { exact Ha3. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* CLoad cgp csp 2 *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 14)%a cgp csp
      _ _ _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld $Hnormal_gp]"
      as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld & #Hactual_gp)".
    { exact Ha2. }
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea csp csp 4 *)
    iInstr "Hcode".
    (* GetB ctp csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc".
    (* SetA ct2 csp ctp *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iAssert (switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iSpecialize ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iApply "Hpost". iFrame "∗ Hcode".
    iFrame "Hactual_gp Hactual_ra Hactual_s1 Hactual_s0".
  Qed.

  Lemma switcher_return_block_13_restore_open_cases_spec
    Wworld Wval C opened (ccrel : caller_callee_relation)
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wctp wct1 wct2 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + SpillSlot_size)%a = Some (a_stk ^+ SpillSlot_size)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ (SpillSlot_size - 1) < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 10)%a ∗
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
    codefrag_pers pc_a switcher_instrs_13 ∗
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
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 18)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ctp ↦ᵣ WInt b_stk ∗
        ct1 ↦ᵣ WInt (a_stk ^+ SpillSlot_size)%a ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk e_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ SpillSlot_size)%a ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra ∗
        codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    destruct (is_untrusted_caller ccrel) eqn:Huntrusted.
    - iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a He_a3)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
        & Hcells & Hworld
        & (Hnormal_gp & Hnormal_ra & Hnormal_s1 & Hnormal_s0)
        & #Hcode & Hpost)".
      iApply (switcher_return_block_13_restore_interp_spec Wworld Wval C opened
        with "[$HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp
        $Hcells $Hworld
        $Hnormal_gp $Hnormal_ra $Hnormal_s1 $Hnormal_s0 $Hcode $Hpost]");
        eauto.
    - subst switcher_instrs_13 len_switcher_13.
      iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a He_a3)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
        & Hcells & Hworld & Hmem & #Hcode & Hpost)".
        iClear "Hmem".
        rewrite /SpillSlot_size in He_a3. change (4 - 1)%Z with 3%Z in He_a3.
        iDestruct "Hcells" as "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3)".
        unfold SpillSlot_cs1, SpillSlot_cgp, SpillSlot_pcc.
      codefrag_facts "Hcode". clear H0.
      rewrite /switcher_instrs_n /assembled_switcher_n.
      assert ((a_stk + 0)%a = Some a_stk) as Ha0 by solve_addr.
      assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Ha1 by solve_addr.
      assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Ha2 by solve_addr.
      assert ((a_stk + 3)%a = Some (a_stk ^+ 3)%a) as Ha3 by solve_addr.

      (* CLoad cs0 csp 0 *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 11)%a cs0 csp _ _ _ _ _ _ _ _)
        with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld]"
        as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld)".
      { exact Ha0. }
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      (* CLoad cs1 csp 1 *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 12)%a cs1 csp _ _ _ _ _ _ _ _)
        with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld]"
        as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld)".
      { exact Ha1. }
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      (* CLoad cra csp 3 *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 13)%a cra csp _ _ _ _ _ _ _ _)
        with "[$HPC $Hcra $Hcsp $Ha_stk3 $Hworld]"
        as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk3 & Hworld)".
      { exact Ha3. }
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      (* CLoad cgp csp 2 *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 14)%a cgp csp _ _ _ _ _ _ _ _)
        with "[$HPC $Hcgp $Hcsp $Ha_stk2 $Hworld]"
        as (rcgp) "(%HPgp & HPC & Hcgp & Hcsp & Ha_stk2 & Hworld)".
      { exact Ha2. }
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      (* Lea csp csp 4 *)
      iInstr "Hcode".
      (* GetB ctp csp *)
      iInstr "Hcode".
      (* GetA ct1 csp *)
      iInstr "Hcode" with "Hlc".
      (* SetA ct2 csp ctp *)
      iInstr "Hcode" with "Hlc'".

      iCombine "Hlc Hlc'" as "Hlc".
      iAssert (switcher_stk_cells a_stk wcs0 wcs1 wcgp wcra)
        with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
      iSpecialize ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
      iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Blocks 14-16: clear the caller's free part, the spill area and the
      callee's stack, from the base of the stack to the cursor [a], clear
      the registers and jump back to the caller [wcra]. *)
  Lemma switcher_return_blocks_14_16_spec
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
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code -∗
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
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 14: clear the stack frame *)
    switcher_focus_block (switcher_block ".Lswitcher_zero_callee_frame") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; first done.
    iApply (clear_stack_spec with "[ - $HPC $Hct2 $Hct1 $Hcode $Hstk]");
      [done|done| | | | |done|done|].
    1-3: revert Hbounds; rewrite /switcher_stk_bounds; stk_unfold; intros (Hba & Hba3 & Ha4);
      solve_addr.
    { by apply disjoint_from_mmio_shadow. }
    iNext; iIntros "(HPC & Hct2 & Hct1 & _ & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 15-16 *)
    iDestruct (big_sepM_insert_2 with "[Hct2] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap";[iFrame|].
    switcher_change_pc (switcher_label_offset ".Lswitch_callee_dead_zeros").
    iApply (switcher_blocks_15_16_spec with "[- $HPC $Hcra $Hrmap]").
    { rewrite !dom_insert_L Hdom. set_solver. }
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap & _)".
    iAssert ([[ stk_free_b b a , stk_free_e e a ]] ↦ₐ
               [[ region_addrs_zeroes (stk_free_b b a) (stk_free_e e a) ]])%I
      with "[Hstk]" as "Hstk"; first done.
    iEval (rewrite (stk_free_split_zeroes _ _ _ Hbounds)) in "Hstk".
    iDestruct (stk_free_split_join with "Hstk") as "[Hstk' Hstk]"; first done.
    { rewrite /region_addrs_zeroes length_replicate.
      revert Hbounds; rewrite /switcher_stk_bounds; stk_unfold; intros (Hba & Hba3 & Ha4).
      rewrite /finz.dist. solve_addr. }
    iApply ("Hpost" $! rmap'); iFrame "∗ % Hswitcher".
  Qed.

  (** End of block 13 and blocks 14-16: restore the callee-save registers
      from the spill area of the caller's stack, clear its free part, clear
      the registers and jump back to the caller. Each restored register is
      the result of a load, which may clear the tag of a saved heap
      capability. *)
  Lemma switcher_return_blocks_2_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 wca2 wctp : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_restore_spill") ∗
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
    revert Hba Hba3 Ha4; stk_unfold; change (4 - 1)%Z with 3%Z; intros Hba Hba3 Ha4.
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
      as Hspill4 by (stk_unfold; solve_addr).
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    assert (is_Some (rmap !! ct2)) as [wct2 Hwct2]
      by (apply elem_of_dom; rewrite Hdom; set_solver-).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first done.
    switcher_unfold_code "Hswitcher".

    (* Block 13: restore the callee-save registers *)
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call") ^+ 10)%a.
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_return_block_13_restore_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp
        $Hcells $Hcode]"); [done|done|done|done|stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
        & Hcells & _ & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp Hct1".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_zero_callee_frame").

    (* Blocks 14-16 *)
    iApply (switcher_return_blocks_14_16_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap]"); [done|done| |].
    { rewrite dom_delete_L Hdom. set_solver. }
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & _)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0); iFrame "∗ % Hswitcher".
  Qed.

  (** Variant of [switcher_return_blocks_2_spec] where the loads observe the
      heap of the world [Wval], through the open world [Wworld]. When the
      caller is untrusted, the restored registers are safe. *)
  Lemma switcher_return_blocks_2_world_spec
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

    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_restore_spill") ∗
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
    revert Hba Hba3 Ha4; stk_unfold; change (4 - 1)%Z with 3%Z; intros Hba Hba3 Ha4.
    assert ((stk_spill_a a ^+ SpillSlot_size)%a = a) as Hspill_top
      by (stk_unfold; solve_addr).
    assert ((stk_spill_a a + SpillSlot_size)%a = Some (stk_spill_a a ^+ SpillSlot_size)%a)
      as Hspill4 by (stk_unfold; solve_addr).
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    assert (is_Some (rmap !! ct2)) as [wct2 Hwct2]
      by (apply elem_of_dom; rewrite Hdom; set_solver-).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first done.
    switcher_unfold_code "Hswitcher".

    (* Block 13: restore the callee-save registers *)
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call") ^+ 10)%a.
    rewrite /stk_saved_a -/(stk_spill_a a).
    iApply (switcher_return_block_13_restore_open_cases_spec Wworld Wval C opened ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hctp $Hct1 $Hct2 $Hcsp
        $Hcells $Hworld $Hmem $Hcode]");
      [done|done|done|done|done|stk_unfold; solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(Hworld & Hinterps & HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hctp & Hct1 & Hct2 & Hcsp
        & Hcells & _ & Hlc)".
    iEval (rewrite Hspill_top) in "Hcsp Hct1".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_zero_callee_frame").

    (* Blocks 14-16 *)
    iApply (switcher_return_blocks_14_16_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hct2 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap]"); [done|done| |].
    { rewrite dom_delete_L Hdom. set_solver. }
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & _)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0); iFrame "∗ % Hswitcher".
  Qed.

End Switcher_Return_Blocks_2.
