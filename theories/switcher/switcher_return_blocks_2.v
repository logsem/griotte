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

  Lemma switcher_return_block_13_restore_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 11)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
    ▷ ( ∀ rcgp rcra rcs1 rcs0,
        ⌜load_heap wcgp rcgp ∧ load_heap wcra rcra ∧ load_heap wcs1 rcs1 ∧ load_heap wcs0 rcs0⌝ -∗
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 20)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    subst switcher_instrs_13 len_switcher_13.
    iIntros (Hstk_shadow Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- CLoad cgp csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 12)%a cgp csp
      _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk3]"
      as (rcgp) "(%HPg & HPC & Hcgp & Hcsp & Ha_stk3)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }

    (* --- CLoad cra csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 14)%a cra csp
      _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk2]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk2)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }

    (* --- CLoad cs1 csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 16)%a cs1 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some a_stk); solve_addr+Ha_stk4. }

    (* --- CLoad cs0 csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore _ _ _ _ _ _ (pc_a ^+ 18)%a cs0 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".

    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done. iFrame "∗ Hcode".
  Qed.

  Lemma switcher_return_block_13_restore_interp_spec
    Wworld Wval C opened
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 11)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
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
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 20)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    subst switcher_instrs_13 len_switcher_13.
    iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hworld & #Hnormal_gp & #Hnormal_ra & #Hnormal_s1 & #Hnormal_s0 & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- CLoad cgp csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 12)%a cgp csp
      _ _ _ _ _ _)
      with "[$HPC $Hcgp $Hcsp $Ha_stk3 $Hworld $Hnormal_gp]"
      as (rcgp) "(%HPg & HPC & Hcgp & Hcsp & Ha_stk3 & Hworld & #Hactual_gp)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }

    (* --- CLoad cra csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 14)%a cra csp
      _ _ _ _ _ _)
      with "[$HPC $Hcra $Hcsp $Ha_stk2 $Hworld $Hnormal_ra]"
      as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk2 & Hworld & #Hactual_ra)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }

    (* --- CLoad cs1 csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 16)%a cs1 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld $Hnormal_s1]"
      as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld & #Hactual_s1)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- Lea csp csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some a_stk); solve_addr+Ha_stk4. }

    (* --- CLoad cs0 csp --- *)
    iInstrApply "Hcode" (switcher_load_stack_restore_interp _ Wworld Wval C opened _ _ _ _ _ (pc_a ^+ 18)%a cs0 csp
      _ _ _ _ _ _)
      with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld $Hnormal_s0]"
      as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld & #Hactual_s0)".
    { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
      rewrite /withinBounds; solve_addr. }
    { rewrite /withinBounds; solve_addr. }

    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".

    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iSpecialize ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
    iApply "Hpost". iFrame "∗ Hcode".
    iFrame "Hactual_gp Hactual_ra Hactual_s1 Hactual_s0".
  Qed.

  Lemma switcher_return_block_13_restore_open_cases_spec
    Wworld Wval C opened (ccrel : caller_callee_relation)
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    heap_std Wworld = heap_std Wval ->
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 11)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
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
        PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 20)%a ∗
        cgp ↦ᵣ rcgp ∗
        cra ↦ᵣ rcra ∗
        cs1 ↦ᵣ rcs1 ∗
        cs0 ↦ᵣ rcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_13 len_switcher_13.
    destruct (is_untrusted_caller ccrel) eqn:Huntrusted.
    - iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a4 He_a1)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hworld
        & (Hnormal_gp & Hnormal_ra & Hnormal_s1 & Hnormal_s0)
        & #Hcode & Hpost)".
      iApply (switcher_return_block_13_restore_interp_spec Wworld Wval C opened
        with "[$HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hworld
        $Hnormal_gp $Hnormal_ra $Hnormal_s1 $Hnormal_s0 $Hcode $Hpost]");
        eauto.
    - iIntros (Hheap_eq Hstk_shadow Hsub_reg Ha_stk4 Hb_a4 He_a1)
        "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hworld
        & Hmem & #Hcode & Hpost)".
      iClear "Hmem".
      subst switcher_instrs_13 len_switcher_13.
      codefrag_facts "Hcode". clear H0.
      rewrite /switcher_instrs_n /assembled_switcher_n.

      (* CLoad cgp csp. *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 12)%a cgp csp _ _ _ _ _ _)
        with "[$HPC $Hcgp $Hcsp $Ha_stk3 $Hworld]"
        as (rcgp) "(%HPg & HPC & Hcgp & Hcsp & Ha_stk3 & Hworld)".
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }

      (* Lea csp csp (-1)%Z. *)
      iInstr "Hcode".
      { transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }

      (* CLoad cra csp. *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 14)%a cra csp _ _ _ _ _ _)
        with "[$HPC $Hcra $Hcsp $Ha_stk2 $Hworld]"
        as (rcra) "(%HPra & HPC & Hcra & Hcsp & Ha_stk2 & Hworld)".
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }

      (* Lea csp csp (-1)%Z. *)
      iInstr "Hcode".
      { transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }

      (* CLoad cs1 csp. *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 16)%a cs1 csp _ _ _ _ _ _)
        with "[$HPC $Hcs1 $Hcsp $Ha_stk1 $Hworld]"
        as (rcs1) "(%HPs1 & HPC & Hcs1 & Hcsp & Ha_stk1 & Hworld)".
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }

      (* Lea csp csp (-1)%Z. *)
      iInstr "Hcode".
      { transitivity (Some a_stk); solve_addr+Ha_stk4. }

      (* CLoad cs0 csp. *)
      iInstrApply "Hcode" (switcher_load_stack_restore_world _ Wworld Wval C opened
        _ _ _ _ _ (pc_a ^+ 18)%a cs0 csp _ _ _ _ _ _)
        with "[$HPC $Hcs0 $Hcsp $Ha_stk $Hworld]"
        as (rcs0) "(%HPs0 & HPC & Hcs0 & Hcsp & Ha_stk & Hworld)".
      { eapply disjoint_from_shadow_not_in; first exact (disjoint_from_mmio_shadow _ _ Hstk_shadow).
        rewrite /withinBounds; solve_addr. }
      { rewrite /withinBounds; solve_addr. }

      (* GetE ct0 csp. *)
      iInstr "Hcode" with "Hlc".

      (* GetA ct1 csp. *)
      iInstr "Hcode" with "Hlc'".

      iCombine "Hlc Hlc'" as "Hlc".
      iSpecialize ("Hpost" $! rcgp rcra rcs1 rcs0 with "[%]"); first done.
      iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Blocks 14-16: clear the caller's stack frame [[a, e)], clear the
      registers and jump back to the caller [wcra]. *)
  Lemma switcher_return_blocks_14_16_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp' wcra' wcs1' wcs0' wca2 wctp : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_zero_callee_frame" ∗
    cgp ↦ᵣ wcgp' ∗
    cra ↦ᵣ wcra' ∗
    cs1 ↦ᵣ wcs1' ∗
    cs0 ↦ᵣ wcs0' ∗
    ct0 ↦ᵣ WInt e ∗
    ct1 ↦ᵣ WInt a ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ {[ cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        cra ↦ᵣ wcra' ∗
        cgp ↦ᵣ wcgp' ∗
        cs0 ↦ᵣ wcs0' ∗
        cs1 ↦ᵣ wcs1' ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ a , (a ^+ 4)%a ]] ↦ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
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
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & Hcells & Hstk & Hrmap & #Hswitcher & Hpost)".
    stk_unfold. change (4 - 1)%Z with 3%Z in Hba3.
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 14: clear the stack frame *)
    switcher_focus_block (switcher_block ".Lswitcher_zero_callee_frame") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iDestruct (switcher_stk_cells_region with "Hcells Hstk")
      as "Hstk"; [done|solve_addr|].
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]");
      [done|done|solve_addr|solve_addr| |done|done|].
    { by apply disjoint_from_mmio_shadow. }
    iNext; iIntros "(HPC & Hcsp & Hct0 & Hct1 & _ & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Blocks 15-16 *)
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap";[iFrame|].
    switcher_change_pc (switcher_label_offset ".Lswitch_callee_dead_zeros").
    iApply (switcher_blocks_15_16_spec with "[- $HPC $Hcra $Hrmap]").
    { rewrite !dom_insert_L Hdom. set_solver. }
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hrmap & _)".
    rewrite (region_addrs_zeroes_split a (a ^+ 4)%a e); last solve_addr.
    iDestruct (region_pointsto_split a e (a ^+ 4)%a with "Hstk") as "[Hstk' Hstk]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iApply ("Hpost" $! rmap'); iFrame "∗ % Hswitcher".
  Qed.

  (** End of block 13 and blocks 14-16: restore the callee-save registers
      from the caller's stack frame [[a, e)], clear it, clear the registers
      and jump back to the caller. Each restored register is the result of a
      load, which may clear the tag of a saved heap capability. *)
  Lemma switcher_return_blocks_2_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp : LWord)
    (wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 wca2 wctp : LWord)
    (rmap : LReg) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    dom rmap = all_registers_s ∖
                 {[ csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_restore_cgp") ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e (a ^+ 3)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
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
        [[ a , (a ^+ 4)%a ]] ↦ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
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
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hstk & Hrmap & #Hswitcher & Hpost)".
    stk_unfold. change (4 - 1)%Z with 3%Z in Hba3.
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 13: restore the callee-save registers *)
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call") ^+ 11)%a.
    iApply (switcher_return_block_13_restore_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]"); [done|done|done|done|solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_zero_callee_frame").

    (* Blocks 14-16 *)
    iAssert (switcher_stk_cells a wcs0 wcs1 wcra wcgp)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply (switcher_return_blocks_14_16_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap]"); [done|done|done|].
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

    PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_restore_cgp") ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap true RWL Local b e (a ^+ 3)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
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
        [[ a , (a ^+ 4)%a ]] ↦ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
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
    iIntros (Hheap (Hba & Hba3 & Ha4) Hstk_mmio Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hstk & Hworld & Hmem & Hrmap & #Hswitcher & Hpost)".
    stk_unfold. change (4 - 1)%Z with 3%Z in Hba3.
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 13: restore the callee-save registers *)
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    change_pc_to ((a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call") ^+ 11)%a.
    iApply (switcher_return_block_13_restore_open_cases_spec Wworld Wval C opened ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hworld $Hmem $Hcode]");
      [done|done|done|done|done|solve_addr|].
    iNext; iIntros (rcgp rcra rcs1 rcs0 Hrestored)
      "(Hworld & Hinterps & HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_zero_callee_frame").

    (* Blocks 14-16 *)
    iAssert (switcher_stk_cells a wcs0 wcs1 wcra wcgp)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply (switcher_return_blocks_14_16_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hrmap]"); [done|done|done|].
    iSplitR; first iFrame "Hswitcher".
    iNext; iIntros (rmap') "(%Hrmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & _)".
    iApply ("Hpost" $! rmap' rcgp rcra rcs1 rcs0); iFrame "∗ % Hswitcher".
  Qed.

End Switcher_Return_Blocks_2.
