From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_return_states switcher_blocks_14_15.

(** * Return routine, end of block 12 and blocks 13-15

    The end of block 12 restores the callee-save registers of the caller,
    block 13 clears the caller's stack frame, and blocks 14-15 clear the
    registers and jump back to the caller ([switcher_blocks_14_15_spec], see
    [switcher_blocks_14_15]). *)

Section Switcher_Return_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_return_block_12_restore_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk a_stk4
    wcgp wcra wcs1 wcs0
    wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 5)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    a_stk ↦ₐ wcs0 ∗
    (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
    (a_stk ^+ 2)%a ↦ₐ wcra ∗
    (a_stk ^+ 3)%a ↦ₐ wcgp ∗
    codefrag pc_a switcher_instrs_12 ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local pc_b pc_e (pc_a ^+ 14)%a ∗
        cgp ↦ᵣ wcgp ∗
        cra ↦ᵣ wcra ∗
        cs1 ↦ᵣ wcs1 ∗
        cs0 ↦ᵣ wcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        a_stk ↦ₐ wcs0 ∗
        (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
        (a_stk ^+ 2)%a ↦ₐ wcra ∗
        (a_stk ^+ 3)%a ↦ₐ wcgp ∗
        codefrag pc_a switcher_instrs_12 ∗
        £ 2 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- Load cgp csp --- *)
    iInstr "Hcode".
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }

    (* --- Load cra csp --- *)
    iInstr "Hcode".
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }

    (* --- Load cs1 csp --- *)
    iInstr "Hcode".
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- Lea csp (-1)%Z --- *)
    iInstr "Hcode".
    { transitivity (Some a_stk); solve_addr. }

    (* --- Load cs0 csp --- *)
    iInstr "Hcode".
    { split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1]. }

    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".

    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iApply "Hpost"; iFrame.
  Qed.




  (** End of block 12 and blocks 13-15: restore the callee-save registers
      from the caller's stack frame [[a, e)], clear it, clear the registers
      and jump back to the caller. *)
  Lemma switcher_return_blocks_2_spec
    (b e a : Addr) (stk_mem : list Word)
    (wcs0 wcs1 wcra wcgp : Word)
    (wcgp_old wcra_old wcs1_old wcs0_old wct0 wct1 wca2 wctp : Word)
    (rmap : Reg) :
    switcher_stk_bounds b e a ->
    dom rmap = all_registers_s ∖
                 {[ PC ; csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    PC ↦ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
    cgp ↦ᵣ wcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ctp ↦ᵣ wctp ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        csp ↦ᵣ WCap RWL Local b e a ∗
        [[ a , (a ^+ 4)%a ]] ↦ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        £ 3 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hdom)
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hca2 & Hctp & Hcsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & Hstk & Hrmap & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 12: restore the callee-save registers *)
    switcher_focus_block 12 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    change_pc_to ((a_switcher_call ^+ switcher_block_offset 12) ^+ 5)%a.
    iApply (switcher_return_block_12_restore_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]"); [done|done|done|solve_addr|].
    iNext; iIntros
      "(HPC & Hcgp & Hcra & Hcs1 & Hcs0 & Hct0 & Hct1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 13: clear the stack frame *)
    switcher_focus_block 13 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iDestruct (switcher_stk_cells_region with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3] Hstk")
      as "Hstk"; [done|solve_addr|].
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]");
      [done|done|solve_addr|solve_addr|done|done|].
    iNext; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Blocks 14-15 *)
    iDestruct (big_sepM_insert_2 with "[Hct1] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct0] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hca2] Hrmap") as "Hrmap";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hctp] Hrmap") as "Hrmap";[iFrame|].
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with "[- $HPC $Hcra $Hrmap]").
    { rewrite !dom_insert_L Hdom. set_solver. }
    iSplitL "Hcode"; first iFrame "Hcode".
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hrmap & Hcode & Hlc')".
    rewrite (region_addrs_zeroes_split a (a ^+ 4)%a e); last solve_addr.
    iDestruct (region_pointsto_split a e (a ^+ 4)%a with "Hstk") as "[Hstk' Hstk]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap'); iFrame "∗ %".
  Qed.

End Switcher_Return_Blocks_2.
