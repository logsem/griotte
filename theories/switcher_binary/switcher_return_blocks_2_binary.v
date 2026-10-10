From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary.
From griotte Require Import switcher_return_states_binary switcher_blocks_14_15_binary.

(** * Return routine, end of block 12 and blocks 13-15, binary model

    The end of block 12 restores the callee-save registers of each run from
    its own copy of the caller's stack frame, block 13 clears the stack
    frame, and blocks 14-15 clear the registers and jump back to the
    caller. *)

Section Switcher_Return_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_return_block_12_restore_spec
    pc_a
    b_stk e_stk a_stk a_stk4
    wcgp swcgp wcra swcra wcs1 swcs1 wcs0 swcs0
    wcgp_old swcgp_old wcra_old swcra_old wcs1_old swcs1_old wcs0_old swcs0_old
    wct0 swct0 wct1 swct1 :
    let switcher_instrs_12 := switcher_instrs_n 12 in
    let len_switcher_12 := length switcher_instrs_12 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ len_switcher_12)%a ->
    (a_stk + 4)%a = Some a_stk4 ->
    (b_stk <= a_stk)%a ->
    (a_stk ^+ 3 < e_stk)%a ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 5)%a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 5)%a ∗
    cgp ↦ᵣ wcgp_old ∗
    cgp ↣ᵣ swcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cra ↣ᵣ swcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs1 ↣ᵣ swcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    cs0 ↣ᵣ swcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk (a_stk ^+ 3)%a ∗
    switcher_stk_cells a_stk wcs0 wcs1 wcra wcgp ∗
    switcher_stk_cells_spec a_stk swcs0 swcs1 swcra swcgp ∗
    codefrag pc_a switcher_instrs_12 ∗
    spec_codefrag pc_a switcher_instrs_12 ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 14)%a ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ 14)%a ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        cs0 ↦ᵣ wcs0 ∗
        cs0 ↣ᵣ swcs0 ∗
        ct0 ↦ᵣ WInt e_stk ∗
        ct0 ↣ᵣ WInt e_stk ∗
        ct1 ↦ᵣ WInt a_stk ∗
        ct1 ↣ᵣ WInt a_stk ∗
        csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk ∗
        switcher_stk_cells a_stk wcs0 wcs1 wcra wcgp ∗
        switcher_stk_cells_spec a_stk swcs0 swcs1 swcra swcgp ∗
        codefrag pc_a switcher_instrs_12 ∗
        spec_codefrag pc_a switcher_instrs_12 ∗
        £ 2 -∗
        switcher_wp
      )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_12 len_switcher_12.
    subst switcher_instrs_12 len_switcher_12.
    iIntros (Hsub_reg Ha_stk4 Hb_a4 He_a1)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs1 & Hscs1 & Hcs0 & Hscs0
      & Hct0 & Hsct0 & Hct1 & Hsct1 & Hcsp & Hscsp
      & (Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3) & (Hsa_stk & Hsa_stk1 & Hsa_stk2 & Hsa_stk3)
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* Load cgp csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1].
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4.
    (* Load cra csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1].
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4.
    (* Load cs1 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1].
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some a_stk); solve_addr.
    (* Load cs0 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split; [solve_pure|rewrite le_addr_withinBounds; solve_addr+Ha_stk4 Hb_a4 He_a1].
    (* GetE ct0 csp *)
    iInstr_spec "Hscode".
    (* GetE ct0 csp *)
    iInstr "Hcode" with "Hlc".
    (* GetA ct1 csp *)
    iInstr_spec "Hscode".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc'".

    iCombine "Hlc Hlc'" as "Hlc".
    iApply "Hpost"; iFrame.
  Qed.


  (** End of block 12 and blocks 13-15: restore the callee-save registers
      from the caller's stack frame [[a, e)], clear it, clear the registers
      and jump back to the caller. *)
  Lemma switcher_return_blocks_2_spec
    (b e a : Addr) (stk_mem stk_mem_spec : list Word)
    (wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp : Word)
    (wcgp_old swcgp_old wcra_old swcra_old wcs1_old swcs1_old wcs0_old swcs0_old : Word)
    (wct0 swct0 wct1 swct1 wca2 swca2 wctp swctp : Word)
    (rmap smap : Reg) :
    switcher_stk_bounds b e a ->
    dom rmap = all_registers_s ∖
                 {[ PC ; csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->
    dom smap = all_registers_s ∖
                 {[ PC ; csp ; ca0 ; ca1 ; cra ; cgp ; ctp ; ca2 ; cs1 ; cs0 ; ct0 ; ct1 ]} ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
    PC ↣ᵣ switcher_pc (switcher_block_offset 12 + 5) ∗
    cgp ↦ᵣ wcgp_old ∗
    cgp ↣ᵣ swcgp_old ∗
    cra ↦ᵣ wcra_old ∗
    cra ↣ᵣ swcra_old ∗
    cs1 ↦ᵣ wcs1_old ∗
    cs1 ↣ᵣ swcs1_old ∗
    cs0 ↦ᵣ wcs0_old ∗
    cs0 ↣ᵣ swcs0_old ∗
    ct0 ↦ᵣ wct0 ∗
    ct0 ↣ᵣ swct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct1 ↣ᵣ swct1 ∗
    ca2 ↦ᵣ wca2 ∗
    ca2 ↣ᵣ swca2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    csp ↦ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
    csp ↣ᵣ WCap RWL Local b e (a ^+ 3)%a ∗
    switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
    switcher_stk_cells_spec a swcs0 swcs1 swcra swcgp ∗
    [[ (a ^+ 4)%a , e ]] ↦ₐ [[ stk_mem ]] ∗
    [[ (a ^+ 4)%a , e ]] ↣ₐ [[ stk_mem_spec ]] ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ smap, r ↣ᵣ w ) ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ∀ (rmap' : Reg),
        ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} ⌝ ∗
        ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        PC ↣ᵣ updatePcPerm swcra ∗
        cra ↦ᵣ wcra ∗
        cra ↣ᵣ swcra ∗
        cgp ↦ᵣ wcgp ∗
        cgp ↣ᵣ swcgp ∗
        cs0 ↦ᵣ wcs0 ∗
        cs0 ↣ᵣ swcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cs1 ↣ᵣ swcs1 ∗
        csp ↦ᵣ WCap RWL Local b e a ∗
        csp ↣ᵣ WCap RWL Local b e a ∗
        [[ a , (a ^+ 4)%a ]] ↦ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ a , (a ^+ 4)%a ]] ↣ₐ [[ region_addrs_zeroes a (a ^+ 4)%a ]] ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        [[ (a ^+ 4)%a , e ]] ↣ₐ [[ region_addrs_zeroes (a ^+ 4)%a e ]] ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) ∗
        switcher_code ∗
        switcher_spec_code ∗
        £ 3 -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hdom Hsdom)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs1 & Hscs1 & Hcs0 & Hscs0
      & Hct0 & Hsct0 & Hct1 & Hsct1 & Hca2 & Hsca2 & Hctp & Hsctp & Hcsp & Hscsp
      & Hcells & Hscells & Hstk & Hsstk & Hrmap & Hsmap & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 12: restore the callee-save registers *)
    switcher_focus_block_lockstep 12 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    change_pc_to ((a_switcher_call ^+ switcher_block_offset 12) ^+ 5)%a.
    iApply (switcher_return_block_12_restore_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcs1 $Hscs1 $Hcs0 $Hscs0
        $Hct0 $Hsct0 $Hct1 $Hsct1 $Hcsp $Hscsp $Hcells $Hscells $Hcode $Hscode]");
      [done|done|done|solve_addr|].
    iNext; iIntros
      "(Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs1 & Hscs1 & Hcs0 & Hscs0
        & Hct0 & Hsct0 & Hct1 & Hsct1 & Hcsp & Hscsp & Hcells & Hscells & Hcode & Hscode & Hlc)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Block 13: clear the stack frame *)
    switcher_focus_block_lockstep 13 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iDestruct (switcher_stk_cells_region with "Hcells Hstk") as "Hstk"; [done|solve_addr|].
    iDestruct (switcher_stk_cells_region_spec with "Hscells Hsstk") as "Hsstk"; [done|solve_addr|].
    iApply (clear_stack_spec with
      "[ - $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct0 $Hct1 $Hsct0 $Hsct1 $Hcode $Hscode $Hstk $Hsstk]");
      [done|done|solve_addr|solve_addr|done|done|].
    iNext; iIntros "(Hj & HPC & HsPC & Hcsp & Hscsp & Hct0 & Hct1 & Hsct0 & Hsct1 & Hcode & Hscode
      & Hstk & Hsstk)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Blocks 14-15 *)
    iInsertList "Hrmap" [ctp;ca2;ct0;ct1].
    iInsertListSpec "Hsmap" [ctp;ca2;ct0;ct1].
    switcher_change_pc (switcher_block_offset 14).
    iApply (switcher_blocks_14_15_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcra $Hscra $Hrmap $Hsmap]").
    { rewrite !dom_insert_L Hdom. set_solver. }
    { rewrite !dom_insert_L Hsdom. set_solver. }
    iSplitL "Hcode"; first iExact "Hcode".
    iSplitL "Hscode"; first iExact "Hscode".
    iNext; iIntros (rmap') "(%Hrmap' & Hj & HPC & HsPC & Hcra & Hscra & Hrmap & Hcode & Hscode & Hlc')".
    rewrite (region_addrs_zeroes_split a (a ^+ 4)%a e); last solve_addr.
    iDestruct (region_pointsto_split a e (a ^+ 4)%a with "Hstk") as "[Hstk' Hstk]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iDestruct (spec_region_pointsto_split a e (a ^+ 4)%a with "Hsstk") as "[Hsstk' Hsstk]";
      [solve_addr | by rewrite /region_addrs_zeroes length_replicate |].
    iCombine "Hlc Hlc'" as "Hlc".
    iApply ("Hpost" $! rmap'); iFrame "∗ %".
  Qed.

End Switcher_Return_Blocks_2.
