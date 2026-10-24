From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import lse_spec_states.

(** * LSE [f], block 4: push the capability of [a], load [a]

    Block 4 restricts [cgp] to the capability of [a] (at [cgp_b]), stores
    it in the top cell of the stack frame, below the cursor, loads [a] in
    [ct0] and [2] in [ct1]. The stack frame holds the pushed capability. *)

Section LSE_F_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_f_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (csp_b csp_e : Addr) (stk_mem : list LWord)
    (wct0 wct1 wcs0 wcs1 : LWord) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    disjoint_from_mmio csp_b csp_e ->
    (* The stack frame holds the pushed capability, below the space reserved
       at the top of the stack *)
    (csp_b + 1 + StackEntry_reserved_space <= csp_e)%Z ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cgp_b ↦ₐ WInt 2 ∗
    [[csp_b, csp_e]] ↦ₐ [[stk_mem]] ∗
    codefrag_pers pc_a lse_main_code ∗
    ▷ (∀ stk_mem' wcs0' wcs1',
        PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f_assert")%a ∗
        cgp ↦ᵣ lse_a_cap cgp_b ∗
        csp ↦ᵣ WCap true RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
        ct0 ↦ᵣ WInt 2 ∗
        ct1 ↦ᵣ WInt 2 ∗
        cs0 ↦ᵣ wcs0' ∗
        cs1 ↦ᵣ wcs1' ∗
        cgp_b ↦ₐ WInt 2 ∗
        [[csp_b, csp_e]] ↦ₐ [[stk_mem']] ∗
        codefrag_pers pc_a lse_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow Hcgp_nonheap Hstk_mmio Hcsp_size)
      "(HPC & Hcgp & Hcsp & Hct0 & Hct1 & Hcs0 & Hcs1
      & Hcgp_b & Hstk & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.
    rewrite /lse_a_cap.

    (* Block 4: push the capability of [a], load [a] *)
    focus_block (lse_block ".Llse_f") "Hcode_main" of lse_main_blocks at pc_a as a_f Ha_f "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetB cs0 cgp *)
    iInstr "Hcode".
    (* Add cs1 cs0 1 *)
    iInstr "Hcode".
    (* Subseg cgp cgp cs0 cs1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1%nat)%a); [solve_addr+Hcgp_bounds|reflexivity]. }
    { solve_addr+Hcgp_bounds. }
    { solve_addr+Hcgp_bounds. }
    unfold StackEntry_reserved_space in Hcsp_size.
    assert ((stk_start_a csp_b csp_e + 2)%a = Some csp_e) as Hstart
      by (unfold stk_start_a, StackEntry_reserved_space; solve_addr+Hcsp_size).
    remember (stk_start_a csp_b csp_e) as a_start eqn:Ha_start.
    assert (csp_b < a_start)%a as Hcsp_lt by solve_addr+Hcsp_size Hstart.
    (* The two cells reserved at the top of the stack *)
    iDestruct (region_pointsto_split_top with "Hstk") as (stk_mem1 w_res1 ->) "[Hstk Hres1]";
      first solve_addr+Hcsp_size Hstart.
    iDestruct (region_pointsto_split_top with "Hstk") as (stk_mem2 w_res2 ->) "[Hstk Hres2]";
      first solve_addr+Hcsp_size Hstart.
    replace ((csp_e ^+ -1) ^+ -1)%a with a_start by solve_addr+Hcsp_size Hstart.
    iDestruct (region_pointsto_split_top with "Hstk") as (stk_mem' w_top ->) "[Hstk Ha_stk]";
      first exact Hcsp_lt.
    assert ((a_start + -1)%a = Some (a_start ^+ -1)%a) as Hcsp_top
      by solve_addr+Hcsp_lt.
    (* Store csp cgp (-1) *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr+Hcsp_size Hstart. }
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { done. }
    { split; [solve_pure|solve_addr+Hcgp_bounds]. }
    (* Mov ct1 2 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iAssert ([[csp_e, csp_e]] ↦ₐ [[ [] ]])%I as "Hstk_nil".
    { rewrite /region_pointsto finz_seq_between_empty; [done|solve_addr]. }
    iDestruct (region_pointsto_cons (csp_e ^+ -1)%a csp_e csp_e
      with "[$Hres1 $Hstk_nil]") as "Hres_top".
    { solve_addr+Hcsp_size Hstart. }
    { solve_addr. }
    iDestruct (region_pointsto_cons a_start (csp_e ^+ -1)%a csp_e
      with "[$Hres2 $Hres_top]") as "Hres".
    { solve_addr+Hcsp_size Hstart. }
    { solve_addr+Hcsp_size Hstart. }
    iDestruct (region_pointsto_cons (a_start ^+ -1)%a a_start csp_e
      with "[$Ha_stk $Hres]") as "Ha_stk".
    { solve_addr+Hcsp_size Hstart. }
    { solve_addr+Hcsp_size Hstart. }
    iDestruct (region_pointsto_split_r csp_b csp_e (a_start ^+ -1)%a
      with "[$Hstk $Ha_stk]") as "Hstk".
    { solve_addr+Hcsp_size Hstart. }
    { rewrite /finz.dist. cbn. solve_addr+Hcsp_size Hstart. }
    assert ((a_f ^+ 6)%a = (pc_a ^+ lse_label_offset ".Llse_f_assert")%a) as ->
      by (offsets_compute; solve_addr).
    subst a_start.
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End LSE_F_Blocks_1.
