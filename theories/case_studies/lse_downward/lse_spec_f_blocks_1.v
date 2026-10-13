From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import lse_spec_states.

(** * LSE [f], block 4: push the capability of [a], load [a]

    Block 4 restricts [cgp] to the capability of [a] (at [cgp_b]), pushes
    it on top of the stack frame, loads [a] in [ct0] and [2] in [ct1]. When
    the stack frame is empty, the push fails, and so does the machine. *)

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
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
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
        csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
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
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow Hcgp_nonheap Hstk_mmio)
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
    (* Subseg cgp cs0 cs1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1%nat)%a); [solve_addr+Hcgp_bounds|reflexivity]. }
    { solve_addr+Hcgp_bounds. }
    { solve_addr+Hcgp_bounds. }
    destruct (decide (csp_b < csp_e)%a) as [Hcsp_size|Hcsp_size]; cycle 1.
    { (* The stack frame is empty: the push fails *)
      (* Store csp cgp 0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]"); try solve_pure.
      { rewrite /withinBounds; solve_addr+Hcsp_size. }
      iIntros "!> _".
      wp_pure; wp_end; iIntros (?); done.
    }
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length finz_dist_S in Hstklen; last solve_addr+Hcsp_size.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]".
    { transitivity (Some (csp_b ^+ 1)%a); [solve_addr+Hcsp_size|reflexivity]. }
    { solve_addr+Hcsp_size. }
    (* Store csp cgp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr+Hcsp_size. }
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { done. }
    { split; [solve_pure|solve_addr+Hcgp_bounds]. }
    (* Mov ct1 2 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk".
    { transitivity (Some (csp_b ^+ 1)%a); [solve_addr+Hcsp_size|reflexivity]. }
    { solve_addr+Hcsp_size. }
    assert ((a_f ^+ 6)%a = (pc_a ^+ lse_label_offset ".Llse_f_assert")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End LSE_F_Blocks_1.
