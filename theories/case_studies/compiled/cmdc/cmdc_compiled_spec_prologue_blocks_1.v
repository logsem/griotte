From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_compiled_spec_states.

(** * Compiled cmdc, block 0: the prologue of [run]

    Block 0 moves the stack cursor below the frame of [run] and spills
    [cs1], [cs0] and [cra] in its words 0, 1 and 2. It then sets [cs0] and
    [cs1] to 1-word capabilities to the globals [b] and [c], writes [0] in
    both, and prepares the argument [b] of the call to [B.f] in [ca0]. *)

Section CMDC_Compiled_Prologue_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma cmdc_compiled_prologue_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e a_f : Addr)
    (wcra wcs0 wcs1 wca0 wct1 wct2 wf0 wf1 wf2 wb wc : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_compiled_main_code) ->
    (cgp_b + length cmdc_compiled_main_data)%a = Some cgp_e ->
    is_mmio_address cgp_b = false ->
    is_heap_address cgp_b = false ->
    is_mmio_address (cgp_b ^+ 1) = false ->
    is_heap_address (cgp_b ^+ 1) = false ->
    disjoint_from_mmio csp_b csp_e ->
    (a_f + Z.of_nat cmdc_compiled_main_run_frame_size)%a = Some (stk_start_a csp_b csp_e) ->
    (csp_b <= a_f)%a ->
    (stk_start_a csp_b csp_e <= csp_e)%a ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    a_f ↦ₐ wf0 ∗
    (a_f ^+ 1) ↦ₐ wf1 ∗
    (a_f ^+ 2) ↦ₐ wf2 ∗
    cgp_b ↦ₐ wb ∗
    (cgp_b ^+ 1) ↦ₐ wc ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e
          (pc_a ^+ cmdc_compiled_label_offset ".Lcmdc_run_call_B_f")%a ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e a_f ∗
        cra ↦ᵣ[th] wcra ∗
        cs0 ↦ᵣ[th] Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b ∗
        cs1 ↦ᵣ[th] Cap RW Global (cgp_b ^+ 1) (cgp_b ^+ 2) (cgp_b ^+ 1) ∗
        ca0 ↦ᵣ[th] Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b ∗
        (∃ w, ct1 ↦ᵣ[th] w) ∗
        (∃ w, ct2 ↦ᵣ[th] w) ∗
        a_f ↦ₐ wcs1 ∗
        (a_f ^+ 1) ↦ₐ wcs0 ∗
        (a_f ^+ 2) ↦ₐ wcra ∗
        cgp_b ↦ₐ WInt 0 ∗
        (cgp_b ^+ 1) ↦ₐ WInt 0 ∗
        codefrag_pers pc_a cmdc_compiled_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hcgp_contiguous Hcgp_mmio Hcgp_heap Hcgp1_mmio Hcgp1_heap
               Hstk_mmio Ha_f Hcsp_b Hstk_start)
      "(HPC & Hcgp & Hcsp & Hcra & Hcs0 & Hcs1 & Hca0 & Hct1 & Hct2
        & Hf0 & Hf1 & Hf2 & Hcgp_b & Hcgp_c & Hcode_main & Hpost)".
    rewrite /cmdc_compiled_main_run_frame_size in Ha_f.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* Block 0: the prologue *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Lea csp csp (-3) *)
    iInstr "Hcode".
    { transitivity (Some a_f); auto; solve_addr. }
    assert ((a_f + 2)%a = Some (a_f ^+ 2)) as Ha_f2 by solve_addr+Ha_f.
    assert ((a_f + 1)%a = Some (a_f ^+ 1)) as Ha_f1 by solve_addr+Ha_f.
    (* Store csp cra 2 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr. }
    (* Store csp cs0 1 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr. }
    (* Store csp cs1 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hstk_mmio. }
    { rewrite /withinBounds; solve_addr. }
    (* Lea cs0 cgp 0 *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* GetA ct1 cs0 *)
    iInstr "Hcode".
    (* Add ct2 ct1 1 *)
    iInstr "Hcode".
    (* The side condition of [Subseg] on the new base takes the last
       non-heap fact of the context: that of [b]. *)
    move Hcgp_heap at bottom.
    (* Subseg cs0 cs0 ct1 ct2 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    { solve_addr. }
    { solve_addr. }
    (* Lea cs1 cgp 1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)); auto; solve_addr. }
    (* GetA ct1 cs1 *)
    iInstr "Hcode".
    (* Add ct2 ct1 1 *)
    iInstr "Hcode".
    move Hcgp1_heap at bottom.
    (* Subseg cs1 cs1 ct1 ct2 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 2)); auto; solve_addr. }
    { solve_addr. }
    { solve_addr. }
    (* Store cs0 0 0 *)
    iInstr "Hcode".
    { by apply not_mmio_not_shadow. }
    { solve_addr. }
    (* Store cs1 0 0 *)
    iInstr "Hcode".
    { by apply not_mmio_not_shadow. }
    { solve_addr. }
    (* Mov ca0 cs0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    (* The stack has the permission WL: the spilled words are unchanged *)
    iEval (rewrite !lstore_word_isWL //) in "Hf0 Hf1 Hf2".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End CMDC_Compiled_Prologue_Blocks_1.
