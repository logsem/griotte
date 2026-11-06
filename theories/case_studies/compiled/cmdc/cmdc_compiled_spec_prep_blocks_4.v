From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_compiled_spec_states.

(** * Compiled cmdc, block 4: preparation of the call to [C.g]

    After the assertion on [c], block 4 sets [b := 42] through [cs0] and
    prepares the argument of the call to [C.g], the capability to [c] in
    [cs1], in [ca0]. *)

Section CMDC_Compiled_Prep_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma cmdc_compiled_prep_blocks_4_spec
    (pc_b pc_e pc_a a_b : Addr)
    (wb wca0 wcs1 : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_compiled_main_code) ->
    (a_b + 1)%a = Some (a_b ^+ 1) ->
    is_mmio_address a_b = false ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e
      (pc_a ^+ cmdc_compiled_label_offset ".Lcmdc_run_return_assert_1")%a ∗
    cs0 ↦ᵣ[th] Cap RW Global a_b (a_b ^+ 1) a_b ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ca0 ↦ᵣ[th] wca0 ∗
    a_b ↦ₐ wb ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e
          (pc_a ^+ cmdc_compiled_label_offset ".Lcmdc_run_call_C_g")%a ∗
        cs0 ↦ᵣ[th] Cap RW Global a_b (a_b ^+ 1) a_b ∗
        cs1 ↦ᵣ[th] wcs1 ∗
        ca0 ↦ᵣ[th] wcs1 ∗
        a_b ↦ₐ WInt 42 ∗
        codefrag_pers pc_a cmdc_compiled_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Ha_b Ha_b_mmio)
      "(HPC & Hcs0 & Hcs1 & Hca0 & Hb & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code cmdc_compiled_main_code "Hcode_main".

    (* Block 4: overwrite b and prepare the argument of the call to C.g *)
    focus_block (cmdc_compiled_block ".Lcmdc_run_return_assert_1") "Hcode_main"
      of cmdc_compiled_main_blocks at pc_a as a_prep Ha_prep "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 42 *)
    iInstr "Hcode".
    (* Store cs0 ca0 0 *)
    iInstr "Hcode".
    { by apply not_mmio_not_shadow. }
    { rewrite /withinBounds; solve_addr. }
    (* Mov ca0 cs1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ cmdc_compiled_label_offset ".Lcmdc_run_call_C_g")%a.
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End CMDC_Compiled_Prep_Blocks_4.
