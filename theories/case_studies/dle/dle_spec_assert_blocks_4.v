From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import dle_spec_states.

(** * Deep locality, blocks 3-5: assertion and halt

    On return from the second call, block 3 loads [b], block 4 asserts that
    [b = 42] and block 5 halts. *)

Section DLE_Assert_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_assert_blocks_4_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable)
    (wct0 wct1 wct2 wca2 wcnull wcra : LWord) :
    dle_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    assert_static b_assert e_assert a_flag ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ dle_label_offset ".Ldle_check")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ca2 ↦ᵣ wca2 ∗
    cnull ↦ᵣ wcnull ∗
    cra ↦ᵣ wcra ∗
    cgp_b ↦ₐ WInt 42 ∗
    (pc_b ^+ 1)%a ↦ₐ□ WSentry Inherit true RX Global b_assert e_assert b_assert ∗
    codefrag_pers pc_a dle_main_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap)
             Hcgp_contiguous Hcgp_mmio)
      "(#Hassert & Hna & HPC & Hcgp & Hct0 & Hct1 & Hct2 & Hca2 & Hcnull & Hcra
      & Hcgp_b & Himport_assert & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code dle_main_code "Hcode_main".

    (* Block 3: return from the second call *)
    focus_block (dle_block ".Ldle_call_B") "Hcode_main" of dle_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB ^+ 8)%a.
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { done. }
    { split; [done| solve_addr]. }
    (* Mov ct1 42%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: assert that b = 42 *)
    focus_block (dle_block ".Ldle_assert") "Hcode_main" of dle_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & Hcnull
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: halt *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Halt *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.
  Qed.

End DLE_Assert_Blocks_4.
