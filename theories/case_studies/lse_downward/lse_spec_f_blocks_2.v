From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import lse_spec_states.

(** * LSE [f], blocks 5-6: assert that [a] contains [2], return

    Block 5 asserts that [ct0] (the content of [a]) and [ct1] are equal.
    Block 6 clears the return values and jumps to the return address, for
    the return to the switcher. *)

Section LSE_F_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_f_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (wcgp wcs0 wcra wca0 wca1 : LWord) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    jalr_target_ok cnull cra wcra.(lw) = true ->
    assert_static b_assert e_assert a_flag ∗
    PC ↦ₚ[th] WCap true RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_f_assert")%a ∗
    cgp ↦ᵣ[th] wcgp ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    ct0 ↦ᵣ[th] WInt 2 ∗
    ct1 ↦ᵣ[th] WInt 2 ∗
    cra ↦ᵣ[th] wcra ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    (pc_b ^+ 1)%a ↦ₐ□ lse_assert_entry ∗
    codefrag_pers pc_a lse_main_code ∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm wcra ∗
        cgp ↦ᵣ[th] WInt 0 ∗
        cs0 ↦ᵣ[th] WInt 0 ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wcra ∗
        ca0 ↦ᵣ[th] WInt 0 ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        (pc_b ^+ 1)%a ↦ₐ□ lse_assert_entry ∗
        codefrag_pers pc_a lse_main_code
        -∗ WP Seq (Instr Executable) @[th] {{ HO th }})
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Htgt)
      "(#Hassert & HPC & Hcgp & Hcs0 & Hct0 & Hct1 & Hcra
      & Hca0 & Hca1 & Himport_assert & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.
    rewrite /lse_assert_entry.

    (* Block 5: assert that [a] contains [2] *)
    focus_block (lse_block ".Llse_f_assert") "Hcode_main" of lse_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hcgp $Hcs0 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hcs0 & Hcra & Hct0 & Hct1
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: clear the return values, and return *)
    focus_block (lse_block ".Llse_f_return") "Hcode_main" of lse_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End LSE_F_Blocks_2.
