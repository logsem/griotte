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
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_f_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (Nassert : namespace) (E : coPset)
    (wcgp wcs0 wcs1 wcra wca0 wca1 wcnull : Word) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    ↑Nassert ⊆ E ->
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    na_own cerise_nais E ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ lse_block_offset 5)%a ∗
    cgp ↦ᵣ wcgp ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct0 ↦ᵣ WInt 2 ∗
    ct1 ↦ᵣ WInt 2 ∗
    cra ↦ᵣ wcra ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wcnull ∗
    (pc_b ^+ 1)%a ↦ₐ lse_assert_entry ∗
    codefrag pc_a lse_main_code ∗
    ▷ (na_own cerise_nais E ∗
        PC ↦ᵣ updatePcPerm wcra ∗
        cgp ↦ᵣ WInt 0 ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs1 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wcra ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        (pc_b ^+ 1)%a ↦ₐ lse_assert_entry ∗
        codefrag pc_a lse_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] HNassert)
      "(#Hassert & Hna & HPC & Hcgp & Hcs0 & Hcs1 & Hct0 & Hct1 & Hcra
      & Hca0 & Hca1 & Hcnull & Himport_assert & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.
    rewrite /lse_assert_entry.

    (* Block 5: assert that [a] contains [2] *)
    focus_block 5 "Hcode_main" of lse_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hcgp $Hcs0 $Hcs1 $Hct0 $Hct1 $Hcra $Hcnull
              $Hcode $Himport_assert]"); auto.
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(Hna & HPC & Hcgp & Hcs0 & Hcs1 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: clear the return values, and return *)
    focus_block 6 "Hcode_main" of lse_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame.
  Qed.

End LSE_F_Blocks_2.
