From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import droe_spec_states.

(** * Deep immutability, blocks 3-5: assertion and halt

    On return from the call, block 3 restores the return address saved in
    [cs0] and loads [b], block 4 asserts that [b = 42], and block 5 clears
    the return values and halts. *)

Section DROE_Assert_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma droe_assert_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable) (Nassert : namespace)
    (wca0 wca1 wct0 wct1 wct2 wct3 wct4 wcnull wcs0 wcra : Word) :
    droe_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ droe_instr_offset 3 2)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    ct4 ↦ᵣ wct4 ∗
    cnull ↦ᵣ wcnull ∗
    cs0 ↦ᵣ wcs0 ∗
    cra ↦ᵣ wcra ∗
    cgp_b ↦ₐ WInt 42 ∗
    (pc_b ^+ 1)%a ↦ₐ WSentry RX Global b_assert e_assert b_assert ∗
    codefrag pc_a droe_main_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous] Hcgp_contiguous)
      "(#Hassert & Hna & HPC & Hcgp & Hca0 & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4
      & Hcnull & Hcs0 & Hcra & Hcgp_b & Himport_assert & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code droe_main_code "Hcode_main".

    (* Block 3: return from the call *)
    focus_block 3 "Hcode_main" of droe_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB ^+ 2)%a.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Load ct0 cgp *)
    iInstr "Hcode".
    { split; [done| solve_addr]. }
    (* Mov ct1 42%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: assert that b = 42 *)
    focus_block 4 "Hcode_main" as a_assert Ha_assert "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (assert_success_spec with
             "[- $Hassert $Hna $HPC $Hct2 $Hct3 $Hct4 $Hct0 $Hct1 $Hcnull $Hcra
              $Hcode $Himport_assert]"); auto.
    { solve_addr. }
    iNext; iIntros "(Hna & HPC & Hct2 & Hct3 & Hct4 & Hcra & Hct0 & Hct1 & Hcnull
                    & Hcode & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: clear the return values and halt *)
    focus_block 5 "Hcode_main" as a_halt Ha_halt "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Halt *)
    iInstr "Hcode".
    wp_end; iIntros "_"; iFrame.
  Qed.

End DROE_Assert_Blocks_3.
