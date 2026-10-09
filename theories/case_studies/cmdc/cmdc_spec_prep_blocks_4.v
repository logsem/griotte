From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, block 5: preparation of the call to [C.g]

    On return from the call to [B.f], and after the assertion on [c],
    block 5 sets [b := 42] and prepares the argument
    [(RW, Global, c, c+1, c)] of the call to [C.g] in [ca0]. The group ends
    with [cgp] pointing to [b]. *)

Section CMDC_Prep_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma cmdc_prep_blocks_4_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wcgp_b wca0 wca1 wct0 wct1 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->
    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 5)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cgp_b ↦ₐ wcgp_b ∗
    codefrag pc_a cmdc_main_code ∗
    ▷ ( PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 6)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WCap RW Global (cgp_b ^+ 1)%a (cgp_b ^+ 2)%a (cgp_b ^+ 1)%a ∗
        ca1 ↦ᵣ WInt 0 ∗
        (∃ w, ct0 ↦ᵣ w) ∗
        (∃ w, ct1 ↦ᵣ w) ∗
        cgp_b ↦ₐ WInt 42 ∗
        codefrag pc_a cmdc_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous)
      "(HPC & Hcgp & Hca0 & Hca1 & Hct0 & Hct1 & Hcgp_b & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code cmdc_main_code "Hcode_main".

    (* Block 5: overwrite b and prepare the argument of the call to C.g *)
    focus_block 5 "Hcode_main" of cmdc_main_blocks at pc_a as a_prep Ha_prep "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 cgp *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Lea cgp (-1)%Z *)
    iInstr "Hcode".
    { transitivity (Some cgp_b); auto; solve_addr. }
    (* Store cgp 42%Z *)
    iInstr "Hcode".
    { solve_addr. }
    (* GetA ct0 ca0 *)
    iInstr "Hcode".
    (* Add ct1 ct0 1%Z *)
    iInstr "Hcode".
    (* Subseg ca0 ct0 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ cmdc_block_offset 6)%a.
    iApply "Hpost"; iFrame.
  Qed.

End CMDC_Prep_Blocks_4.
