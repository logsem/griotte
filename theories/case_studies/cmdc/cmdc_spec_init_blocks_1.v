From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, block 0: initialisation of the data

    Block 0 sets [b := 0] and [c := 0], and prepares the argument
    [(RW, Global, b, b+1, b)] of the call to [B.f] in [ca0]. The group ends
    with [cgp] pointing to [c]. *)

Section CMDC_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma cmdc_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr)
    (wca0 wct0 wct1 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->
    (cgp_b + length cmdc_main_data)%a = Some cgp_e ->
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cgp_b ↦ₐ WInt 0 ∗
    (cgp_b ^+ 1)%a ↦ₐ WInt 0 ∗
    codefrag pc_a cmdc_main_code ∗
    ▷ ( PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 1)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e (cgp_b ^+ 1)%a ∗
        ca0 ↦ᵣ WCap RW Global cgp_b (cgp_b ^+ 1)%a cgp_b ∗
        (∃ w, ct0 ↦ᵣ w) ∗
        (∃ w, ct1 ↦ᵣ w) ∗
        cgp_b ↦ₐ WInt 0 ∗
        (cgp_b ^+ 1)%a ↦ₐ WInt 0 ∗
        codefrag pc_a cmdc_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcgp_b & Hcgp_c & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.

    (* Block 0: initialisation *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0%Z *)
    iInstr "Hcode".
    { solve_addr. }
    (* Mov ca0 cgp *)
    iInstr "Hcode".
    (* Lea cgp 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    (* Store cgp 0%Z *)
    iInstr "Hcode".
    { solve_addr. }
    (* GetA ct0 ca0 *)
    iInstr "Hcode".
    (* Add ct1 ct0 1%Z *)
    iInstr "Hcode".
    (* Subseg ca0 ct0 ct1 *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); auto; solve_addr. }
    { solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame.
  Qed.

End CMDC_Init_Blocks_1.
