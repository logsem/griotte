From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import vae_spec_states.

(** * VAE, block 3: halt

    From the return of the call to [B.adv], the second instruction of
    block 3 halts the machine. *)

Section VAE_Init_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_init_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (φ : language.val griotte_lang -> iProp Σ) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ vae_instr_offset 3 1)%a ∗
    codefrag pc_a vae_main_code ∗
    ▷ (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ vae_instr_offset 3 1)%a ∗
        codefrag pc_a vae_main_code
        -∗ WP Instr Halted {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous]) "(HPC & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.

    (* Block 3: halt *)
    focus_block 3 "Hcode_main" of vae_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_call ^+ 1)%a.
    (* Halt *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ vae_instr_offset 3 1)%a.
    iApply "Hpost"; iFrame.
  Qed.

End VAE_Init_Blocks_2.
