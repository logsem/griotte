From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import write_only_secret_spec_states_binary.

(** * Binary write-only sharing, block 0: the write-only capability

    In both runs, block 0 copies the capability [cgp] to the private data
    of [main] in [ca0], and restricts it to the permission [WO]. *)

Section Write_only_secret_Init_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
  .

  Lemma write_only_secret_init_blocks_1_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (wca0 swca0 : Word)
    (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length write_only_secret_main_code)%a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ca0 ↣ᵣ swca0 ∗
    codefrag pc_a write_only_secret_main_code ∗
    spec_codefrag pc_a write_only_secret_main_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ write_only_secret_block_offset 1)%a ∗
        PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ write_only_secret_block_offset 1)%a ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        cgp ↣ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WCap WO Global cgp_b cgp_e cgp_b ∗
        ca0 ↣ᵣ WCap WO Global cgp_b cgp_e cgp_b ∗
        codefrag pc_a write_only_secret_main_code ∗
        spec_codefrag pc_a write_only_secret_main_code
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds)
      "(#Hspec & Hj & HPC & HsPC & Hcgp & Hscgp & Hca0 & Hsca0
      & Hcode_main & Hscode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code write_only_secret_main_code "Hcode_main".
    unfold_code write_only_secret_main_code "Hscode_main".

    (* Block 0: the write-only capability *)
    focus_block_0_lockstep "Hscode_main" "Hcode_main" as "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.

    (* Mov ca0 cgp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Restrict ca0 (encodePermPair (WO, Global)) *)
    iInstr_lockstep "Hscode" "Hcode".
    1,4: by rewrite decode_encode_permPair_inv.
    1-4: solve_pure.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    change_pc_to (pc_a ^+ write_only_secret_block_offset 1)%a.
    iApply "Hpost"; iFrame.
  Qed.

End Write_only_secret_Init_Blocks_1.
