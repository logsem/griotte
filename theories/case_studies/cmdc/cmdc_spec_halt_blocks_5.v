From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, block 10: halt *)

Section CMDC_Halt_Blocks_5.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma cmdc_halt_blocks_5_spec
    (pc_b pc_e pc_a : Addr) (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code)%a ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset 10)%a ∗
    codefrag pc_a cmdc_main_code ∗
    ▷ WP Instr Halted {{ φ }}
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds) "(HPC & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code cmdc_main_code "Hcode_main".

    (* Block 10: halt *)
    focus_block 10 "Hcode_main" of cmdc_main_blocks at pc_a as a_halt Ha_halt "Hcode" "Hcont".
    (* Halt *)
    iInstr "Hcode".
    iApply "Hpost".
  Qed.

End CMDC_Halt_Blocks_5.
