From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, block 2: halt

    From the return of the call to [C.adv], the second instruction of
    block 2 halts the machine. *)

Section SO_Run_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_run_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (φ : language.val griotte_lang -> iProp Σ) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_instr_offset 2 1)%a ∗
    codefrag pc_a so_main_code ∗
    ▷ (PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ so_instr_offset 2 1)%a ∗
        codefrag pc_a so_main_code
        -∗ WP Instr Halted {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous]) "(HPC & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 2: halt *)
    focus_block 2 "Hcode_main" of so_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_call ^+ 1)%a.
    (* Halt *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ so_instr_offset 2 1)%a.
    iApply "Hpost"; iFrame.
  Qed.

End SO_Run_Blocks_2.
