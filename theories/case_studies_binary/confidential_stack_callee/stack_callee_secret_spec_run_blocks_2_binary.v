From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import stack_callee_secret_spec_states_binary.

(** * Binary trusted callee, block 2: halt

    On return from the call to [B.adv], the last instruction of block 2
    halts both runs. The code is given back, to close the invariant of
    [T]. *)

Section Stack_callee_secret_Run_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
  .

  Lemma stack_callee_secret_run_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_callee_secret_instr_offset 2 1)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_callee_secret_instr_offset 2 1)%a ∗
    codefrag pc_a stack_callee_secret_code ∗
    spec_codefrag pc_a stack_callee_secret_code ∗
    ▷ ( ⤇ Seq (Instr Halted) ∗
        codefrag pc_a stack_callee_secret_code ∗
        spec_codefrag pc_a stack_callee_secret_code
        -∗ WP Instr Halted {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds) "(#Hspec & Hj & HPC & HsPC & Hcode_main & Hscode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    stack_callee_secret_unfold_code.

    (* Block 2: halt, after the return from the call to B.adv *)
    focus_block_lockstep 2 "Hscode_main" "Hcode_main" of stack_callee_secret_blocks at pc_a
      as a_halt Ha_halt "Hscode" "Hscont" "Hcode" "Hcont".
    change_pc_to (a_halt ^+ 1)%a.
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    (* Halt *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsi]") as "(Hj & HsPC & Hsi)";
      [solve_ndisj|solve_pure|solve_pure|].
    iSpecialize ("Hscode" with "Hsi").
    (* Halt *)
    iInstr "Hcode".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode_main" "Hcode_main".
    iApply ("Hpost" with "[$Hj $Hcode_main $Hscode_main]").
  Qed.

End Stack_callee_secret_Run_Blocks_2.
