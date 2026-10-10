From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Import stack_secret_spec_states_binary.

(** * Binary stack confidentiality, block 3: halt

    On return from the call to [B.f], the last instruction of block 3 halts
    both runs. *)

Section Stack_secret_Halt_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
  .

  Lemma stack_secret_halt_blocks_3_spec
    (pc_b pc_e pc_a : Addr) (φ : language.val griotte_lang -> iProp Σ) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_secret_main_code)%a ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_instr_offset 3 1)%a ∗
    PC ↣ᵣ WCap RX Global pc_b pc_e (pc_a ^+ stack_secret_instr_offset 3 1)%a ∗
    codefrag pc_a stack_secret_main_code ∗
    spec_codefrag pc_a stack_secret_main_code ∗
    ▷ ( ⤇ Seq (Instr Halted) -∗ WP Instr Halted {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (HsubBounds) "(#Hspec & Hj & HPC & HsPC & Hcode_main & Hscode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code stack_secret_main_code "Hcode_main".
    unfold_code stack_secret_main_code "Hscode_main".

    (* Block 3: halt, after the return from the call to B.f *)
    focus_block_lockstep 3 "Hscode_main" "Hcode_main" of stack_secret_main_blocks at pc_a
      as a_halt Ha_halt "Hscode" "Hscont" "Hcode" "Hcont".
    change_pc_to (a_halt ^+ 1)%a.
    (* Halt *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_halt with "[$Hspec $Hj $HsPC $Hsi]") as "(Hj & HsPC & Hsi)";
      [solve_ndisj|solve_pure|solve_pure|].
    (* Halt *)
    iInstr "Hcode".
    iApply ("Hpost" with "Hj").
  Qed.

End Stack_secret_Halt_Blocks_3.
