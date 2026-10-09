From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import lse_spec_states.

(** * LSE [run], block 3: halt

    From the return of the call to [C_f], the last instruction of block 3
    halts the machine. *)

Section LSE_Run_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_run_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ lse_instr_offset 3 1)%a ∗
    codefrag pc_a lse_main_code ∗
    ▷ (codefrag pc_a lse_main_code ={⊤}=∗ na_own cerise_nais ⊤)
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous]) "(HPC & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.

    (* Block 3: halt *)
    focus_block 3 "Hcode_main" of lse_main_blocks at pc_a as a_halt Ha_halt "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_halt ^+ 1)%a.
    (* Halt *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iMod ("Hpost" with "Hcode_main") as "Hna".
    wp_end; iIntros "_"; iFrame.
  Qed.

End LSE_Run_Blocks_2.
