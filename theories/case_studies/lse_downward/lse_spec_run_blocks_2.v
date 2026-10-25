From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import lse_spec_states.

(** * LSE [run], block 3: return

    From the return of the call to [C_f], the last two instructions of
    block 3 restore the return address of the thread, the switcher's return
    sentry saved in [cs0], and return through it: the thread exits. *)

Section LSE_Run_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma lse_run_return_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable) (cstk : CSTK) (wcra wctp wct0 wct2 : LWord) :
    lse_code_bounds pc_b pc_e pc_a C_f ->
    cstk.(cstk_frames) = [] ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ lse_label_offset ".Llse_run_return")%a ∗
    cs0 ↦ᵣ thread_return_sentry ∗
    cra ↦ᵣ wcra ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct2 ↦ᵣ wct2 ∗
    cstack_frag cstk ∗
    codefrag_pers pc_a lse_main_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hframes)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcs0 & Hcra & Hctp & Hct0 & Hct2
        & Hcstk & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    lse_unfold_code.

    (* Block 3: return *)
    focus_block (lse_block ".Llse_run_call") "Hcode_main" of lse_main_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    change_pc_to (a_call ^+ 2)%a.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.

End LSE_Run_Blocks_2.
