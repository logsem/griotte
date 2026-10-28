From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import stack_object_spec_states.

(** * Stack object, block 2: return

    From the return of the call to [C.adv], the last two instructions of
    block 2 restore the return address of the thread, the switcher's return
    sentry saved in [cs0], and return through it: the thread exits. *)

Section SO_Run_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_run_return_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable) (cstk : CSTK) (wcra wctp wct0 wct2 : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    cstk.(cstk_frames) = [] ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_run_return")%a ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a so_main_code
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & _) Hframes)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcs0 & Hcra & Hctp & Hct0 & Hct2
        & Hcstk & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.

    (* Block 2: return *)
    focus_block (so_block ".Lso_run_call") "Hcode_main" of so_main_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    change_pc_to (a_call ^+ 2).
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.

End SO_Run_Blocks_2.
