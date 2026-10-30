From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, block 10: return

    Block 10 restores the return address of the thread, the switcher's
    return sentry saved in [cs0], and returns through it: the thread
    exits. *)

Section CMDC_Halt_Blocks_5.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma cmdc_return_spec
    (pc_b pc_e pc_a : Addr) (cstk : CSTK) (wcra wctp wct0 wct2 : LWord) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_main_code) ->
    cstk.(cstk_frames) = [] ->
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ cmdc_label_offset ".Lcmdc_return")%a ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ◯(CSTK)[th] cstk ∗
    codefrag_pers pc_a cmdc_main_code
    ⊢ safe[th].
  Proof.
    iIntros (HsubBounds Hframes)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcs0 & Hcra & Hctp & Hct0 & Hct2
        & Hcstk & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code cmdc_main_code "Hcode_main".

    (* Block 10: return *)
    focus_block (cmdc_block ".Lcmdc_return") "Hcode_main" of cmdc_main_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.

End CMDC_Halt_Blocks_5.
