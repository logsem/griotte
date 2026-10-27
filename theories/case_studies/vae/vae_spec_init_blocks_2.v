From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import vae_spec_states.

(** * VAE, block 3: return

    From the return of the call to [B.adv], the last two instructions of
    block 3 restore the return address of the thread, the switcher's return
    sentry saved in [cs0], and return through it: the thread exits. *)

Section VAE_Init_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma vae_init_return_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable) (cstk : CSTK) (wcra wctp wct0 wct2 : LWord) :
    vae_code_bounds pc_b pc_e pc_a C_f ->
    cstk.(cstk_frames) = [] ->
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] WCap true RX Global pc_b pc_e (pc_a ^+ vae_label_offset ".Lvae_init_return")%a ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cstack_frag cstk ∗
    codefrag_pers pc_a vae_main_code
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & _) Hframes)
      "(#Hswitcher & #Hswitcher_static & Hna & HPC & Hcs0 & Hcra & Hctp & Hct0 & Hct2
        & Hcstk & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    vae_unfold_code.

    (* Block 3: return *)
    focus_block (vae_block ".Lvae_init_call") "Hcode_main" of vae_main_blocks at pc_a
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

End VAE_Init_Blocks_2.
