From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_preamble.

(** * Failure: thread exit

    [.Lcommon_defer_irqs_and_thread_exit] disables interrupts, then
    [.Lcommon_thread_exit] writes the exit marker to mcause: the thread's
    turn ends in [ExitV], and the context-switch thread continues at
    [a_exit]. It is reached when the return routine finds no frame to
    pop. *)

Section Common_Thread_Exit.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters} {CR : CritRoute Σ th CL}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lcommon_defer_irqs_and_thread_exit], at the posture [b]: the
      thread exits, with interrupts disabled and its posture at mcause
      [MCAUSE_THREAD_EXIT]. *)
  Lemma common_defer_irqs_and_thread_exit_spec (E : coPset) (Φ : tval (kind_of th) → iProp Σ)
    (b : InterruptStatus) :
    th ≠ CtxSwitch →
    route_pre th b →
    PC ↦ₚ switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
    switcher_code ∗
    MIE ↦ₜ b ∗
    held b ∗
    ▷ ( PC ↦ₚ Cap XSRW_ Local b_switcher e_switcher a_exit ∗
        MIE ↦ₜ InterruptDisabled ∗
        posture_res_gen None None (Some (lword_of_word (WInt MCAUSE_THREAD_EXIT))) None
        ={E}=∗
        Φ ExitV )
    ⊢ WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hth Hpre) "(HPC & #Hswitcher & Hmie & Hheld & Hpost)".
    switcher_open_label ".Lcommon_defer_irqs_and_thread_exit" "Hswitcher" as "Hcode"
      a_block Heq_block.
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    rewrite held_disabled handover_res_unfold.
    iDestruct "Hheld" as "[(%p & %c & %v & %b' & Hho) Hpart]".
    rewrite /handover_at /volatile_csr_at.
    iDestruct "Hho" as "(Hcrit & HU & Hepcc & Hcause & Htval & Hmpie)".
    (* SpecialRW cnull mcause (inl MCAUSE_THREAD_EXIT) *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iApply wp_fupd.
    rewrite (_ : a_block ^+ Z.to_nat 1 = a_block ^+ 1)%a; last done.
    iApply (wp_exit_marker _ _ _ _ _ _ _ a_exit with "HPC Hi Hcause").
    { done. }
    { by rewrite decode_encode_instrW_inv. }
    { solve_pure. }
    { done. }
    { subst a_block. pose proof a_exit_label as Hexit. clear - Hexit.
      offsets_compute. solve_addr. }
    iIntros "!> HPC _ Hcause".
    iApply ("Hpost" with "[$HPC $Hmie Hcrit HU Hepcc Hcause Htval Hmpie Hpart]").
    rewrite posture_res_gen_unfold. iFrame "Hpart".
    iExists p, _, v, b'. by iFrame.
  Qed.

End Common_Thread_Exit.
