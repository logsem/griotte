From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_preamble.

(** * Failure: thread exit

    [.Lcommon_defer_irqs_and_thread_exit] disables interrupts, then
    [.Lcommon_thread_exit] halts the machine. It is reached when the return
    routine finds no frame to pop. *)

Section Common_Thread_Exit.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters} {CR : CritRoute Σ th CL}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lcommon_defer_irqs_and_thread_exit], at the posture [b]: the
      thread exits, with interrupts disabled and the posture at
      InterruptDisabled. *)
  Lemma common_defer_irqs_and_thread_exit_spec (E : coPset) (Φ : tval (kind_of th) → iProp Σ)
    (b : InterruptStatus) :
    route_pre th b →
    PC ↦ₚ switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
    switcher_code ∗
    MIE ↦ₜ b ∗
    held b ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lcommon_thread_exit" ∗
        MIE ↦ₜ InterruptDisabled ∗
        held InterruptDisabled
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Exec @ E {{ Φ }}.
  Proof.
    iIntros (Hpre) "(HPC & #Hswitcher & Hmie & Hheld & Hpost)".
    switcher_open_label ".Lcommon_defer_irqs_and_thread_exit" "Hswitcher" as "Hcode".
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    (* Halt *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lcommon_thread_exit".
    iApply wp_value_fupd.
    by iMod ("Hpost" with "[$HPC $Hmie $Hheld]").
  Qed.

End Common_Thread_Exit.
