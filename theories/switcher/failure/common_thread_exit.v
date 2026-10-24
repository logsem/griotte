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
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lcommon_defer_irqs_and_thread_exit]: the thread exits, with
      interrupts disabled. *)
  Lemma common_defer_irqs_and_thread_exit_spec (E : coPset) (Φ : griotte_lang.val → iProp Σ) :
    PC ↦ₚ switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lcommon_thread_exit"
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    iIntros "(HPC & #Hswitcher & Hpost)".
    switcher_open_label ".Lcommon_defer_irqs_and_thread_exit" "Hswitcher" as "Hcode".
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    (* Halt *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lcommon_thread_exit".
    iApply wp_value_fupd.
    by iMod ("Hpost" with "HPC").
  Qed.

End Common_Thread_Exit.
