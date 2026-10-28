From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_preamble.

(** * Failure: the callee's stack is too small

    [.Lswitch_stack_too_small] is reached when the callee's stack is smaller
    than the minimum stack size of the entry point plus the space reserved
    at its top ([StackEntry_reserved_space]). The frame is already pushed:
    it sets the return values [-ENOTENOUGHSTACK] and 0, and jumps to the
    return routine, [switcher_after_compartment_call], which pops it. *)

Section Switch_Stack_Too_Small.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_stack_too_small]: the return values are set, and the
      PC is at the return routine. *)
  Lemma switch_stack_too_small_spec (wca0 wca1 : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_too_small" ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ[th] switcher_label_pc "switcher_after_compartment_call" ∗
        ca0 ↦ᵣ[th] WInt ENOTENOUGHSTACK ∗
        ca1 ↦ᵣ[th] WInt 0 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hca0 & Hca1 & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_stack_too_small" "Hswitcher" as "Hcode".
    (* Mov ca0 ENOTENOUGHSTACK *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jmp switcher_after_compartment_call *)
    iInstr "Hcode".
    { jump_to (a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call")%a
        by switcher_addr_eq. }
    destruct (decide (ca0 = cnull)) as [Hca0_null|_]; first done.
    iApply "Hpost". iFrame "HPC Hca0 Hca1".
  Qed.

End Switch_Stack_Too_Small.
