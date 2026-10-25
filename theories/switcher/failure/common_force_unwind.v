From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_preamble.

(** * Failure: forced unwind

    [.Lcommon_force_unwind] sets the return values [-ECOMPARTMENTFAIL] and
    0, and jumps to the return routine, [switcher_after_compartment_call],
    which pops the topmost frame. It is
    reached when the checks on the stack pointer fail, and from the
    exception path. *)

Section Common_Force_Unwind.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lcommon_force_unwind]: the return values are set, and the PC
      is at the return routine. *)
  Lemma common_force_unwind_spec (wca0 wca1 : LWord) :
    PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc "switcher_after_compartment_call" ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hca0 & Hca1 & #Hswitcher & Hpost)".
    switcher_open_label ".Lcommon_force_unwind" "Hswitcher" as "Hcode".
    (* Mov ca0 ECOMPARTMENTFAIL *)
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

End Common_Force_Unwind.
