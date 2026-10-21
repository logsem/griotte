From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import trusted_spill_registers_spec.

(** * Shared interfaces of the exception path of the switcher

    The exception path runs from the exception entry ([exception_entry_asm],
    block 21) to the forced unwind of the faulting compartment's call, or to
    the resumption of a fault of the first spill of the call path. Its
    block-group lemmas only depend on this file and on the specifications of
    the spill and reload macros ([trusted_spill_registers_spec]):
    - [switcher_exception_blocks_1]: blocks 21-23, swap the trusted stack
      in from mtdc, spill the registers of the interrupted context in the
      register save area, then the PC, mstatus and the cause, and dispatch
      on the cause,
    - [switcher_exception_blocks_2]: blocks 24-25, [.Lhandle_error]:
      restore mtdc, test for a fault of the switcher and for a trusted stack
      with no frame, and force the unwind, or, for a fault of the first
      spill of the call path, overwrite the saved return values,
    - [switcher_exception_blocks_3]: block 28, [.Lcommon_context_install]:
      install the context of the register save area and resume it.

    The specifications are thread-generic: they take the points-to of the
    register save area, not the invariant of the switcher. *)

Section Switcher_Exception_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The end of the register save area of the trusted stack. *)
  Definition tstack_save_end : Addr := (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a.

  (** The capability of mtdc, to the base of the trusted stack. *)
  Definition tstack_cap : LWord :=
    WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack.

  (** The register save area after the spill of the exception entry, from
      the save area [save]: the PC [wmepcc] at word 0, the registers x1 to
      x15 [wregs] at words 1 to 15, mstatus [wst] at word 17 and the cause
      [wcause] at word 18. The other words are kept. *)
  Definition exception_spill (save : list LWord) (wmepcc : LWord) (wregs : list LWord)
    (wst wcause : LWord) : list LWord :=
    wmepcc :: wregs ++ take 1 (drop 16 save) ++ [wst; wcause] ++ drop 19 save.

  Lemma exception_spill_length save wmepcc wregs wst wcause :
    length save = 21%nat →
    length wregs = 15%nat →
    length (exception_spill save wmepcc wregs wst wcause) = 21%nat.
  Proof.
    intros Hsave Hregs.
    rewrite /exception_spill /= !length_app length_take !length_drop /=.
    rewrite length_drop Hsave Hregs; reflexivity.
  Qed.

  (** The register save area holds 21 words. *)
  Lemma tstack_save_area_length save :
    [[ b_trusted_stack, tstack_save_end ]] ↦ₐ [[ save ]] -∗ ⌜length save = 21%nat⌝.
  Proof.
    iIntros "Hsave". rewrite /region_pointsto.
    iDestruct (big_sepL2_length with "Hsave") as %Hlen.
    iPureIntro. rewrite -Hlen finz_seq_between_length /finz.dist /tstack_save_end.
    pose proof trusted_stack_frames_fit as [n Hfit].
    tstack_unfold. solve_addr.
  Qed.

  (** The words of the register save area are in the bounds of the trusted
      stack, outside the shadow table. *)
  Lemma tstack_save_cell_ok (k : Z) :
    (0 <= k < 21)%Z →
    (b_trusted_stack + k)%a = Some (b_trusted_stack ^+ k)%a ∧
    withinBounds b_trusted_stack e_trusted_stack (b_trusted_stack ^+ k)%a = true ∧
    is_shadow_address (b_trusted_stack ^+ k)%a = false.
  Proof.
    intros Hk.
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    tstack_unfold.
    split_and!; [solve_addr | rewrite /withinBounds; solve_addr | tstk_not_shadow Hts_shadow].
  Qed.

  (** The cells of the registers but the stack pointer in the register save
      area. *)
  Lemma trusted_save_cells_ok_exception :
    trusted_save_cells_ok b_trusted_stack e_trusted_stack b_trusted_stack exception_spill_regs.
  Proof.
    intros r Hr. apply tstack_save_cell_ok.
    rewrite /exception_spill_regs !elem_of_cons elem_of_nil in Hr.
    repeat (destruct Hr as [-> | Hr]);
      cbv [TrustedStack_offset_reg cra cgp ctp ct0 ct1 ct2 cs0 cs1 ca0 ca1 ca2 ca3 ca4 ca5
           Z.of_nat Pos.of_succ_nat Pos.succ];
      lia.
  Qed.

End Switcher_Exception_States.
