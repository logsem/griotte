From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_stack_spec.

(** * Call routine: the callee's stack

    [.Lswitch_stack_chop] restricts the stack capability to the callee's
    stack, below the spill area: [ct2] gets it with its cursor at the base,
    and [csp] with its cursor at the top. CHERIoT computes the length for
    its relative [csetboundsrounddown] and rounds the top down; [Subseg]
    takes the bounds and sets them exactly. [.Lswitcher_zero_callee_stack]
    clears the callee's stack ([clear_stack_asm]), and
    [.Lswitch_after_zero] loads the unsealing capability of the switcher,
    one word before its code ([.Lswitcher_unseal_key]). The region falls
    through to [.Lswitch_unseal_entry]. *)

Section Switch_Stack_Chop.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_stack_chop]: restrict the stack capability to the
      callee's stack, below the spill area, clear it, and load the unsealing
      capability of the switcher in [cs0]. *)
  Lemma switch_stack_chop_spec
    (b e a : Addr) (stk_mem : list LWord) (wcs0 wcs1 wct2 : LWord) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_chop" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lswitch_unseal_entry" ∗
        cs0 ↦ᵣ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
        (∃ wct2', ct2 ↦ᵣ wct2') ∗
        csp ↦ᵣ chopped_csp b e a ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hstk_heap)
      "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & Hstk & #Hb_switcher & #Hswitcher & Hpost)".
    rewrite /chopped_csp.
    stk_unfold.
    iAssert switcher_code as "Hswitcher_zero"; first iFrame "Hswitcher".
    iAssert switcher_code as "Hswitcher_key"; first iFrame "Hswitcher".

    (* [.Lswitch_stack_chop] *)
    switcher_open_label ".Lswitch_stack_chop" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* GetA cs0 csp *)
    iInstr "Hcode".
    (* GetB cs1 csp *)
    iInstr "Hcode".
    (* SetA csp csp cs1 *)
    iInstr "Hcode".
    assert ((None : option AId) = None → (b < a ^+ -4)%a → is_heap_address b = false)
      as Hnot_heap.
    { intros _ Hlt. eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      apply withinBounds_true_iff. solve_addr. }
    (* Subseg ct2 csp cs1 cs0 *)
    iInstr "Hcode".
    { rewrite /isWithin; solve_addr. }
    (* GetE cs0 ct2 *)
    iInstr "Hcode".
    (* SetA csp ct2 cs0 *)
    iInstr "Hcode".

    (* [.Lswitcher_zero_callee_stack] *)
    switcher_open_label ".Lswitcher_zero_callee_stack" "Hswitcher_zero" as "Hcode_zero".
    iApply (clear_stack_spec with "[- $HPC $Hcode_zero $Hct2 $Hcs0 $Hstk]");
      try solve_pure.
    all: try (clear -Hba Hba3 Ha4; solve_addr).
    { pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
      rewrite /disjoint_from_shadow elem_of_disjoint in Hstk_shadow |- *.
      intros x Hx HR. eapply Hstk_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    iIntros "!> (HPC & Hct2 & Hcs0 & _ & Hstk)".

    (* [.Lswitch_after_zero] *)
    switcher_open_label ".Lswitch_after_zero" "Hswitcher_key" as "Hcode_key".
    (* Auipcc cs0 .Lswitcher_unseal_key *)
    iInstr "Hcode_key".
    { instantiate (1 := b_switcher). switcher_addr_eq. }
    (* CLoad cs0 cs0 0 *)
    iInstr "Hcode_key".
    { apply switcher_base_not_shadow. }
    { done. }
    switcher_change_pc_label ".Lswitch_unseal_entry".
    subst hpost.
    iApply "Hpost".
    iFrame "HPC Hcs0 Hcs1 Hct2 Hcsp Hstk".
  Qed.

End Switch_Stack_Chop.
