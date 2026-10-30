From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import call_stack switcher_preamble clear_stack_spec.

(** * Call routine: the callee's stack

    [.Lswitch_stack_chop] restricts the stack capability to the callee's
    stack, below the spill area: [ct2] gets it with its cursor at the base,
    and [csp] with its cursor at the top. CHERIoT computes the length for
    its relative [csetboundsrounddown] and rounds the top down; [Subseg]
    takes the bounds and sets them exactly. It then reads MSHWM and clears
    the callee's stack from it ([clear_stack_asm]), unless MSHWM is at or
    above the top; the first store faults when MSHWM is below the base of
    the callee's stack. [.Lswitch_after_zero] loads the
    unsealing capability of the switcher ([.unsealing_key_import_tables]),
    in the data words before its code. The region falls
    through to [.Lswitch_unseal_entry]. *)

Section Switch_Stack_Chop.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The last block of [.Lswitch_stack_chop]: load the unsealing capability
      of the switcher in [cs0], at [.Lswitch_after_zero]. *)
  #[local] Ltac chop_after_zero :=
    switcher_open_label ".Lswitch_after_zero" "Hswitcher_key" as "Hcode_key";
    (* Auipcc cs0 .unsealing_key_import_tables *)
    iInstr "Hcode_key";
    [ instantiate (1 := b_switcher ^+ 1); switcher_addr_eq | ];
    (* CLoad cs0 cs0 0 *)
    iInstr "Hcode_key";
    [ apply switcher_key_not_shadow
    | done
    | apply withinBounds_true_iff;
      pose proof switcher_call_entry_point; pose proof switcher_size; solve_addr
    | ];
    switcher_change_pc_label ".Lswitch_unseal_entry".

  (** From [.Lswitch_stack_chop]: restrict the stack capability to the
      callee's stack, below the spill area, clear it from the value [h] of
      MSHWM, unless [h] is above it, and load the unsealing capability of the
      switcher in [cs0]. The cells from [h] are zeroed. When [h] is below the
      base of the callee's stack, the first store of the zeroing faults. *)
  Lemma switch_stack_chop_spec
    (b e a : Addr) (stk_mem : list LWord) (wcs0 wcs1 wct2 wcgp : LWord) (hb h : Z) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->
    (0 <= hb <= h)%Z ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_stack_chop" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cgp ↦ᵣ[th] wcgp ∗
    csp ↦ᵣ[th] Cap RWL Local b e (stk_saved_a a) ∗
    stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
    hwm_regs hb h ∗
    (b_switcher ^+ 1) ↦ₐ□ SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
    switcher_code ∗
    ( ▷ ( (* the zeroing, from the value [h] read from MSHWM, did not fault *)
          ⌜(stk_callee_b b a <= h)%Z⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_unseal_entry" ∗
          cs0 ↦ᵣ[th] SealRange (true,true) Global ot_switcher (ot_switcher ^+ 1) ot_switcher ∗
          (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          cgp ↦ᵣ[th] WInt h ∗
          csp ↦ᵣ[th] chopped_csp b e a ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a)
            (stack_zeroed_from (stk_callee_b b a) h stk_mem) ∗
          hwm_regs hb h -∗
          safe[th] ) ∧
      (* the first store of the zeroing faults: [h] is below the base *)
      ( ∀ off : Z,
          ⌜(h < stk_callee_b b a)%Z⌝ -∗
          ⌜ trap_no_resume (switcher_pc off) ⌝ -∗
          (∃ wcs0', cs0 ↦ᵣ[th] wcs0') ∗
          (∃ wcs1', cs1 ↦ᵣ[th] wcs1') ∗
          (∃ wct2', ct2 ↦ᵣ[th] wct2') ∗
          cgp ↦ᵣ[th] WInt h ∗
          csp ↦ᵣ[th] chopped_csp b e a ∗
          stack_region (stk_callee_b b a) (stk_callee_e e a) stk_mem ∗
          hwm_regs hb h -∗
          trap_safe (switcher_pc off) ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hstk_heap Hhwm_ok)
      "(HPC & Hcs0 & Hcs1 & Hct2 & Hcgp & Hcsp & Hstk & [Hmshwmb Hmshwm]
        & #Hb_switcher & #Hswitcher & Hpost)".
    rewrite /chopped_csp.
    stk_unfold.
    iAssert switcher_code as "Hswitcher_key"; first iFrame "Hswitcher".
    pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.

    (* [.Lswitch_stack_chop] *)
    switcher_open_label ".Lswitch_stack_chop" "Hswitcher" as "Hcode" a_chop Heq_chop.
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
    (* SpecialRW cgp MSHWM (inr cnull) *)
    iInstrApply "Hcode" wp_csrr_mshwm with "[$HPC $Hcgp $Hmshwm]"
      as "(HPC & Hcgp & Hmshwm)".
    iDestruct (big_sepL2_length with "Hstk") as %Hlen_stk.
    rewrite finz_seq_between_length in Hlen_stk.
    destruct (decide ((a ^+ -4) <= h)%Z) as [Habove | Hbelow].
    { (* Jle .Lswitch_after_zero csp cgp *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hcsp $Hcgp]"
        as "(HPC & Hcsp & Hcgp)".
      { cbn; apply Z.leb_le; solve_addr. }
      chop_after_zero.
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[%]"); [solve_addr |].
      rewrite stack_zeroed_from_above; last (rewrite -Hlen_stk /finz.dist; solve_addr).
      iFrame. }
    (* Jle .Lswitch_after_zero csp cgp *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hcsp $Hcgp]"
      as "(HPC & Hcsp & Hcgp)".
    { cbn; apply Z.leb_gt; solve_addr. }
    assert (0 <= h)%Z as Hv0 by lia.
    destruct (finz_of_z_spec MemNum h) as [ (va & Hva & Hvaeq) | [_ Hva] ];
      last (exfalso; solve_addr).
    subst h.
    (* SetA ct2 csp cgp *)
    iInstr "Hcode".

    (* zero_stack t2, s0, gp *)
    iAssert (codefrag_pers (a_chop ^+ 9%nat) (clear_stack_instrs ct2 cs0)) as "Hcode_zero".
    { iEval (rewrite -(take_drop 9 (encodeInstrsW _))) in "Hcode".
      iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode']".
      rewrite length_take_le; last (cbn; lia).
      iExact "Hcode'". }
    destruct (decide (b <= va)%a) as [Hbva | Hvab]; cycle 1.
    { (* The first store of the zeroing faults *)
      iApply (clear_stack_below_base_spec with "[- $HPC $Hcode_zero $Hct2 $Hcs0]");
        try solve_pure.
      { cbn [length clear_stack_instrs]; solve_addr. }
      all: try solve_addr.
      iIntros "[Hct2 Hcs0]".
      iDestruct "Hpost" as "[_ Hfailed]".
      rewrite (_ : (a_chop ^+ 9%nat) ^+ 1
                   = a_switcher_call ^+ (switcher_label_offset ".Lswitch_stack_chop" + 10));
        last (subst a_chop; switcher_addr_eq).
      iApply ("Hfailed" with
               "[%] [%] [$Hcs0 $Hcs1 $Hct2 $Hcgp $Hcsp $Hstk $Hmshwmb $Hmshwm]").
      { solve_addr. }
      { apply trap_no_resume_switcher_pc; by vm_compute. } }
    iDestruct (stack_region_split b va with "Hstk") as "[Hstk_lo Hstk_hi]";
      [solve_addr|solve_addr|].
    iApply (clear_stack_spec _ _ _ _ _ _ b _ va _ ct2 cs0 _ hb va
             with "[- $HPC $Hcode_zero $Hct2 $Hcs0 $Hstk_hi $Hmshwmb $Hmshwm]");
      try solve_pure.
    { cbn [length clear_stack_instrs]; solve_addr. }
    { solve_addr. }
    { cbn. lia. }
    { rewrite /disjoint_from_shadow elem_of_disjoint in Hstk_shadow |- *.
      intros x Hx HR. eapply Hstk_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    iIntros "!> (HPC & Hct2 & Hcs0 & [Hmshwmb Hmshwm] & _ & Hzero)".

    (* [.Lswitch_after_zero] *)
    chop_after_zero.
    iDestruct "Hpost" as "[Hpost _]".
    iApply ("Hpost" with "[%]"); [solve_addr |].
    iFrame "HPC Hcs0 Hcs1 Hcgp Hcsp Hmshwmb Hmshwm".
    iSplitL "Hct2"; first by iExists _.
    iApply (stack_region_zeroed_from with "[$Hstk_lo $Hzero]"); [solve_addr | solve_addr |].
    rewrite -Hlen_stk. done.
  Qed.

End Switch_Stack_Chop.
