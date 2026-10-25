From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_call_states.

(** * Call routine: checks on the stack pointer

    [.Lswitch_csp_check] checks that [csp] has the permission [RWL] and that
    it is [Local]. When a check fails, the
    execution jumps to [.Lcommon_force_unwind]. *)

Section Switch_Csp_Check.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The call entry point is the label [.Lswitch_csp_check]. *)
  Lemma switcher_call_entry_label :
    (a_switcher_call ^+ switcher_label_offset ".Lswitch_csp_check")%a = a_switcher_call.
  Proof. switcher_addr_eq. Qed.

  (** From [.Lswitch_csp_check]: when [csp] is a [RWL] [Local] capability,
      the PC is at [.Lswitch_entry_first_spill]; otherwise, at
      [.Lcommon_force_unwind]. *)
  Lemma switch_csp_check_spec (wcsp wct2 wctp : LWord) :
    PC ↦ₚ switcher_label_pc ".Lswitch_csp_check" ∗
    csp ↦ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    switcher_code ∗
    ▷ ( ( ⌜ switcher_csp_checked wcsp ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitch_entry_first_spill" ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt COMPARTMENT_STACK_LOCALITY ∗
          ctp ↦ᵣ WInt COMPARTMENT_STACK_LOCALITY )
        ∨
        ( ⌜ ¬ switcher_csp_checked wcsp ⌝ ∗
          ∃ zct2 zctp,
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt zctp )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcsp & Hct2 & Hctp & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_csp_check" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* GetP ct2 csp *)
    iInstr "Hcode".
    set (p0 := encodePermSum (get_p wcsp.(lw))).
    assert (rules_Get.denote (GetP ct2 csp) wcsp.(lw) = Some p0) as Hp0 by done.
    (* Mov ctp COMPARTMENT_STACK_PERMISSIONS *)
    iInstr "Hcode".
    destruct (decide (p0 = COMPARTMENT_STACK_PERMISSIONS)) as [Hp0'|Hp0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ctp ct2 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hctp $Hct2]"
        as "(HPC & Hctp & Hct2)".
      { cbn [jcond_test get_a lw]; case_decide; [done|].
        apply negb_true_iff, Z.eqb_neq; intros Heq; apply Hp0'; rewrite -Heq; reflexivity. }
      { switcher_jump_label ".Lcommon_force_unwind". }
      subst hpost.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [Hcontra _]; rewrite Hp0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp". }
    (* Jne .Lcommon_force_unwind ctp ct2 *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hctp $Hct2]"
      as "(HPC & Hctp & Hct2)".
    { cbn [jcond_test get_a lw]; case_decide; [done|].
      apply negb_false_iff, Z.eqb_eq; rewrite Hp0'; reflexivity. }
    (* GetL ct2 csp *)
    iInstr "Hcode".
    set (g0 := encodeLoc (get_l wcsp.(lw))).
    assert (rules_Get.denote (GetL ct2 csp) wcsp.(lw) = Some g0) as Hg0 by done.
    (* Mov ctp COMPARTMENT_STACK_LOCALITY *)
    iInstr "Hcode".
    destruct (decide (g0 = COMPARTMENT_STACK_LOCALITY)) as [Hg0'|Hg0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ctp ct2 *)
      iInstrApply "Hcode" wp_jcond_success_jmp_r_r with "[$HPC $Hctp $Hct2]"
        as "(HPC & Hctp & Hct2)".
      { cbn [jcond_test get_a lw]; case_decide; [done|].
        apply negb_true_iff, Z.eqb_neq; intros Heq; apply Hg0'; rewrite -Heq; reflexivity. }
      { switcher_jump_label ".Lcommon_force_unwind". }
      subst hpost.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [_ Hcontra]; rewrite Hg0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp". }
    (* Jne .Lcommon_force_unwind ctp ct2 *)
    iInstrApply "Hcode" wp_jcond_success_next_r_r with "[$HPC $Hctp $Hct2]"
      as "(HPC & Hctp & Hct2)".
    { cbn [jcond_test get_a lw]; case_decide; [done|].
      apply negb_false_iff, Z.eqb_eq; rewrite Hg0'; reflexivity. }
    switcher_change_pc_label ".Lswitch_entry_first_spill".
    rewrite Hg0'.
    subst hpost.
    iApply "Hpost"; iLeft.
    iFrame "HPC Hcsp Hct2 Hctp".
    iPureIntro; split; [rewrite Hp0 | rewrite Hg0]; f_equal; lia.
  Qed.

End Switch_Csp_Check.
