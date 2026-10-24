From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_call_states.

(** * Call routine: checks on the stack pointer

    [.Lswitch_csp_check] checks that [csp] has the permission [RWL], and
    [.Lswitcher_csp_check_loc] that it is [Local]. When a check fails, the
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
          ct2 ↦ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) )
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
    iAssert switcher_code as "Hswitcher_loc"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_csp_check" "Hswitcher" as "Hcode".
    (* The label is at offset 0: [iInstr] simplifies its address *)
    rewrite switcher_call_entry_label.
    repeat match goal with
      | Hfact : context [switcher_label_offset ".Lswitch_csp_check"] |- _ =>
          rewrite switcher_call_entry_label in Hfact
      end.
    (* GetP ct2 csp *)
    iInstr "Hcode".
    set (p0 := encodePermSum (get_p wcsp.(lw))).
    assert (rules_Get.denote (GetP ct2 csp) wcsp.(lw) = Some p0) as Hp0 by done.
    (* Mov ctp (encodePerm RWL) *)
    iInstr "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode".
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|Hp0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ct2 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hct2]" as "(HPC & Hct2)".
      { apply negb_true_iff, Z.eqb_neq. intros Hcontr; cbn in Hcontr; done. }
      { switcher_jump_label ".Lcommon_force_unwind". }
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [Hcontra _]; rewrite Hp0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp". }
    rewrite Hp0'.
    (* Jne .Lcommon_force_unwind ct2 0 *)
    iInstr "Hcode".
    switcher_open_label ".Lswitcher_csp_check_loc" "Hswitcher_loc" as "Hcode_loc".
    (* GetL ct2 csp *)
    iInstr "Hcode_loc".
    set (g0 := encodeLoc (get_l wcsp.(lw))).
    assert (rules_Get.denote (GetL ct2 csp) wcsp.(lw) = Some g0) as Hg0 by done.
    (* Mov ctp (encodeLoc Local) *)
    iInstr "Hcode_loc".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode_loc".
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|Hg0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ct2 0 *)
      iInstrApply "Hcode_loc" wp_jnez_success_jmp_z with "[$HPC $Hct2]" as "(HPC & Hct2)".
      { apply negb_true_iff, Z.eqb_neq. intros Hcontr; cbn in Hcontr; done. }
      { switcher_jump_label ".Lcommon_force_unwind". }
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [_ Hcontra]; rewrite Hg0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp". }
    rewrite Hg0'.
    (* Jne .Lcommon_force_unwind ct2 0 *)
    iInstr "Hcode_loc".
    switcher_change_pc_label ".Lswitch_entry_first_spill".
    iApply "Hpost"; iLeft.
    iFrame "HPC Hcsp Hct2 Hctp".
    iPureIntro; split; [rewrite Hp0 | rewrite Hg0]; f_equal; lia.
  Qed.

End Switch_Csp_Check.
