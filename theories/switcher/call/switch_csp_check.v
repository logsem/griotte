From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_call_states.

(** * Call routine: checks on the stack pointer

    [.Lswitch_csp_check] checks that [csp] has the permission [RWL], that
    it is [Local], and that its base is the value of MSHWMB, the base of the
    thread's stack. When a check fails, the execution jumps to
    [.Lcommon_force_unwind]. *)

Section Switch_Csp_Check.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The call entry point is the label [.Lswitch_csp_check]. *)
  Lemma switcher_call_entry_label :
    (a_switcher_call ^+ switcher_label_offset ".Lswitch_csp_check")%a = a_switcher_call.
  Proof. switcher_addr_eq. Qed.

  (** From [.Lswitch_csp_check]: when [csp] is a [RWL] [Local] capability
      whose base is the value [mshwmb_v] of MSHWMB, the PC is at
      [.Lswitch_entry_first_spill]; otherwise, at [.Lcommon_force_unwind]. *)
  Lemma switch_csp_check_spec (wcsp wct2 wctp : LWord) (mshwmb_v : Z) :
    PC ↦ₚ[th] switcher_label_pc ".Lswitch_csp_check" ∗
    csp ↦ᵣ[th] wcsp ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] wctp ∗
    mshwmb ↦ₜ[th] mshwmb_v ∗
    switcher_code ∗
    ▷ ( ( ⌜ switcher_csp_checked wcsp ⌝ ∗
          ⌜ get_b wcsp.(lw) = mshwmb_v ⌝ ∗
          PC ↦ₚ[th] switcher_label_pc ".Lswitch_entry_first_spill" ∗
          csp ↦ᵣ[th] wcsp ∗
          ct2 ↦ᵣ[th] WInt mshwmb_v ∗
          ctp ↦ᵣ[th] WInt mshwmb_v ∗
          mshwmb ↦ₜ[th] mshwmb_v )
        ∨
        ( ⌜ ¬ (switcher_csp_checked wcsp ∧ get_b wcsp.(lw) = mshwmb_v) ⌝ ∗
          ∃ zct2 zctp,
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ[th] wcsp ∗
          ct2 ↦ᵣ[th] WInt zct2 ∗
          ctp ↦ᵣ[th] WInt zctp ∗
          mshwmb ↦ₜ[th] mshwmb_v )
        -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros "(HPC & Hcsp & Hct2 & Hctp & Hmshwmb & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitch_csp_check" "Hswitcher" as "Hcode".
    switcher_hide "Hpost" as hpost.
    (* GetP ct2 csp *)
    iInstr "Hcode".
    set (p0 := encodePermSum (get_p wcsp.(lw))).
    assert (get_denote (GetP ct2 csp) wcsp.(lw) = Some p0) as Hp0 by done.
    (* Mov ctp COMPARTMENT_STACK_PERMISSIONS *)
    iInstr "Hcode".
    destruct (decide (p0 = COMPARTMENT_STACK_PERMISSIONS)) as [Hp0'|Hp0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ctp ct2 *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      subst hpost.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [ [Hcontra _] _]; rewrite Hp0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp Hmshwmb". }
    (* Jne .Lcommon_force_unwind ctp ct2 *)
    iInstr "Hcode".
    (* GetL ct2 csp *)
    iInstr "Hcode".
    set (g0 := encodeLoc (get_l wcsp.(lw))).
    assert (get_denote (GetL ct2 csp) wcsp.(lw) = Some g0) as Hg0 by done.
    (* Mov ctp COMPARTMENT_STACK_LOCALITY *)
    iInstr "Hcode".
    destruct (decide (g0 = COMPARTMENT_STACK_LOCALITY)) as [Hg0'|Hg0']; cycle 1.
    { (* Jne .Lcommon_force_unwind ctp ct2 *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      subst hpost.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [ [_ Hcontra] _]; rewrite Hg0 in Hcontra; simplify_eq; lia. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp Hmshwmb". }
    (* Jne .Lcommon_force_unwind ctp ct2 *)
    iInstr "Hcode".
    assert (switcher_csp_checked wcsp) as Hchecked.
    { split; [rewrite Hp0 | rewrite Hg0]; f_equal; lia. }
    (* GetB ct2 csp *)
    iInstr "Hcode".
    (* SpecialRW ctp MSHWMB cnull *)
    iInstrApply "Hcode" wp_csrr_mshwmb with "[$HPC $Hctp $Hmshwmb]"
      as "(HPC & Hctp & Hmshwmb)".
    destruct (decide (get_b wcsp.(lw) = mshwmb_v)) as [Hb|Hb]; cycle 1.
    { (* Jne .Lcommon_force_unwind ctp ct2 *)
      iInstr "Hcode".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      subst hpost.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [_ Hcontra]; done. }
      iExists _, _. iFrame "HPC Hcsp Hct2 Hctp Hmshwmb". }
    (* Jne .Lcommon_force_unwind ctp ct2 *)
    iInstr "Hcode".
    switcher_change_pc_label ".Lswitch_entry_first_spill".
    rewrite Hb.
    subst hpost.
    iApply "Hpost"; iLeft.
    by iFrame "HPC Hcsp Hct2 Hctp Hmshwmb".
  Qed.

End Switch_Csp_Check.
