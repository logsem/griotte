From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 0-1: checks on the stack pointer

    Blocks 0 and 1 check that [csp] is a [RWL] [Local] capability. When the
    checks fail, the execution jumps to block 18 (see
    [switcher_call_blocks_6]). *)

Section Switcher_Call_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_blocks_1_spec (wcsp wct2 wctp : LWord) :
    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    csp ↦ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    switcher_code ∗
    ▷ ( ( ⌜ switcher_csp_checked wcsp ⌝ ∗
          PC ↦ₚ switcher_label_pc ".Lswitcher_entry_first_spill" ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) ∗
          switcher_code )
        ∨
        ( ⌜ ¬ switcher_csp_checked wcsp ⌝ ∗
          ∃ zct2 zctp,
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt zctp ∗
          switcher_code )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcsp & Hct2 & Hctp & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 0: check the permission of csp *)
    focus_block_0 "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    (* GetP ct2 csp *)
    iInstr "Hcode".
    set (p0 := encodePermSum (get_p wcsp.(lw))).
    assert (rules_Get.denote (GetP ct2 csp) wcsp.(lw) = Some p0) as Hp0 by done.
    (* Mov ctp (encodePerm RWL) *)
    iInstr "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode".
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|Hp0']; cycle 1.
    {
      (* Jne (".Lcommon_force_unwind")%asm ct2 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hct2]" as "(HPC & Hct2)".
      { apply negb_true_iff, Z.eqb_neq. intros Hcontr; cbn in Hcontr; done. }
      { transitivity (Some (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a); auto.
        offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [Hcontra _]; rewrite Hp0 in Hcontra; simplify_eq; lia. }
      iExists _,_. iFrame "∗ Hswitcher".
    }
    rewrite Hp0'.
    (* Jne (".Lcommon_force_unwind")%asm ct2 0 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 1: check the locality of csp *)
    focus_block 1 "Hswitcher" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls";
      iHide "Hswitcher" as hswitcher.
    (* GetL ct2 csp *)
    iInstr "Hcode".
    set (g0 := encodeLoc (get_l wcsp.(lw))).
    assert (rules_Get.denote (GetL ct2 csp) wcsp.(lw) = Some g0) as Hg0 by done.
    (* Mov ctp (encodeLoc Local) *)
    iInstr "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode".
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|Hg0']; cycle 1.
    {
      (* Jne (".Lcommon_force_unwind")%asm ct2 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hct2]" as "(HPC & Hct2)".
      { apply negb_true_iff, Z.eqb_neq. intros Hcontr; cbn in Hcontr; done. }
      { transitivity (Some (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a); auto.
        offsets_compute; solve_addr. }
      iEval (simplify_map_eq) in "HPC".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [_ Hcontra]; rewrite Hg0 in Hcontra; simplify_eq; lia. }
      iExists _,_. iFrame "∗ Hswitcher".
    }
    rewrite Hg0'.
    (* Jne (".Lcommon_force_unwind")%asm ct2 0 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    iApply "Hpost"; iLeft.
    iFrame "∗ Hswitcher".
    switcher_change_pc (switcher_label_offset ".Lswitcher_entry_first_spill").
    iFrame. iPureIntro; split; [rewrite Hp0 | rewrite Hg0]; f_equal; lia.
  Qed.



End Switcher_Call_Blocks_1.
