From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 0-1: checks on the stack pointer

    Blocks 0 and 1 check that [csp] is a [RWL] [Local] capability. When the
    checks fail, the execution jumps to block 17 (see
    [switcher_call_blocks_6]). *)

Section Switcher_Call_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_blocks_1_spec (wcsp wct2 wctp : Word) :
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    csp ↦ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ wctp ∗
    switcher_code ∗
    ▷ ( ( ⌜ switcher_csp_checked wcsp ⌝ ∗
          PC ↦ᵣ switcher_block_pc 2 ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) ∗
          switcher_code )
        ∨
        ( ⌜ ¬ switcher_csp_checked wcsp ⌝ ∗
          ∃ zct2 zctp,
          PC ↦ᵣ switcher_block_pc 17 ∗
          csp ↦ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt zctp ∗
          switcher_code )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hcsp & Hct2 & Hctp & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".

    (* Block 0: check the permission of csp *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* GetP ct2 csp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* Mov ctp (encodePerm RWL) *)
    iInstr "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode".
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|Hp0']; cycle 1.
    {
      (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      { transitivity (Some (a_switcher_call ^+ switcher_block_offset 17)%a); auto.
        offsets_compute; solve_addr. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [Hcontra _]; rewrite Hp0 in Hcontra; simplify_eq; lia. }
      iExists _,_. iFrame.
    }
    rewrite Hp0'.
    (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* Block 1: check the locality of csp *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls";
      iHide "Hcls" as hcont.
    (* GetL ct2 csp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%g0 & %Hg0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* Mov ctp (encodeLoc Local) *)
    iInstr "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr "Hcode".
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|Hg0']; cycle 1.
    {
      (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      { transitivity (Some (a_switcher_call ^+ switcher_block_offset 17)%a); auto.
        offsets_compute; solve_addr. }
      iIntros "!> (HPC & Hi & Hct2)".
      iEval (simplify_map_eq) in "HPC".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      iApply "Hpost"; iRight.
      iSplit.
      { iPureIntro; intros [_ Hcontra]; rewrite Hg0 in Hcontra; simplify_eq; lia. }
      iExists _,_. iFrame.
    }
    rewrite Hg0'.
    (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    assert (p0 = encodePerm RWL)%Z by lia; subst p0.
    assert (g0 = encodeLoc Local)%Z by lia; subst g0.
    iApply "Hpost"; iLeft.
    iFrame "∗".
    switcher_change_pc (switcher_block_offset 2).
    iFrame. iPureIntro; split; done.
  Qed.



End Switcher_Call_Blocks_1.
