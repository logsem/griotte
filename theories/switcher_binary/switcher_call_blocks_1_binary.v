From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Call routine, blocks 0-1: checks on the stack pointer, binary model

    Blocks 0 and 1 check that [csp] is a [RWL] [Local] capability, in both
    runs, which hold the same stack pointer. When the checks fail, the
    execution jumps to block 17 (see [switcher_call_blocks_6_binary]). *)

Section Switcher_Call_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Lemma switcher_call_block_0_spec
    pc_a a_tgt
    wcsp wct2 swct2 wctp swctp :
    let switcher_instrs_0 := switcher_instrs_n 0 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length switcher_instrs_0)%a ->
    (pc_a ^+ 3 + 144)%a = Some a_tgt ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    codefrag pc_a switcher_instrs_0 ∗
    spec_codefrag pc_a switcher_instrs_0 ∗
    ▷ ( ( ⌜ rules_Get.denote (GetP ct2 csp) wcsp = Some (encodePerm RWL) ⌝ ∗
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ length switcher_instrs_0)%a ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ length switcher_instrs_0)%a ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt 0 ∗
          ct2 ↣ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodePerm RWL) ∗
          ctp ↣ᵣ WInt (encodePerm RWL) ∗
          codefrag pc_a switcher_instrs_0 ∗
          spec_codefrag pc_a switcher_instrs_0 )
        ∨
        ( ⌜ rules_Get.denote (GetP ct2 csp) wcsp ≠ Some (encodePerm RWL) ⌝ ∗
          ∃ zct2,
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_tgt ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_tgt ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ct2 ↣ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt (encodePerm RWL) ∗
          ctp ↣ᵣ WInt (encodePerm RWL) ∗
          codefrag pc_a switcher_instrs_0 ∗
          spec_codefrag pc_a switcher_instrs_0 )
        -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_0; subst switcher_instrs_0.
    iIntros (Hsub_reg Htgt) "(#Hspec & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* GetP ct2 csp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* GetP ct2 csp *)
    iInstr_spec "Hscode".
    { exact Hp0. }
    (* Mov ctp (encodePerm RWL) *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    change (match MP with | {| encodePerm := e |} => e end) with (@encodePerm MP).
    replace ( (if decide (ctp = cnull) then 0 else encodePerm RWL)%Z )
      with (encodePerm RWL) by (destruct (decide _); done).
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|Hp0']; cycle 1.
    { (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: intros Hcontr; inversion Hcontr; done.
      iApply "Hpost"; iRight.
      iSplit; first (iPureIntro; rewrite Hp0; intros Hcontra; simplify_eq; lia).
      iExists _; iFrame. }
    rewrite Hp0'.
    (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply "Hpost"; iLeft.
    assert (p0 = encodePerm RWL)%Z as -> by lia.
    iFrame. done.
  Qed.

  Lemma switcher_call_block_1_spec
    pc_a a_tgt
    wcsp wct2 swct2 wctp swctp :
    let switcher_instrs_1 := switcher_instrs_n 1 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length switcher_instrs_1)%a ->
    (pc_a ^+ 3 + 140)%a = Some a_tgt ->

    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    codefrag pc_a switcher_instrs_1 ∗
    spec_codefrag pc_a switcher_instrs_1 ∗
    ▷ ( ( ⌜ rules_Get.denote (GetL ct2 csp) wcsp = Some (encodeLoc Local) ⌝ ∗
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ length switcher_instrs_1)%a ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (pc_a ^+ length switcher_instrs_1)%a ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt 0 ∗
          ct2 ↣ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) ∗
          ctp ↣ᵣ WInt (encodeLoc Local) ∗
          codefrag pc_a switcher_instrs_1 ∗
          spec_codefrag pc_a switcher_instrs_1 )
        ∨
        ( ⌜ rules_Get.denote (GetL ct2 csp) wcsp ≠ Some (encodeLoc Local) ⌝ ∗
          ∃ zct2,
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_tgt ∗
          PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_tgt ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ct2 ↣ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) ∗
          ctp ↣ᵣ WInt (encodeLoc Local) ∗
          codefrag pc_a switcher_instrs_1 ∗
          spec_codefrag pc_a switcher_instrs_1 )
        -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    intros switcher_instrs_1; subst switcher_instrs_1.
    iIntros (Hsub_reg Htgt) "(#Hspec & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* GetL ct2 csp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%g0 & %Hg0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* GetL ct2 csp *)
    iInstr_spec "Hscode".
    { exact Hg0. }
    (* Mov ctp (encodeLoc Local) *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Sub ct2 ct2 ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    change (match MP with | {| encodeLoc := e |} => e end) with (@encodeLoc MP).
    replace ( (if decide (ctp = cnull) then 0 else encodeLoc Local)%Z )
      with (encodeLoc Local) by (destruct (decide _); done).
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|Hg0']; cycle 1.
    { (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: intros Hcontr; inversion Hcontr; done.
      iApply "Hpost"; iRight.
      iSplit; first (iPureIntro; rewrite Hg0; intros Hcontra; simplify_eq; lia).
      iExists _; iFrame. }
    rewrite Hg0'.
    (* Jnz (".Lcommon_force_unwind")%asm ct2 *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply "Hpost"; iLeft.
    assert (g0 = encodeLoc Local)%Z as -> by lia.
    iFrame. done.
  Qed.

  (** Blocks 0-1: check that the stack pointer is a [RWL] [Local]
      capability. *)
  Lemma switcher_call_blocks_1_spec (wcsp wct2 swct2 wctp swctp : Word) :
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    csp ↦ᵣ wcsp ∗
    csp ↣ᵣ wcsp ∗
    ct2 ↦ᵣ wct2 ∗
    ct2 ↣ᵣ swct2 ∗
    ctp ↦ᵣ wctp ∗
    ctp ↣ᵣ swctp ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ( ⌜ switcher_csp_checked wcsp ⌝ ∗
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ switcher_block_pc 2 ∗
          PC ↣ᵣ switcher_block_pc 2 ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt 0 ∗
          ct2 ↣ᵣ WInt 0 ∗
          ctp ↦ᵣ WInt (encodeLoc Local) ∗
          ctp ↣ᵣ WInt (encodeLoc Local) ∗
          switcher_code ∗
          switcher_spec_code )
        ∨
        ( ⌜ ¬ switcher_csp_checked wcsp ⌝ ∗
          ∃ zct2 zctp,
          ⤇ Seq (Instr Executable) ∗
          PC ↦ᵣ switcher_block_pc 17 ∗
          PC ↣ᵣ switcher_block_pc 17 ∗
          csp ↦ᵣ wcsp ∗
          csp ↣ᵣ wcsp ∗
          ct2 ↦ᵣ WInt zct2 ∗
          ct2 ↣ᵣ WInt zct2 ∗
          ctp ↦ᵣ WInt zctp ∗
          ctp ↣ᵣ WInt zctp ∗
          switcher_code ∗
          switcher_spec_code )
        -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros "(#Hspec & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp
      & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".

    (* Block 0: check the permission of csp *)
    focus_block_0_lockstep "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_0_spec _ (a_switcher_call ^+ switcher_block_offset 17)%a with
      "[- $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct2 $Hsct2 $Hctp $Hsctp $Hcode $Hscode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "[(%Hp & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp & Hcode & Hscode)
      | (%Hp & %zct2 & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp & Hcode & Hscode)]";
      subst hcont hscont;
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode"; cycle 1.
    { iApply "Hpost"; iRight.
      iSplit; first (iPureIntro; intros [? _]; done).
      iExists _, _; iFrame. }

    (* Block 1: check the locality of csp *)
    switcher_focus_block_lockstep 1 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_1_spec _ (a_switcher_call ^+ switcher_block_offset 17)%a with
      "[- $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct2 $Hsct2 $Hctp $Hsctp $Hcode $Hscode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "[(%Hl & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp & Hcode & Hscode)
      | (%Hl & %zct2' & Hj & HPC & HsPC & Hcsp & Hscsp & Hct2 & Hsct2 & Hctp & Hsctp & Hcode & Hscode)]";
      subst hcont hscont;
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode"; cycle 1.
    { iApply "Hpost"; iRight.
      iSplit; first (iPureIntro; intros [_ ?]; done).
      iExists _, _; iFrame. }
    switcher_change_pc (switcher_block_offset 2).
    iApply "Hpost"; iLeft.
    iFrame. done.
  Qed.

  (** Block 0 fails when the stack pointer is sealed. *)
  Lemma switcher_call_blocks_1_sealed_fail_spec (o : OType) (sb : Sealable) (wct2 : Word) :
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    csp ↦ᵣ WSealed o sb ∗
    ct2 ↦ᵣ wct2 ∗
    switcher_code
    ⊢ switcher_wp.
  Proof.
    iIntros "(HPC & Hcsp & Hct2 & Hcode)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hcode".
    focus_block_0 "Hcode" as "Hcode" "Hcls".
    (* GetP ct2 csp *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & %Hcap & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr"; done. }
    done.
  Qed.

End Switcher_Call_Blocks_1.
