From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, blocks 1-3 and 6-8: calls to the switcher

    For the call [c], the first block fetches the entry point of the
    switcher in [ctp], the second block fetches the entry point of the
    callee in [ct1], and the first instruction of the third block jumps to
    the switcher. The group ends at the entry point of the switcher, with
    the return address of the call in [cra]. *)

Section CMDC_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The proof of [cmdc_call_blocks_2_spec], for the call whose blocks
      start at the labels [l_call], [l_fetch] and [l_jump], and that returns
      at [l_ret]: the code of the two calls only differs by the import of
      the callee. *)
  #[local] Ltac cmdc_call_blocks_proof l_call l_fetch l_jump l_ret pc_a pc_b :=
    let hcont := fresh "hcont" in
    let a_fetch1 := fresh "a_fetch1" in
    let a_fetch2 := fresh "a_fetch2" in
    let a_call := fresh "a_call" in
    let Ha_fetch1 := fresh "Ha_fetch1" in
    let Ha_fetch2 := fresh "Ha_fetch2" in
    let Ha_call := fresh "Ha_call" in
    (* Fetch the entry point of the switcher *)
    focus_block (cmdc_block l_call) "Hcode_main" of cmdc_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      with "[- $HPC $Hctp $Hcode]");
    eauto using switcher_call_sentry_not_heap; try done;
    [offsets_compute; solve_addr|solve_addr|];
    replace (pc_b ^+ 0)%a with pc_b by solve_addr;
    iFrame "Himport_switcher";
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)";
    iEval (cbn) in "Hctp";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Fetch the entry point of the callee *)
    focus_block (cmdc_block l_fetch) "Hcode_main" of cmdc_main_blocks at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcode $Himport_target]");
    eauto; try done; [offsets_compute; solve_addr|solve_addr|];
    iNext; iIntros "(HPC & Hct1 & _ & Himport_target)";
    iEval (cbn) in "Hct1";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Jump to the switcher *)
    focus_block (cmdc_block l_jump) "Hcode_main" of cmdc_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    (* Jalr cra ctp *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    assert ((a_call ^+ 1)%a = (pc_a ^+ cmdc_label_offset l_ret)%a) as ->
      by (offsets_compute; solve_addr);
    iApply "Hpost"; iFrame "∗ Hcode_main".

  Lemma cmdc_call_blocks_2_spec (c : cmdc_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (wctp wct1 wcra : LWord) :
    cmdc_code_bounds pc_b pc_e pc_a B_f C_g ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ cmdc_label_offset (cmdc_call_label c))%a ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ□ cmdc_switcher_entry ∗
    (pc_b ^+ cmdc_call_import c)%a ↦ₐ□ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
    codefrag_pers pc_a cmdc_main_code ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ cmdc_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
        cra ↦ᵣ WSentry true RX Global pc_b pc_e
          (pc_a ^+ cmdc_label_offset (cmdc_return_label c))%a ∗
        pc_b ↦ₐ□ cmdc_switcher_entry ∗
        (pc_b ^+ cmdc_call_import c)%a ↦ₐ□ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
        codefrag_pers pc_a cmdc_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    destruct c; cbn [cmdc_call_label cmdc_return_label cmdc_call_import cmdc_call_target].
    all: iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap
                   & HC_g_nonheap))
      "(HPC & Hctp & Hct1 & Hcra & Himport_switcher & Himport_target
      & Hcode_main & Hpost)".
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_main_code "Hcode_main".
    all: rewrite /cmdc_switcher_entry.
    - (* Call to [B.f], blocks 1-3 *)
      cmdc_call_blocks_proof
        ".Lcmdc_call_B"%string ".Lcmdc_fetch_B_f"%string
        ".Lcmdc_jump_B"%string ".Lcmdc_return_B"%string pc_a pc_b.
    - (* Call to [C.g], blocks 6-8 *)
      cmdc_call_blocks_proof
        ".Lcmdc_call_C"%string ".Lcmdc_fetch_C_g"%string
        ".Lcmdc_jump_C"%string ".Lcmdc_return_C"%string pc_a pc_b.
  Qed.

End CMDC_Call_Blocks_2.
