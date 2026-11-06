From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_compiled_spec_states.

(** * Compiled cmdc, blocks 1 and 5: calls to the switcher

    For the call [c], the block fetches the entry point of the callee in
    [ct1], the entry point of the switcher in [ct2], and jumps to the
    switcher. The group ends at the entry point of the switcher, with the
    return address of the call in [cra]. *)

Section CMDC_Compiled_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  (** The proof of [cmdc_compiled_call_blocks_2_spec], for the call whose
      block starts at the label [l_call], fetches the callee from the
      import [n], and returns at [l_ret]: the code of the two calls only
      differs by the import of the callee. *)
  #[local] Ltac cmdc_compiled_call_blocks_proof l_call n l_ret pc_a pc_b :=
    let hcont := fresh "hcont" in
    let a_call := fresh "a_call" in
    let Ha_call := fresh "Ha_call" in
    focus_block (cmdc_compiled_block l_call) "Hcode_main" of cmdc_compiled_main_blocks
      at pc_a as a_call Ha_call "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    (* Fetch the entry point of the callee *)
    (* Auipcc ct1 (-17), resp. Auipcc ct1 (-30) *)
    iInstr "Hcode";
    [jump_to (pc_b ^+ n) |];
    (* CLoad ct1 ct1 0 *)
    iInstr "Hcode";
    [ eapply disjoint_from_shadow_not_in; eauto; rewrite /withinBounds; solve_addr
    | rewrite /withinBounds; solve_addr
    | ];
    (* Fetch the entry point of the switcher *)
    (* Auipcc ct2 (-21), resp. Auipcc ct2 (-35) *)
    iInstr "Hcode";
    [jump_to (pc_b ^+ 0) |];
    (* CLoad ct2 ct2 0 *)
    iInstr "Hcode";
    [ eapply disjoint_from_shadow_not_in; eauto; rewrite /withinBounds; solve_addr
    | apply switcher_call_sentry_not_heap
    | ];
    iEval (rewrite !lload_word_no_dl_dro //) in "Hct1 Hct2";
    (* Jump to the switcher *)
    (* Jalr cra ct2 *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    assert (a_call ^+ 5 = pc_a ^+ cmdc_compiled_label_offset l_ret) as ->
      by (offsets_compute; solve_addr);
    iApply "Hpost"; iFrame "∗ Hcode_main".

  Lemma cmdc_compiled_call_blocks_2_spec (c : cmdc_compiled_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (wct1 wct2 wcra : LWord) (b : InterruptStatus) :
    cmdc_compiled_code_bounds pc_b pc_e pc_a B_f C_g ->
    route_pre th b ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e
      (pc_a ^+ cmdc_compiled_label_offset (cmdc_compiled_call_label c)) ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    cra ↦ᵣ[th] wcra ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ cmdc_compiled_call_import c) ↦ₐ□
      WSealed ot_switcher (cmdc_compiled_call_target c B_f C_g) ∗
    codefrag_pers pc_a cmdc_compiled_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ ( PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ct1 ↦ᵣ[th] WSealed ot_switcher (cmdc_compiled_call_target c B_f C_g) ∗
        ct2 ↦ᵣ[th] switcher_entry_call ∗
        cra ↦ᵣ[th] Sentry (ret_kind b) RX Global pc_b pc_e
          (pc_a ^+ cmdc_compiled_label_offset (cmdc_compiled_return_label c)) ∗
        pc_b ↦ₐ□ switcher_entry_call ∗
        (pc_b ^+ cmdc_compiled_call_import c) ↦ₐ□
          WSealed ot_switcher (cmdc_compiled_call_target c B_f C_g) ∗
        codefrag_pers pc_a cmdc_compiled_main_code ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        held (th := th) InterruptDisabled
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    destruct c; cbn [cmdc_compiled_call_label cmdc_compiled_return_label
                       cmdc_compiled_call_import cmdc_compiled_call_target].
    all: iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap
                   & HC_g_nonheap) Hroute)
      "(HPC & Hct1 & Hct2 & Hcra & Himport_switcher & Himport_target
      & Hcode_main & Hmie & Hheld & Hpost)".
    all: rewrite /cmdc_compiled_main_run_offset in Himports_contiguous.
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_compiled_main_code "Hcode_main".
    all: rewrite /switcher_entry_call.
    - (* Call to [B.f], block 1 *)
      cmdc_compiled_call_blocks_proof
        ".Lcmdc_run_call_B_f"%string 2 ".Lcmdc_run_return_B_f"%string pc_a pc_b.
    - (* Call to [C.g], block 5 *)
      cmdc_compiled_call_blocks_proof
        ".Lcmdc_run_call_C_g"%string 3 ".Lcmdc_run_return_C_g"%string pc_a pc_b.
  Qed.

End CMDC_Compiled_Call_Blocks_2.
