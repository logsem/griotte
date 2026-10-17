From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 0-2: call to the adversary [C.adv]

    Block 0 fetches the entry point of the switcher in [ct0], block 1
    fetches the entry point of [C.adv] in [ct1], and the first instruction
    of block 2 jumps to the switcher. The group ends at the entry point of
    the switcher, with the return address of the call in [cra]. *)

Section SO_Run_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_run_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (wct0 wct1 wcra : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ□ so_switcher_entry ∗
    (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher C_f ∗
    codefrag_pers pc_a so_main_code ∗
    ▷ (PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ct0 ↦ᵣ so_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        cra ↦ᵣ WSentry (ret_kind InterruptDisabled) true RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_run_halt")%a ∗
        pc_b ↦ₐ□ so_switcher_entry ∗
        (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher C_f ∗
        codefrag_pers pc_a so_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hsealed_nonheap)
      "(HPC & Hct0 & Hct1 & Hcra & Himport_switcher & Himport_C_f
      & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.
    rewrite /so_switcher_entry.

    (* Block 0: fetch the entry point of the switcher *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
      (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
      with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 1: fetch the entry point of [C.adv] *)
    focus_block (so_block ".Lso_run_fetch_adv") "Hcode_main" of so_main_blocks at pc_a as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcode $Himport_C_f]"); eauto; try done.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: jump to the switcher *)
    focus_block (so_block ".Lso_run_call") "Hcode_main" of so_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ so_label_offset ".Lso_run_halt")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End SO_Run_Blocks_1.
