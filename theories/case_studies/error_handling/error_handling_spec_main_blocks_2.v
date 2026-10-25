From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * [main], blocks 7-14: the first two asserts, and the call to
    [stats_read] with the untagged capability of [x]

    From the return of the first call to [stats_read], block 7 halts when
    the call returned [ENOTENOUGHTRUSTEDSTACK] (the trusted stack is
    exhausted), and block 8 asserts that it returned [X_INIT]
    ([main_check_1_spec]). Block 9 puts the capability of [x] without its
    tag in [ca0], blocks 10 and 11 fetch the entry points of the switcher
    and of [stats_read], and block 12 jumps to the switcher
    ([main_call_read_2_spec]). From its return, blocks 13 and 14 check
    that it returned [ECOMPARTMENTFAIL] ([main_check_2_spec]). *)

Section Error_Handling_Main_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
    {statslayout : statsLayout} {statslayoutWf : statsLayoutWf}
  .

  Lemma main_check_1_spec
    (pc_b pc_e pc_a : Addr) (v : Z)
    (wct0 wct1 wct2 wca2 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    v = ENOTENOUGHTRUSTEDSTACK ∨ v = X_INIT ->
    assert_static b_assert e_assert a_flag ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_read_1")%a ∗
    ca0 ↦ᵣ WInt v ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ca2 ↦ᵣ wca2 ∗
    cra ↦ᵣ wcra ∗
    (pc_b ^+ 1)%a ↦ₐ□ main_assert_entry ∗
    codefrag_pers pc_a error_handling_main_code ∗
    ▷ (na_own cerise_nais ⊤ ∗
        PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_2")%a ∗
        ca0 ↦ᵣ WInt X_INIT ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ca2 ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wcra ∗
        codefrag_pers pc_a error_handling_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hv)
      "(#Hassert & Hna & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
      & #Himport_assert & #Hcode_main & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /main_assert_entry.

    (* Block 7: halt on trusted-stack exhaustion *)
    focus_block (main_block ".Lmain_ret_read_1") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_check Ha_check "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct Hv as [-> | ->].
    { (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna". }
    (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr "Hcode".
    (* Mov ct0 ca0 *)
    iInstr "Hcode".
    (* Mov ct1 X_INIT *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: assert (ct0 == ct1) *)
    focus_block (main_block ".Lmain_assert_1") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra $Hcode $Himport_assert]");
      auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & _ & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_assert ^+ length (assert_instrs (-18) ct2 ca2))%a =
              (pc_a ^+ main_label_offset ".Lmain_arg_2")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma main_call_read_2_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wca0 wctp wct1 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_2")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ□ main_switcher_entry ∗
    (pc_b ^+ 3)%a ↦ₐ□ WSealed ot_switcher (STATS_read Global) ∗
    codefrag_pers pc_a error_handling_main_code ∗
    ▷ (∀ mie, PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WCap false RW Global cgp_b cgp_e cgp_b ∗
        ctp ↦ᵣ main_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher (STATS_read Global) ∗
        cra ↦ᵣ WSentry (ret_kind mie) true RX Global pc_b pc_e
                 (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a ∗
        codefrag_pers pc_a error_handling_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap))
      "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra
      & #Himport_switcher & #Himport_read & #Hcode_main & Hpost)".
    assert (is_heap_cap (WSealed ot_switcher (STATS_read Global)) = false) as Hsealed_nonheap
      by (apply sealed_cap_nonheap, stats_export_base_not_heap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /main_switcher_entry.

    (* Block 9: the untagged capability of [x] *)
    focus_block (main_block ".Lmain_arg_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_arg Ha_arg "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* ClearTag ca0 cgp *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 10: fetch the entry point of the switcher *)
    focus_block (main_block ".Lmain_fetch_switcher_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _
              (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
              with "[- $HPC $Hctp $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & _)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: fetch the entry point of [stats_read] *)
    focus_block (main_block ".Lmain_fetch_read_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 3 with "[- $HPC $Hct1 $Hcode $Himport_read]"); eauto.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & _)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: jump to the switcher *)
    focus_block (main_block ".Lmain_call_read_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma main_check_2_spec
    (pc_b pc_e pc_a : Addr) (v : Z)
    (wct0 wct1 wct2 wca2 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    v = ENOTENOUGHTRUSTEDSTACK ∨ v = ECOMPARTMENTFAIL ->
    assert_static b_assert e_assert a_flag ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a ∗
    ca0 ↦ᵣ WInt v ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ca2 ↦ᵣ wca2 ∗
    cra ↦ᵣ wcra ∗
    (pc_b ^+ 1)%a ↦ₐ□ main_assert_entry ∗
    codefrag_pers pc_a error_handling_main_code ∗
    ▷ (na_own cerise_nais ⊤ ∗
        PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_3")%a ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WInt 0 ∗
        ct2 ↦ᵣ WInt 0 ∗
        ca2 ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wcra ∗
        codefrag_pers pc_a error_handling_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hv)
      "(#Hassert & Hna & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
      & #Himport_assert & #Hcode_main & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /main_assert_entry.

    (* Block 13: halt on trusted-stack exhaustion *)
    focus_block (main_block ".Lmain_ret_read_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_check Ha_check "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct Hv as [-> | ->].
    { (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
      iInstr "Hcode".
      (* Halt *)
      iInstr "Hcode".
      wp_end; iIntros (_); iFrame "Hna". }
    (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
    iInstr "Hcode".
    (* Mov ct0 ca0 *)
    iInstr "Hcode".
    (* Mov ct1 ECOMPARTMENTFAIL *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 14: assert (ct0 == ct1) *)
    focus_block (main_block ".Lmain_assert_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra $Hcode $Himport_assert]");
      auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & _ & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_assert ^+ length (assert_instrs (-35) ct2 ca2))%a =
              (pc_a ^+ main_label_offset ".Lmain_arg_3")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End Error_Handling_Main_Blocks_2.
