From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import error_handling_spec_states error_handling_spec_main_blocks_3.

(** * [main], blocks 7-14: the first two asserts, and the call to
    [stats_read] with the untagged capability of [x]

    From the return of the first call to [stats_read], block 7 returns
    ([main_return_spec]) when the call returned [ENOTENOUGHTRUSTEDSTACK]
    (the trusted stack is exhausted), and block 8 asserts that it returned [X_INIT]
    ([main_check_1_spec]). Block 9 puts the capability of [x] without its
    tag in [ca0], blocks 10 and 11 fetch the entry points of the switcher
    and of [stats_read], and block 12 jumps to the switcher
    ([main_call_read_2_spec]). From its return, blocks 13 and 14 check
    that it returned [ECOMPARTMENTFAIL] ([main_check_2_spec]). *)

Section Error_Handling_Main_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
    {statslayout : statsLayout} {statslayoutWf : statsLayoutWf}
  .

  Lemma main_check_1_spec
    (pc_b pc_e pc_a : Addr) (v : Z) (cstk : CSTK) (rmap : LReg)
    (wctp wct0 wct1 wct2 wca2 wcra : LWord) (b : InterruptStatus) :
    main_code_bounds pc_b pc_e pc_a ->
    v = ENOTENOUGHTRUSTEDSTACK ∨ v = X_INIT ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ ca0 ; ctp ; ct0 ; ct1 ; ct2 ; ca2 ; cra ; cs0 ]} ->
    route_pre th b ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_read_1")%a ∗
    ca0 ↦ᵣ[th] WInt v ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗
    ◯(CSTK)[th] cstk ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a error_handling_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ (na_own (tpool th) ⊤ ∗
        PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_2")%a ∗
        ca0 ↦ᵣ[th] WInt X_INIT ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        ct2 ↦ᵣ[th] WInt 0 ∗
        ca2 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wcra ∗
        ctp ↦ᵣ[th] wctp ∗
        cs0 ↦ᵣ[th] thread_return_sentry ∗
        regs[th] rmap ∗
        ◯(CSTK)[th] cstk ∗
        codefrag_pers pc_a error_handling_main_code ∗
        MIE ↦ₜ[th] b ∗
        held (th := th) b
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hbounds Hv Hframes Hdom Hroute)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna & HPC & Hca0 & Hctp & Hct0 & Hct1
      & Hct2 & Hca2 & Hcra & Hcs0 & Hrmap & Hcstk & #Himport_assert & #Hcode_main & Hmie & Hheld
      & Hpost)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /assert_entry.

    (* Block 7: return on trusted-stack exhaustion *)
    focus_block (main_block ".Lmain_ret_read_1") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_check Ha_check "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct Hv as [-> | ->].
    { (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
      iInstr "Hcode".
      (* Jmp .Lmain_return *)
      iInstr "Hcode".
      { jump_to (pc_a ^+ main_label_offset ".Lmain_return")%a. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iDestruct (main_check_regs_exit _ _ _ _ Hdom with "Hrmap Hca0 Hct1 Hca2")
        as (rmap_exit) "[%Hdom_exit Hrmap]".
      iApply (main_return_spec with
               "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcs0 $Hcra $Hctp $Hct0 $Hct2
                 $Hrmap $Hcstk $Hcode_main $Hmie $Hheld]");
        [exact Hbounds | exact Hframes | exact Hdom_exit | exact Hroute]. }
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
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra $Hcode $Himport_assert $Hmie $Hheld]");
      auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & Hmie & Hheld & _ & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_assert ^+ length (assert_instrs (-19) ct2 ca2) =
              (pc_a ^+ main_label_offset ".Lmain_arg_2")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma main_call_read_2_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wca0 wctp wct1 wcra : LWord) (b : InterruptStatus) :
    main_code_bounds pc_b pc_e pc_a ->
    route_pre th b ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_2")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ctp ↦ᵣ[th] wctp ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cra ↦ᵣ[th] wcra ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 3) ↦ₐ□ WSealed ot_switcher (STATS_read Global) ∗
    codefrag_pers pc_a error_handling_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ (PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ[th] Cap⁻ RW Global cgp_b cgp_e cgp_b ∗
        ctp ↦ᵣ[th] switcher_entry_call ∗
        ct1 ↦ᵣ[th] WSealed ot_switcher (STATS_read Global) ∗
        cra ↦ᵣ[th] Sentry (ret_kind b) RX Global pc_b pc_e
                 (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a ∗
        codefrag_pers pc_a error_handling_main_code ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        held (th := th) InterruptDisabled
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hroute)
      "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra
      & #Himport_switcher & #Himport_read & #Hcode_main & Hmie & Hheld & Hpost)".
    assert (is_heap_cap (WSealed ot_switcher (STATS_read Global)) = false) as Hsealed_nonheap
      by (apply sealed_cap_nonheap, stats_export_base_not_heap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /switcher_entry_call.

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
              switcher_entry_call
              with "[- $HPC $Hctp $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
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
    assert (a_call ^+ 1 = (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma main_check_2_spec
    (pc_b pc_e pc_a : Addr) (v : Z) (cstk : CSTK) (rmap : LReg)
    (wctp wct0 wct1 wct2 wca2 wcra : LWord) (b : InterruptStatus) :
    main_code_bounds pc_b pc_e pc_a ->
    v = ENOTENOUGHTRUSTEDSTACK ∨ v = ECOMPARTMENTFAIL ->
    cstk.(cstk_frames) = [] ->
    dom rmap = all_registers_s ∖ {[ ca0 ; ctp ; ct0 ; ct1 ; ct2 ; ca2 ; cra ; cs0 ]} ->
    route_pre th b ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_read_2")%a ∗
    ca0 ↦ᵣ[th] WInt v ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗
    ◯(CSTK)[th] cstk ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a error_handling_main_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ (na_own (tpool th) ⊤ ∗
        PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_arg_3")%a ∗
        ca0 ↦ᵣ[th] WInt ECOMPARTMENTFAIL ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        ct2 ↦ᵣ[th] WInt 0 ∗
        ca2 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wcra ∗
        ctp ↦ᵣ[th] wctp ∗
        cs0 ↦ᵣ[th] thread_return_sentry ∗
        regs[th] rmap ∗
        ◯(CSTK)[th] cstk ∗
        codefrag_pers pc_a error_handling_main_code ∗
        MIE ↦ₜ[th] b ∗
        held (th := th) b
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hbounds Hv Hframes Hdom Hroute)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna & HPC & Hca0 & Hctp & Hct0 & Hct1
      & Hct2 & Hca2 & Hcra & Hcs0 & Hrmap & Hcstk & #Himport_assert & #Hcode_main & Hmie & Hheld
      & Hpost)".
    pose proof Hbounds as (HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /assert_entry.

    (* Block 13: return on trusted-stack exhaustion *)
    focus_block (main_block ".Lmain_ret_read_2") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_check Ha_check "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    destruct Hv as [-> | ->].
    { (* Jne 2 ca0 ENOTENOUGHTRUSTEDSTACK *)
      iInstr "Hcode".
      (* Jmp .Lmain_return *)
      iInstr "Hcode".
      { jump_to (pc_a ^+ main_label_offset ".Lmain_return")%a. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iDestruct (main_check_regs_exit _ _ _ _ Hdom with "Hrmap Hca0 Hct1 Hca2")
        as (rmap_exit) "[%Hdom_exit Hrmap]".
      iApply (main_return_spec with
               "[$Hswitcher $Hswitcher_static $Hna $HPC $Hcs0 $Hcra $Hctp $Hct0 $Hct2
                 $Hrmap $Hcstk $Hcode_main $Hmie $Hheld]");
        [exact Hbounds | exact Hframes | exact Hdom_exit | exact Hroute]. }
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
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra $Hcode $Himport_assert $Hmie $Hheld]");
      auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1 & Hmie & Hheld & _ & _)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_assert ^+ length (assert_instrs (-36) ct2 ca2) =
              (pc_a ^+ main_label_offset ".Lmain_arg_3")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End Error_Handling_Main_Blocks_2.
