From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * [main], blocks 0-6: the calls to [adv] and to [stats_read] with the capability of [x] one past its end

    Blocks 0 and 1 fetch the entry point of the switcher in [ctp] and the
    entry point of [adv] in [ct1], and block 2 jumps to the switcher
    ([main_call_adv_spec]). From the return of [adv], block 3 puts the
    capability of [x], with its address one past its end, in [ca0], blocks 4 and 5 fetch the
    entry points of the switcher and of [stats_read], and block 6 jumps to
    the switcher ([main_call_read_1_spec]). Each group ends at the entry
    point of the switcher, with the return address of the call in [cra]. *)

Section Error_Handling_Main_Blocks_1.
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

  Lemma main_call_adv_spec
    (pc_b pc_e pc_a : Addr) (adv_f : Sealable)
    (wctp wct1 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    is_heap_cap (WSealed ot_switcher adv_f) = false ->
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wctp ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ□ main_switcher_entry ∗
    (pc_b ^+ 2)%a ↦ₐ□ WSealed ot_switcher adv_f ∗
    codefrag_pers pc_a error_handling_main_code ∗
    ▷ (∀ mie, PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ main_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher adv_f ∗
        cra ↦ᵣ WSentry (ret_kind mie) true RX Global pc_b pc_e
                 (pc_a ^+ main_label_offset ".Lmain_ret_adv")%a ∗
        codefrag_pers pc_a error_handling_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hsealed_nonheap)
      "(HPC & Hctp & Hct1 & Hcra & #Himport_switcher & #Himport_adv & #Hcode_main & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /main_switcher_entry.

    (* Block 0: fetch the entry point of the switcher *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
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

    (* Block 1: fetch the entry point of [adv] *)
    focus_block (main_block ".Lmain_fetch_adv") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 2 with "[- $HPC $Hct1 $Hcode $Himport_adv]"); eauto.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & _)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: jump to the switcher *)
    focus_block (main_block ".Lmain_call_adv") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ main_label_offset ".Lmain_ret_adv")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma main_call_read_1_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wca0 wctp wct1 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    (cgp_b + 1)%a = Some cgp_e ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ main_label_offset ".Lmain_ret_adv")%a ∗
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
        ca0 ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_e ∗
        ctp ↦ᵣ main_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher (STATS_read Global) ∗
        cra ↦ᵣ WSentry (ret_kind mie) true RX Global pc_b pc_e
                 (pc_a ^+ main_label_offset ".Lmain_ret_read_1")%a ∗
        codefrag_pers pc_a error_handling_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hcgp_size)
      "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hcra
      & #Himport_switcher & #Himport_read & #Hcode_main & Hpost)".
    assert (is_heap_cap (WSealed ot_switcher (STATS_read Global)) = false) as Hsealed_nonheap
      by (apply sealed_cap_nonheap, stats_export_base_not_heap).
    iDestruct (codefrag_contiguous_region_pers with "Hcode_main") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    main_unfold_code.
    rewrite /main_switcher_entry.

    (* Block 3: the capability of [x], one past its end *)
    focus_block (main_block ".Lmain_ret_adv") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_arg Ha_arg "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Lea ca0 cgp 1 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: fetch the entry point of the switcher *)
    focus_block (main_block ".Lmain_fetch_switcher_1") "Hcode_main" of error_handling_main_blocks
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

    (* Block 5: fetch the entry point of [stats_read] *)
    focus_block (main_block ".Lmain_fetch_read_1") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 3 with "[- $HPC $Hct1 $Hcode $Himport_read]"); eauto.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & _)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: jump to the switcher *)
    focus_block (main_block ".Lmain_call_read_1") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ main_label_offset ".Lmain_ret_read_1")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End Error_Handling_Main_Blocks_1.
