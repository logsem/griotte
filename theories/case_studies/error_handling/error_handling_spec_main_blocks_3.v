From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * [main], blocks 13-15: the second assert, and the halt

    From the return of the second call to [stats_read], block 13 halts
    when the call returned [ENOTENOUGHTRUSTEDSTACK] (the trusted stack is
    exhausted), block 14 asserts that it returned [5], the value of [x],
    and block 15 halts. *)

Section Error_Handling_Main_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma main_check_2_spec
    (pc_b pc_e pc_a : Addr) (v : Z)
    (wct0 wct1 wct2 wca2 wcra : LWord) :
    main_code_bounds pc_b pc_e pc_a ->
    v = ENOTENOUGHTRUSTEDSTACK ∨ v = 5%Z ->
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
    codefrag_pers pc_a error_handling_main_code
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hv)
      "(#Hassert & Hna & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
      & #Himport_assert & #Hcode_main)".
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
    (* Mov ct1 5 *)
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

    (* Block 15: halt *)
    focus_block (main_block ".Lmain_halt") "Hcode_main" of error_handling_main_blocks
      at pc_a as a_halt Ha_halt "Hcode" "Hcont".
    (* Halt *)
    iInstr "Hcode".
    wp_end; iIntros (_); iFrame "Hna".
  Qed.

End Error_Handling_Main_Blocks_3.
