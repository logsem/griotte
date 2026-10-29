From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import dle_spec_states.

(** * Deep locality, blocks 5-7: assertion and return

    On return from the second call, block 5 loads [b], block 6 asserts that
    [b = 42] and block 7 returns through the switcher's return sentry,
    saved in [cs0]: the thread exits. *)

Section DLE_Assert_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_assert_blocks_4_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable) (cstk : CSTK)
    (wctp wct0 wct1 wct2 wca2 wcra : LWord) :
    dle_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    cstk.(cstk_frames) = [] ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ dle_label_offset ".Ldle_check")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ WInt 42 ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a dle_main_code
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap)
             Hcgp_contiguous Hcgp_mmio Hframes)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna & HPC & Hcgp & Hctp & Hct0 & Hct1
      & Hct2 & Hca2 & Hcra & Hcs0 & Hcstk & Hcgp_b & Himport_assert & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code dle_main_code "Hcode_main".
    rewrite /assert_entry.

    (* Block 5: return from the second call *)
    focus_block (dle_block ".Ldle_call_B_2") "Hcode_main" of dle_main_blocks at pc_a
      as a_callB2 Ha_callB2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB2 ^+ 2).
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { done. }
    { split; [done| solve_addr]. }
    (* Mov ct1 42%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: assert that b = 42 *)
    focus_block (dle_block ".Ldle_assert") "Hcode_main" of dle_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 7: return, the thread exits *)
    focus_block (dle_block ".Ldle_return") "Hcode_main" of dle_main_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.

End DLE_Assert_Blocks_4.
