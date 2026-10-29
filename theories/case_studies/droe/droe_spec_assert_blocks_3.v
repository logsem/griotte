From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import switcher_base.
From griotte Require Import droe_spec_states.

(** * Deep immutability, blocks 3-5: assertion and return

    On return from the call, block 3 restores the return address saved in
    [cs0], the switcher's return sentry, and loads [b], block 4 asserts
    that [b = 42], and block 5 clears the return values and returns: the
    thread exits. *)

Section DROE_Assert_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma droe_assert_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable) (cstk : CSTK)
    (wca0 wca1 wctp wct0 wct1 wct2 wca2 wcra : LWord) :
    droe_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b + length droe_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    cstk.(cstk_frames) = [] ->
    assert_static b_assert e_assert a_flag ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ droe_label_offset ".Ldroe_ret_B")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    ctp ↦ᵣ[th] wctp ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cs0 ↦ᵣ[th] thread_return_sentry ∗
    cra ↦ᵣ[th] wcra ∗
    ◯(CSTK)[th] cstk ∗
    cgp_b ↦ₐ WInt 42 ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a droe_main_code
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap)
             Hcgp_contiguous Hcgp_mmio Hframes)
      "(#Hassert & #Hswitcher & #Hswitcher_static & Hna & HPC & Hcgp & Hca0 & Hca1 & Hctp
        & Hct0 & Hct1 & Hct2 & Hca2 & Hcs0 & Hcra & Hcstk & Hcgp_b & Himport_assert
        & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code droe_main_code "Hcode_main".
    rewrite /assert_entry.

    (* Block 3: return from the call *)
    focus_block (droe_block ".Ldroe_call_B") "Hcode_main" of droe_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB ^+ 2).
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { done. }
    { split; [done| solve_addr]. }
    (* Mov ct1 42%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: assert that b = 42 *)
    focus_block (droe_block ".Ldroe_assert") "Hcode_main" of droe_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: clear the return values and return, the thread exits *)
    focus_block (droe_block ".Ldroe_return") "Hcode_main" of droe_main_blocks at pc_a
      as a_ret Ha_ret "Hcode" "Hcont".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    iEval (rewrite thread_return_sentry_pc) in "HPC".
    iApply (switcher_ret_thread_exit_specification _ _ _ _ Hframes with
             "[$Hswitcher $Hswitcher_static $Hna $HPC $Hctp $Hct0 $Hct2 $Hcstk]").
  Qed.

End DROE_Assert_Blocks_3.
