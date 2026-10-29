From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import stack_object_spec_states.

(** * Stack object, blocks 10-12: return from the callback [g]

    Block 10 reads back the secret and pops it with the stack object [z], block 11
    asserts that the secret is unchanged, and block 12 clears the return
    registers and returns to the caller of [f]. *)

Section SO_Return_Blocks_4.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma so_return_blocks_4_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (csp_b csp_e a_stk1 a_stk2 : Addr)
    (wct0 wct1 wct2 wca2 wcra wret wca0 wca1 : LWord) :
    so_code_bounds pc_b pc_e pc_a C_f ->
    disjoint_from_shadow csp_b csp_e ->
    (a_stk2 + 1)%a = Some a_stk1 ->
    (a_stk1 + (1 + StackEntry_reserved_space))%a = Some csp_e ->
    (csp_b <= a_stk2)%a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    assert_static b_assert e_assert a_flag ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ so_label_offset ".Lso_f_after_call")%a ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e a_stk2 ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] wret ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ca1 ↦ᵣ[th] wca1 ∗
    a_stk1 ↦ₐ WInt so_secret ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a so_main_code ∗
    ▷ (PC ↦ₚ[th] lupdatePcPerm wret ∗
        csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        ct2 ↦ᵣ[th] WInt 0 ∗
        ca2 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wret ∗
        cs0 ↦ᵣ[th] wret ∗
        ca0 ↦ᵣ[th] WInt 0 ∗
        ca1 ↦ᵣ[th] WInt 0 ∗
        a_stk1 ↦ₐ WInt so_secret ∗
        (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
        codefrag_pers pc_a so_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap) Hstk_shadow
               Hastk2 Hastk1 Hcsp_b Htgt)
      "(#Hassert & HPC & Hcsp & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
      & Hcs0 & Hca0 & Hca1 & Hsecret & Himport_assert & Hcode_main & Hpost)".
    unfold StackEntry_reserved_space in Hastk1.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    so_unfold_code.
    rewrite /assert_entry.

    (* Block 10: read back the secret *)
    focus_block (so_block ".Lso_f_after_call") "Hcode_main" of so_main_blocks at pc_a as a_prep Ha_prep "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* CLoad ct0 csp 1 *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hstk_shadow|].
      rewrite /withinBounds; solve_addr+Hastk2 Hastk1 Hcsp_b. }
    { done. }
    { split; auto. rewrite /withinBounds. solve_addr+Hastk2 Hastk1 Hcsp_b. }
    (* Lea csp csp 2 *)
    iInstr "Hcode".
    { transitivity (Some (stk_start_a csp_b csp_e)); auto.
      unfold stk_start_a, StackEntry_reserved_space; solve_addr+Hastk2 Hastk1. }
    (* Mov ct1 so_secret *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: assert that the secret is unchanged *)
    focus_block (so_block ".Lso_f_assert") "Hcode_main" of so_main_blocks at pc_a as a_assert Ha_assert "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto; try (by intros ?).
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1
                    & _ & Himport_assert)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: return *)
    focus_block (so_block ".Lso_f_return") "Hcode_main" of so_main_blocks at pc_a as a_return Ha_return "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ca1 0%Z *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End SO_Return_Blocks_4.
