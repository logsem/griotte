From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, blocks 3-4 and 8-9: assertions after the calls

    On return from the call [c], the third block of the call loads the
    word pointed to by [cgp] (the data that was not shared with the
    callee), and the next block asserts that it is unchanged. *)

Section CMDC_Check_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The proof of [cmdc_check_blocks_3_spec], for the call that returns
      at the label [l_ret], followed by the assertion at [l_assert] and by
      the code at [l_next]: the code of the two calls only differs by the
      asserted value. *)
  #[local] Ltac cmdc_check_blocks_proof l_ret l_assert l_next pc_a :=
    let hcont := fresh "hcont" in
    let a_call := fresh "a_call" in
    let a_assert := fresh "a_assert" in
    let Ha_call := fresh "Ha_call" in
    let Ha_assert := fresh "Ha_assert" in
    (* Return from the call *)
    focus_block (cmdc_block l_ret) "Hcode_main" of cmdc_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    change_pc_to (a_call ^+ 1);
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode";
    [by apply not_mmio_not_shadow | done | split; [done | solve_addr] |];
    (* Mov ct1 0%Z, resp. Mov ct1 42%Z *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Assert that the data is unchanged *)
    focus_block (cmdc_block l_assert) "Hcode_main" of cmdc_main_blocks at pc_a
      as a_assert Ha_assert "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (assert_success_spec 1 with
             "[- $Hassert $HPC $Hct2 $Hca2 $Hct0 $Hct1 $Hcra
              $Hcode $Himport_assert]"); auto; try (by intros ?);
      [offsets_compute; solve_addr|solve_addr|];
    iNext; iIntros "(HPC & Hct2 & Hca2 & Hcra & Hct0 & Hct1
                    & _ & Himport_assert)";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    change_pc_to (pc_a ^+ cmdc_label_offset l_next);
    iApply "Hpost"; iFrame "∗ Hcode_main".

  Lemma cmdc_check_blocks_3_spec (c : cmdc_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (cgp_b cgp_e a_chk : Addr)
    (wct0 wct1 wct2 wca2 wcra : LWord) :
    cmdc_code_bounds pc_b pc_e pc_a B_f C_g ->
    a_chk ∈ₐ [cgp_b, cgp_e) ->
    is_mmio_address a_chk = false ->
    assert_static b_assert e_assert a_flag ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ cmdc_label_offset (cmdc_return_label c)) ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e a_chk ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ca2 ↦ᵣ[th] wca2 ∗
    cra ↦ᵣ[th] wcra ∗
    a_chk ↦ₐ WInt (cmdc_call_expected c) ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    codefrag_pers pc_a cmdc_main_code ∗
    ▷ ( PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ cmdc_label_offset (cmdc_next_label c)) ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e a_chk ∗
        ct0 ↦ᵣ[th] WInt 0 ∗
        ct1 ↦ᵣ[th] WInt 0 ∗
        ct2 ↦ᵣ[th] WInt 0 ∗
        ca2 ↦ᵣ[th] WInt 0 ∗
        cra ↦ᵣ[th] wcra ∗
        a_chk ↦ₐ WInt (cmdc_call_expected c) ∗
        (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
        codefrag_pers pc_a cmdc_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    destruct c; cbn [cmdc_return_label cmdc_next_label cmdc_call_expected].
    all: iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap
                   & HC_g_nonheap) Ha_chk Ha_chk_mmio)
      "(#Hassert & HPC & Hcgp & Hct0 & Hct1 & Hct2 & Hca2 & Hcra
      & Ha_chk & Himport_assert & Hcode_main & Hpost)".
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_main_code "Hcode_main".
    all: rewrite /assert_entry.
    - (* Return from [B.f], blocks 3-4 *)
      cmdc_check_blocks_proof
        ".Lcmdc_return_B"%string ".Lcmdc_assert_B"%string
        ".Lcmdc_prep_C"%string pc_a.
    - (* Return from [C.g], blocks 8-9 *)
      cmdc_check_blocks_proof
        ".Lcmdc_return_C"%string ".Lcmdc_assert_C"%string
        ".Lcmdc_return"%string pc_a.
  Qed.

End CMDC_Check_Blocks_3.
