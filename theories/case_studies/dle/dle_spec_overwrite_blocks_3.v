From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import dle_spec_states.

(** * Deep locality, blocks 3-5: second call to the adversary

    On return from the first call, block 3 overwrites [b := 42] and clears
    the argument [ca0], block 4 fetches the entry point of the switcher
    again, and block 5 restores the entry point of the adversary saved in
    [cs1] and jumps to the switcher. The group ends at the entry point of
    the switcher, with the return address of the second call in [cra]. *)

Section DLE_Overwrite_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_overwrite_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable)
    (wcgp_b wca0 wct0 wct1 wcra wcs0 : LWord) :
    dle_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    disjoint_from_mmio cgp_b cgp_e ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ dle_label_offset ".Ldle_overwrite")%a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ[th] wca0 ∗
    ct0 ↦ᵣ[th] wct0 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cra ↦ᵣ[th] wcra ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] WSealed ot_switcher C_f ∗
    cgp_b ↦ₐ wcgp_b ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    codefrag_pers pc_a dle_main_code ∗
    ▷ (∀ mie, PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ[th] WInt 0 ∗
        ct0 ↦ᵣ[th] switcher_entry_call ∗
        ct1 ↦ᵣ[th] WSealed ot_switcher C_f ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) RX Global pc_b pc_e (pc_a ^+ dle_label_offset ".Ldle_check")%a ∗
        cs0 ↦ᵣ[th] wcs0 ∗
        cs1 ↦ᵣ[th] WSealed ot_switcher C_f ∗
        cgp_b ↦ₐ WInt 42 ∗
        pc_b ↦ₐ□ switcher_entry_call ∗
        codefrag_pers pc_a dle_main_code
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap)
             Hcgp_contiguous Hcgp_mmio)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcra & Hcs0 & Hcs1 & Hcgp_b & Himport_switcher
        & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code dle_main_code "Hcode_main".

    (* Block 3: return from the first call *)
    focus_block (dle_block ".Ldle_call_B") "Hcode_main" of dle_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB ^+ 3).
    (* Store cgp 42%Z 0 *)
    iInstr "Hcode".
    { solve_not_shadow Hcgp_mmio. }
    { solve_addr+Hcgp_contiguous. }
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: fetch the entry point of the switcher again *)
    focus_block (dle_block ".Ldle_refetch_switcher") "Hcode_main" of dle_main_blocks at pc_a
      as a_fetch Ha_fetch "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _ switcher_entry_call
              with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { offsets_compute; solve_addr. }
    { solve_addr. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: restore the entry point of the adversary and call it *)
    focus_block (dle_block ".Ldle_call_B_2") "Hcode_main" of dle_main_blocks at pc_a
      as a_callB2 Ha_callB2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ct1 cs1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_callB2 ^+ 2 = (pc_a ^+ dle_label_offset ".Ldle_check")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; rewrite /switcher_entry_call; iFrame "∗ Hcode_main".
  Qed.

End DLE_Overwrite_Blocks_3.
