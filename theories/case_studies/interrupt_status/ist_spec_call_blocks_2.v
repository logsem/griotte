From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import ist_spec_states.

(** * Interrupt status, blocks 1-3: call to the switcher

    Block 1 fetches the entry point of the switcher in [ctp], block 2
    fetches the entry point of [B.f] in [ct1], and the first instruction of
    block 3 jumps to the switcher. The group ends at the entry point of the
    switcher, with the return address of the call in [cra]. *)

Section IST_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma ist_call_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (B_f : Sealable)
    (wctp wct1 wcra : LWord) (b : InterruptStatus) :
    ist_code_bounds pc_b pc_e pc_a B_f ->
    route_pre th b ->
    PC ↦ₚ[th] Cap RX Global pc_b pc_e (pc_a ^+ ist_label_offset ".Lstatus_fetch_switcher")%a ∗
    ctp ↦ᵣ[th] wctp ∗
    ct1 ↦ᵣ[th] wct1 ∗
    cra ↦ᵣ[th] wcra ∗
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher B_f ∗
    codefrag_pers pc_a ist_K_code ∗
    MIE ↦ₜ[th] b ∗
    held (th := th) b ∗
    ▷ (PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ[th] switcher_entry_call ∗
        ct1 ↦ᵣ[th] WSealed ot_switcher B_f ∗
        cra ↦ᵣ[th] Sentry (ret_kind b) RX Global pc_b pc_e
          (pc_a ^+ ist_label_offset ".Lstatus_overwrite")%a ∗
        pc_b ↦ₐ□ switcher_entry_call ∗
        (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher B_f ∗
        codefrag_pers pc_a ist_K_code ∗
        MIE ↦ₜ[th] InterruptDisabled ∗
        held (th := th) InterruptDisabled
        -∗ safe[th])
    ⊢ safe[th].
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & HB_f_nonheap)
             Hroute)
      "(HPC & Hctp & Hct1 & Hcra & Himport_switcher & Himport_B_f
      & Hcode_main & Hmie & Hheld & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code ist_K_code "Hcode_main".
    rewrite /switcher_entry_call.

    (* Block 1: fetch the entry point of the switcher *)
    focus_block (ist_block ".Lstatus_fetch_switcher") "Hcode_main" of ist_K_blocks at pc_a
      as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _ switcher_entry_call
              with "[- $HPC $Hctp $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { offsets_compute; solve_addr. }
    { solve_addr. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: fetch the entry point of [B.f] *)
    focus_block (ist_block ".Lstatus_fetch_B_f") "Hcode_main" of ist_K_blocks at pc_a
      as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hcode $Himport_B_f]"); eauto; try done.
    { offsets_compute; solve_addr. }
    { solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & Himport_B_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 3: jump to the switcher *)
    focus_block (ist_block ".Lstatus_call_B") "Hcode_main" of ist_K_blocks at pc_a
      as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jalr cra ctp *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_call ^+ 1 = (pc_a ^+ ist_label_offset ".Lstatus_overwrite")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End IST_Call_Blocks_2.
