From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import counter_spec_states.

(** * Counter, blocks 0-3: increment the counter, call to [C_f]

    Block 0 increments the counter stored at [cgp_b], block 1 fetches the
    entry point of the switcher in [ct0], block 2 fetches the entry point
    of [C_f] in [ct1], and block 3 saves the return address in [cs0] and
    jumps to the switcher. The group ends at the entry point of the
    switcher, with the return address of the call in [cra]. *)

Section Counter_Main_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma counter_main_blocks_1_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (cgp_b cgp_e : Addr) (cnt : Z)
    (wct0 wct1 wcs0 wcra : LWord) :
    counter_code_bounds pc_b pc_e pc_a C_f ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cra ↦ᵣ wcra ∗
    cgp_b ↦ₐ WInt cnt ∗
    pc_b ↦ₐ□ counter_switcher_entry ∗
    (pc_b ^+ 1)%a ↦ₐ□ WSealed ot_switcher C_f ∗
    codefrag_pers pc_a counter_main_code ∗
    ▷ (PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        ct0 ↦ᵣ counter_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        cs0 ↦ᵣ wcra ∗
        cra ↦ᵣ WSentry (ret_kind InterruptDisabled) true RX Global pc_b pc_e (pc_a ^+ counter_label_offset ".Lcounter_return")%a ∗
        cgp_b ↦ₐ WInt (cnt + 1) ∗
        pc_b ↦ₐ□ counter_switcher_entry ∗
        (pc_b ^+ 1)%a ↦ₐ□ WSealed ot_switcher C_f ∗
        codefrag_pers pc_a counter_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap) Hcgp_bounds Hcgp_shadow)
      "(HPC & Hcgp & Hct0 & Hct1 & Hcs0 & Hcra
      & Hcgp_b & Himport_switcher & Himport_C_f & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    counter_unfold_code.
    rewrite /counter_switcher_entry.

    (* Block 0: increment the counter *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* CLoad cs0 cgp 0 *)
    iInstr "Hcode".
    { done. }
    { split; first done. apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    (* Add cs0 cs0 1 *)
    iInstr "Hcode".
    iPoseProof deref_res_none as "-#Hdw".
    (* Store cgp cs0 0 *)
    iInstrApply "Hcode" wp_store_success_reg with "[$HPC $Hcs0 $Hcgp $Hcgp_b $Hdw]"
      as "(HPC & Hcs0 & Hcgp & Hcgp_b & _)".
    { apply withinBounds_true_iff; solve_addr+Hcgp_bounds. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 1: fetch the entry point of the switcher *)
    focus_block (counter_block ".Lcounter_fetch_switcher") "Hcode_main" of counter_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 0 _ _ _ _ _ _ _ counter_switcher_entry
              with "[- $HPC $Hct0 $Hcode]"); eauto using switcher_call_sentry_not_heap.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & _ & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: fetch the entry point of [C_f] *)
    focus_block (counter_block ".Lcounter_fetch_C_f") "Hcode_main" of counter_main_blocks at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec 1 with "[- $HPC $Hct1 $Hcode $Himport_C_f]"); eauto.
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iNext; iIntros "(HPC & Hct1 & _ & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 3: save the return address and jump to the switcher *)
    focus_block (counter_block ".Lcounter_call") "Hcode_main" of counter_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 2)%a = (pc_a ^+ counter_label_offset ".Lcounter_return")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End Counter_Main_Blocks_1.
