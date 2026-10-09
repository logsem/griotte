From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import droe_spec_states.

(** * Deep immutability, blocks 1-3: call to the adversary

    Blocks 1 and 2 fetch the entry point of the switcher and the entry point
    of the adversary from the imports. Block 3 saves the return address in
    [cs0], and jumps to the switcher. The group ends at the entry point of
    the switcher, with the return address of the call in [cra]. *)

Section DROE_Share_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma droe_share_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (wct0 wct1 wct2 wct3 wcs0 wcra : Word) :
    droe_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ droe_block_offset 1)%a ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    cs0 ↦ᵣ wcs0 ∗
    cra ↦ᵣ wcra ∗
    droe_static_mem pc_b pc_a C_f ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ droe_instr_offset 3 2)%a ∗
        ct0 ↦ᵣ droe_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        ct2 ↦ᵣ WInt 0 ∗
        ct3 ↦ᵣ WInt 0 ∗
        cs0 ↦ᵣ wcra ∗
        droe_static_mem pc_b pc_a C_f
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous])
      "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hcs0 & Hcra & Hmem & Hpost)".
    iDestruct "Hmem" as "((Himport_switcher & Himport_assert & Himport_C_f) & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code droe_main_code "Hcode_main".

    (* Block 1: fetch the entry point of the switcher *)
    focus_block 1 "Hcode_main" of droe_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hct1 $Hct2 $Hcode]"); eauto.
    { solve_addr. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hcode & Himport_switcher)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: fetch the entry point of the adversary *)
    focus_block 2 "Hcode_main" as a_fetch2 Ha_fetch2 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct2 $Hct3 $Hcode $Himport_C_f]"); eauto.
    { solve_addr. }
    iNext; iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hcode & Himport_C_f)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 3: save the return address and call the adversary *)
    focus_block 3 "Hcode_main" of droe_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_callB ^+ 2)%a = (pc_a ^+ droe_instr_offset 3 2)%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; rewrite /droe_static_mem /droe_switcher_entry; iFrame.
  Qed.

End DROE_Share_Blocks_2.
