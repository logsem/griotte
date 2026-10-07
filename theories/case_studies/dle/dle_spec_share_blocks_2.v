From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import dle_spec_states.

(** * Deep locality, blocks 1-3: first call to the adversary

    Blocks 1 and 2 fetch the entry point of the switcher and the entry point
    of the adversary from the imports. Block 3 saves them in [cs0] and
    [cs1], and jumps to the switcher. The group ends at the entry point of
    the switcher, with the return address of the first call in [cra]. *)

Section DLE_Share_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_share_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (wct0 wct1 wct2 wct3 wcs0 wcs1 wcra : Word) :
    dle_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ dle_block_offset 1)%a ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ct3 ↦ᵣ wct3 ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    dle_static_mem pc_b pc_a C_f ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ dle_instr_offset 3 3)%a ∗
        ct0 ↦ᵣ dle_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        ct2 ↦ᵣ WInt 0 ∗
        ct3 ↦ᵣ WInt 0 ∗
        cs0 ↦ᵣ dle_switcher_entry ∗
        cs1 ↦ᵣ WSealed ot_switcher C_f ∗
        dle_static_mem pc_b pc_a C_f
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ([HsubBounds Himports_contiguous])
      "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hcs0 & Hcs1 & Hcra & Hmem & Hpost)".
    iDestruct "Hmem" as "((Himport_switcher & Himport_assert & Himport_C_f) & Hcode_main)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    dle_unfold_code "Hcode_main".

    (* Block 1: fetch the entry point of the switcher *)
    dle_focus_block 1 "Hcode_main" at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
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

    (* Block 3: save the entry points and call the adversary *)
    dle_focus_block 3 "Hcode_main" at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cs0 ct0 *)
    iInstr "Hcode".
    (* Mov cs1 ct1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_callB ^+ 3)%a = (pc_a ^+ dle_instr_offset 3 3)%a) as ->
      by (dle_offsets_compute; solve_addr).
    iApply "Hpost"; rewrite /dle_static_mem /dle_switcher_entry; iFrame.
  Qed.

End DLE_Share_Blocks_2.
