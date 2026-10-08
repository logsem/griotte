From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import cmdc_spec_states.

(** * Cmdc, blocks 1-3 and 6-8: calls to the switcher

    For the call [c], the first block fetches the entry point of the
    switcher in [ctp], the second block fetches the entry point of the
    callee in [ct1], and the first instruction of the third block jumps to
    the switcher. The group ends at the entry point of the switcher, with
    the return address of the call in [cra]. *)

Section CMDC_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The proof of [cmdc_call_blocks_2_spec], for the call starting at
      block [n]: the code of the two calls only differs by the import of the
      callee. *)
  Local Ltac cmdc_call_blocks_proof n pc_a pc_b :=
    let hcont := fresh "hcont" in
    let a_fetch1 := fresh "a_fetch1" in
    let a_fetch2 := fresh "a_fetch2" in
    let a_call := fresh "a_call" in
    let Ha_fetch1 := fresh "Ha_fetch1" in
    let Ha_fetch2 := fresh "Ha_fetch2" in
    let Ha_call := fresh "Ha_call" in
    (* Block n: fetch the entry point of the switcher *)
    focus_block n "Hcode_main" of cmdc_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (fetch_spec with "[- $HPC $Hctp $Hct0 $Hct1 $Hcode]"); eauto; [solve_addr|];
    replace (pc_b ^+ 0)%a with pc_b by solve_addr;
    iFrame "Himport_switcher";
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hcode & Himport_switcher)";
    iEval (cbn) in "Hctp";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Block n+1: fetch the entry point of the callee *)
    focus_block (S n) "Hcode_main" of cmdc_main_blocks at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    iApply (fetch_spec with "[- $HPC $Hct1 $Hct0 $Hcs0 $Hcode $Himport_target]"); eauto; [solve_addr|];
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hcs0 & Hcode & Himport_target)";
    iEval (cbn) in "Hct1";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";

    (* Block n+2: jump to the switcher *)
    focus_block (S (S n)) "Hcode_main" of cmdc_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont";
    iHide "Hcont" as hcont;
    (* Jalr cra ctp *)
    iInstr "Hcode";
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main";
    assert ((a_call ^+ 1)%a = (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a) as ->
      by (offsets_compute; solve_addr);
    iApply "Hpost"; iFrame.

  Lemma cmdc_call_blocks_2_spec (c : cmdc_call)
    (pc_b pc_e pc_a : Addr) (B_f C_g : Sealable)
    (wctp wct0 wct1 wcs0 wcra : Word) :
    let n := cmdc_call_block c in
    cmdc_code_bounds pc_b pc_e pc_a B_f C_g ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ cmdc_block_offset n)%a ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cs0 ↦ᵣ wcs0 ∗
    cra ↦ᵣ wcra ∗
    pc_b ↦ₐ cmdc_switcher_entry ∗
    (pc_b ^+ cmdc_call_import c)%a ↦ₐ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
    codefrag pc_a cmdc_main_code ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        ctp ↦ᵣ cmdc_switcher_entry ∗
        ct0 ↦ᵣ WInt 0 ∗
        ct1 ↦ᵣ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
        cs0 ↦ᵣ WInt 0 ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ cmdc_instr_offset (n + 2) 1)%a ∗
        pc_b ↦ₐ cmdc_switcher_entry ∗
        (pc_b ^+ cmdc_call_import c)%a ↦ₐ WSealed ot_switcher (cmdc_call_target c B_f C_g) ∗
        codefrag pc_a cmdc_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros n.
    destruct c; subst n; cbn [cmdc_call_block cmdc_call_import cmdc_call_target].
    all: iIntros ([HsubBounds Himports_contiguous])
      "(HPC & Hctp & Hct0 & Hct1 & Hcs0 & Hcra & Himport_switcher & Himport_target
      & Hcode_main & Hpost)".
    all: codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    all: unfold_code cmdc_main_code "Hcode_main".
    all: rewrite /cmdc_switcher_entry.
    - (* Call to [B.f], blocks 1-3 *)
      cmdc_call_blocks_proof 1 pc_a pc_b.
    - (* Call to [C.g], blocks 6-8 *)
      cmdc_call_blocks_proof 6 pc_a pc_b.
  Qed.

End CMDC_Call_Blocks_2.
