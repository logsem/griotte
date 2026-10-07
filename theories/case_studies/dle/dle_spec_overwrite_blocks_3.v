From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import dle_spec_states.

(** * Deep locality, block 3: second call to the adversary

    On return from the first call, block 3 overwrites [b := 42], clears the
    argument [ca0], restores the entry points saved in [cs0] and [cs1], and
    jumps to the switcher again. The group ends at the entry point of the
    switcher, with the return address of the second call in [cra]. *)

Section DLE_Overwrite_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  Lemma dle_overwrite_blocks_3_spec
    (pc_b pc_e pc_a cgp_b cgp_e : Addr) (C_f : Sealable)
    (wcgp_b wca0 wct0 wct1 wcra : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ->
    (cgp_b + length dle_main_data)%a = Some cgp_e ->
    PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ dle_instr_offset 3 3)%a ∗
    cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
    ca0 ↦ᵣ wca0 ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    cra ↦ᵣ wcra ∗
    cs0 ↦ᵣ dle_switcher_entry ∗
    cs1 ↦ᵣ WSealed ot_switcher C_f ∗
    cgp_b ↦ₐ wcgp_b ∗
    codefrag pc_a dle_main_code ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call ∗
        cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
        ca0 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ dle_switcher_entry ∗
        ct1 ↦ᵣ WSealed ot_switcher C_f ∗
        cra ↦ᵣ WSentry RX Global pc_b pc_e (pc_a ^+ dle_instr_offset 3 8)%a ∗
        cs0 ↦ᵣ dle_switcher_entry ∗
        cs1 ↦ᵣ WSealed ot_switcher C_f ∗
        cgp_b ↦ₐ WInt 42 ∗
        codefrag pc_a dle_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HsubBounds Hcgp_contiguous)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hcra & Hcs0 & Hcs1 & Hcgp_b & Hcode_main & Hpost)".
    rewrite /dle_switcher_entry.
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    unfold_code dle_main_code "Hcode_main".

    (* Block 3: return from the first call *)
    focus_block 3 "Hcode_main" of dle_main_blocks at pc_a as a_callB Ha_callB "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    change_pc_to (a_callB ^+ 3)%a.
    (* Store cgp 42%Z *)
    iInstr "Hcode".
    { solve_addr+Hcgp_contiguous. }
    (* Mov ca0 0%Z *)
    iInstr "Hcode".
    (* Mov ct0 cs0 *)
    iInstr "Hcode".
    (* Mov ct1 cs1 *)
    iInstr "Hcode".
    (* Jalr cra ct0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_callB ^+ 8)%a = (pc_a ^+ dle_instr_offset 3 8)%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame.
  Qed.

End DLE_Overwrite_Blocks_3.
