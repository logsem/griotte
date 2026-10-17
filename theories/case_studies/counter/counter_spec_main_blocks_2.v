From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import counter_spec_states.

(** * Counter, block 4: return

    From the return of the call to [C_f], block 4 restores the return
    address in [cra], clears the return values and the saved registers,
    and jumps to the switcher, for the return. *)

Section Counter_Main_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma counter_main_blocks_2_spec
    (pc_b pc_e pc_a : Addr) (C_f : Sealable)
    (wret wcra wca0 wca1 wcs1 wcnull : LWord) :
    counter_code_bounds pc_b pc_e pc_a C_f ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ counter_label_offset ".Lcounter_return")%a ∗
    cra ↦ᵣ wcra ∗
    cs0 ↦ᵣ wret ∗
    cs1 ↦ᵣ wcs1 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wcnull ∗
    codefrag_pers pc_a counter_main_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
        cra ↦ᵣ wret ∗
        cs0 ↦ᵣ WInt 0 ∗
        cs1 ↦ᵣ WInt 0 ∗
        ca0 ↦ᵣ WInt 0 ∗
        ca1 ↦ᵣ WInt 0 ∗
        cnull ↦ᵣ WInt 0 ∗
        codefrag_pers pc_a counter_main_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Himports_contiguous & Hpc_shadow & Hpc_nonheap & Hsealed_nonheap))
      "(HPC & Hcra & Hcs0 & Hcs1 & Hca0 & Hca1 & Hcnull & Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.
    counter_unfold_code.

    (* Block 4: restore the return address, clear the registers, and
       return *)
    focus_block (counter_block ".Lcounter_return") "Hcode_main" of counter_main_blocks at pc_a as a_ret Ha_ret "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov cra cs0 *)
    iInstr "Hcode".
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Mov cs0 0 *)
    iInstr "Hcode".
    (* Mov cs1 0 *)
    iInstr "Hcode".
    destruct (jalr_target_ok wret.(lw)) eqn:Htgt; cycle 1.
    { (* Jalr cnull cra *)
      iInstr_fail "Hcode".
      wp_end; by iIntros (?). }
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

End Counter_Main_Blocks_2.
