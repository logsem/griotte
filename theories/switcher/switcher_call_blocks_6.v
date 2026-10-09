From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, block 17: forced unwind

    When the checks on the stack pointer fail (blocks 0-1), block 17 sets the
    error code and jumps to the return routine. *)

Section Switcher_Call_Blocks_6.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Local Lemma switcher_call_block_17_spec_aux
    pc_a wca0 wca1 :
    SubBounds b_switcher e_switcher pc_a
      (pc_a ^+ length (switcher_instrs_n 17))%a ->
    (pc_a ^+ 2 + (-61))%a = Some a_switcher_return ->
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag pc_a (switcher_instrs_n 17) ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        codefrag pc_a (switcher_instrs_n 17) -∗
        WP Seq (Instr Executable)
          {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hret) "(HPC & Hca0 & Hca1 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* Mov ca0 (inl (-1)%Z) *)
    iInstr "Hcode".
    (* Mov ca1 (inl 0%Z) *)
    iInstr "Hcode".
    (* Jmp (".Lswitcher_after_compartment_call")%asm *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  (** Block 17: force the unwinding of the call. *)
  Lemma switcher_call_block_17_spec (wca0 wca1 : Word) :
    PC ↦ᵣ switcher_block_pc 17 ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    switcher_code ∗
    ▷ ( PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_return_offset.
    switcher_unfold_code "Hcode".
    switcher_focus_block 17 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_17_spec_aux with "[- $HPC $Hca0 $Hca1 $Hcode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "(HPC & Hca0 & Hca1 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    iApply "Hpost"; iFrame.
  Qed.

End Switcher_Call_Blocks_6.
