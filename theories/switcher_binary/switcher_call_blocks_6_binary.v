From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region memory_region_binary rules proofmode proofmode_binary.
From griotte Require Import register_tactics register_tactics_binary.
From griotte Require Import switcher_call_states_binary.

(** * Call routine, block 17: forced unwind, binary model

    When the checks on the stack pointer fail (blocks 0-1), block 17 sets the
    error code and jumps to the return routine, in both runs. *)

Section Switcher_Call_Blocks_6.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Local Lemma switcher_call_block_17_spec_aux
    pc_a wca0 swca0 wca1 swca1 :
    SubBounds b_switcher e_switcher pc_a
      (pc_a ^+ length (switcher_instrs_n 17))%a ->
    (pc_a ^+ 2 + (-61))%a = Some a_switcher_return ->
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher pc_a ∗
    ca0 ↦ᵣ wca0 ∗
    ca0 ↣ᵣ swca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca1 ↣ᵣ swca1 ∗
    codefrag pc_a (switcher_instrs_n 17) ∗
    spec_codefrag pc_a (switcher_instrs_n 17) ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca0 ↣ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        ca1 ↣ᵣ WInt 0 ∗
        codefrag pc_a (switcher_instrs_n 17) ∗
        spec_codefrag pc_a (switcher_instrs_n 17) -∗
        switcher_wp)
    ⊢ switcher_wp.
  Proof.
    iIntros (Hsub Hret) "(#Hspec & Hj & HPC & HsPC & Hca0 & Hsca0 & Hca1 & Hsca1
      & Hcode & Hscode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* Mov ca0 ECOMPARTMENTFAIL *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Mov ca1 0 *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Jmp (".Lswitcher_after_compartment_call")%asm *)
    iInstr_lockstep "Hscode" "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

  (** Block 17: force the unwinding of the call. *)
  Lemma switcher_call_block_17_spec (wca0 swca0 wca1 swca1 : Word) :
    spec_ctx ∗
    ⤇ Seq (Instr Executable) ∗
    PC ↦ᵣ switcher_block_pc 17 ∗
    PC ↣ᵣ switcher_block_pc 17 ∗
    ca0 ↦ᵣ wca0 ∗
    ca0 ↣ᵣ swca0 ∗
    ca1 ↦ᵣ wca1 ∗
    ca1 ↣ᵣ swca1 ∗
    switcher_code ∗
    switcher_spec_code ∗
    ▷ ( ⤇ Seq (Instr Executable) ∗
        PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca0 ↣ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        ca1 ↣ᵣ WInt 0 ∗
        switcher_code ∗
        switcher_spec_code -∗
        switcher_wp )
    ⊢ switcher_wp.
  Proof.
    iIntros "(#Hspec & Hj & HPC & HsPC & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcode & Hscode & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_return_offset.
    switcher_unfold_code "Hcode".
    switcher_unfold_code "Hscode".
    switcher_focus_block_lockstep 17 "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (switcher_call_block_17_spec_aux with
      "[- $Hspec $Hj $HPC $HsPC $Hca0 $Hsca0 $Hca1 $Hsca1 $Hcode $Hscode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "(Hj & HPC & HsPC & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    iApply "Hpost"; iFrame.
  Qed.

End Switcher_Call_Blocks_6.
