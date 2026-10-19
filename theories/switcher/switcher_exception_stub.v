From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel switcher_preamble interp_switcher_return.

(** * Exception entry of the switcher

    The exception entry ([exception_entry_asm], the last block of the
    switcher) unwinds the faulting compartment's call: it sets the return
    values and runs the return routine. It reads no register of the faulting
    compartment, so its safety needs no validity of the register file. *)

Section Switcher_Exception_Stub.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  #[local] Lemma switcher_exception_entry_block_spec_aux
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) pc_a wca0 wca1 :
    SubBounds b_switcher e_switcher pc_a
      (pc_a ^+ length (switcher_instrs_n 20))%a ->
    (pc_a ^+ 2 +
       asm_label_offset switcher_asm ".Lexception_entry_return"
         ".Lswitcher_after_compartment_call")%a =
      Some a_switcher_return ->
    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a (switcher_instrs_n 20) ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        codefrag_pers pc_a (switcher_instrs_n 20) -∗
        WP Seq (Instr Executable) @ E {{ Φ }} )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    iIntros (Hsub Hret) "(HPC & Hca0 & Hca1 & #Hcode & Hpost)".
    (* Compute the distance to the return block. *)
    offsets_compute.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    codefrag_facts "Hcode".
    (* Mov ca0 (inl ECOMPARTMENTFAIL) *)
    iInstr "Hcode".
    (* Mov ca1 (inl 0%Z) *)
    iInstr "Hcode".
    (* Jmp (".Lswitcher_after_compartment_call")%asm *)
    iInstr "Hcode".
    iApply "Hpost"; iFrame "∗ Hcode".
  Qed.

  (** The exception entry block: set the error code and jump to the return
      routine. *)
  Lemma switcher_exception_entry_block_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (wca0 wca1 : LWord) :
    PC ↦ₚ switcher_label_pc "exception_entry_asm" ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wca1 ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 ∗
        switcher_code -∗
        WP Seq (Instr Executable) @ E {{ Φ }} )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    iIntros "(HPC & Hca0 & Hca1 & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_return_offset as Hret.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block "exception_entry_asm") "Hswitcher" as "Hcode" "Hcls";
      iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_entry_block_spec_aux with "[- $HPC $Hca0 $Hca1 $Hcode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    iApply "Hpost"; iFrame "∗ Hswitcher".
  Qed.

  (** The validity-free unwind: from the exception entry, whatever the
      registers hold, the switcher unwinds the call of the faulting
      compartment through the return routine. *)
  Lemma switcher_exception_entry_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ switcher_label_pc "exception_entry_asm" ∗
    registers_pointsto rmap ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ interp_conf W C.
  Proof.
    iIntros (Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto /interp_conf.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_exception_entry_block_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. *)
  Lemma switcher_trap_vector_safe (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros "[#Hinv_switcher #Hstatic]".
    rewrite trap_vector_safe_unfold /interp_continuation.
    iIntros "!>" (W C cstk Ws Cs regs Hfull_rmap Hframe)
      "HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    iApply (switcher_exception_entry_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Hworld_interp $Hcont $Hna $Hcstk]");
      done.
  Qed.

End Switcher_Exception_Stub.
