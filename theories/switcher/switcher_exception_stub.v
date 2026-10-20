From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel switcher_preamble switcher_return_blocks_1 interp_switcher_return.
From griotte Require Import switcher_call_blocks_6.

(** * Exception entry of the switcher

    The exception entry ([exception_entry_asm], the last block of the
    switcher) unwinds the faulting compartment's call: it sets the return
    values and runs the return routine. It reads no register of the faulting
    compartment, so its safety needs no validity of the register file.

    It is a safe trap vector ([switcher_trap_vector_safe]), which closes the
    faults of trusted code ([trap_safe_unwind], [trap_safe_absurd]). The file
    also hosts the safety of the return-to-switcher entry point
    ([interp_expr_switcher_return], [interp_switcher_return]), which needs
    the trap vector and would otherwise form an import cycle. *)

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
      compartment through the return routine. The trap vector is only needed
      after the first instruction, hence under a later. *)
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
    ▷ trap_vector_safe (lword_of_word mtcc_vec) ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ interp_conf W C.
  Proof.
    iIntros (Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & #Htrap & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    rewrite /registers_pointsto /interp_conf.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_exception_entry_block_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. The proof is
      by Löb induction: the unwind needs the trap vector to be safe only
      after the first instruction of the exception entry. *)
  Lemma switcher_trap_vector_safe (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc)".
    iLöb as "IH".
    iEval (rewrite trap_vector_safe_unfold /interp_continuation).
    iIntros "!>" (W C cstk Ws Cs regs Hfull_rmap Hframe)
      "HPC Hrmap Hworld_interp Hcont Hna Hcstk".
    iApply (switcher_exception_entry_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Hworld_interp $Hcont $Hna $Hcstk]");
      [done|done|].
    rewrite Hmtcc.
    iExact "IH".
  Qed.

  (** The trap vector of the machine is safe, given the switcher. *)
  Lemma switcher_mtcc_vec_safe (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (lword_of_word mtcc_vec).
  Proof.
    iIntros "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc)".
    rewrite Hmtcc.
    iApply (switcher_trap_vector_safe with "[$Hinv_switcher $Hstatic]").
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point: block 21 sets the return values, and the return routine
      pops the frame already pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_too_small" ∗
    registers_pointsto rmap ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]") as "#Htrap".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_call_block_21_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** A fault closes through the exception entry of the switcher: after
      exception entry, the exception entry block sets the return values and
      jumps to the return routine, which must then be safe. The resources are
      only needed after the exception entry, hence under an update. *)
  Lemma trap_safe_exception_entry (w : LWord) :
    switcher_static -∗
    (|={⊤}=>
       ca0 ↦ᵣ - ∗
       ca1 ↦ᵣ - ∗
       (PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ca0 ↦ᵣ WInt ECOMPARTMENTFAIL ∗
        ca1 ↦ᵣ WInt 0 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros "#Hstatic Hres".
    iPoseProof "Hstatic" as "(#Hcode & _ & %Hmtcc)".
    iApply (trap_safe_entry_intro with "[]"); first iApply trap_entry_res_intro.
    iSplit; last by iIntros "!> %Hv".
    iIntros "!> _ HPC".
    iMod "Hres" as "([%wca0 Hca0] & [%wca1 Hca1] & Hcont)".
    rewrite Hmtcc.
    iApply (switcher_exception_entry_block_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iApply ("Hcont" with "[$HPC $Hca0 $Hca1]").
  Qed.

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment.
      No register needs to be safe. The resources are only needed after the
      exception entry, hence under an update (for instance, to close an
      invariant). *)
  Lemma trap_safe_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       registers_pointsto rmap ∗
       world_interp W C ∗
       interp_cont interp cstk Ws Cs ∗
       na_own cerise_nais ⊤ ∗
       cstack_frag cstk) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (Hfull_rmap Hframe) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]") as "#Htrap".
    iApply (interp_trap_safe with "Htrap Hres"); done.
  Qed.

  (** A fault that cannot happen is safe: the update yields a contradiction,
      which is eliminated after trap entry. *)
  Lemma trap_safe_absurd (w : LWord) :
    (|={⊤}=> False) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros "Hfalse".
    iApply (trap_safe_entry_intro with "[]"); first iApply trap_entry_res_intro.
    iSplit; last by iIntros "!> %Hv".
    iIntros "!> _ _".
    by iMod "Hfalse".
  Qed.

  (** The return-to-switcher entry point is safe to execute: the registers
      are re-filtered, then the return routine runs ([switcher_return_unwind]). *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %rmap0
             [Hregs (HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)]".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]") as "#Htrap".
    iApply (interp_reg_refilter with "Hregs Hrmap Hworld_interp").
    iIntros (rmap) "%Hfull_rmap #Hrmap_interp Hrmap Hworld_interp". clear rmap0.
    cbn in Hfull_rmap.
    getRegValList [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont_K $Hna $Hcstk]");
      [done|done|done|done|].
    iSplit; iApply "Hrmap_interp"; done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (mie : InterruptStatus) :
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "[$Hinv $Hstatic]").
  Qed.


End Switcher_Exception_Stub.
