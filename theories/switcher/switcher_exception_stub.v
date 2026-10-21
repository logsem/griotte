From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import logrel switcher_preamble switcher_return_blocks_1 interp_switcher_return.
From griotte Require Import switcher_call_blocks_6 switcher_spec_exception.

(** * Exception entry of the switcher

    The exception path ([exception_entry_asm], see [switcher_spec_exception])
    spills the interrupted context and unwinds the faulting compartment's
    call: it sets the return values and runs the return routine. It reads
    the registers of the faulting compartment only to spill them, so its
    safety needs no validity of the register file.

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

  (** The validity-free unwind: from the exception entry, after trap entry,
      whatever the registers hold, the switcher unwinds the call of the
      faulting compartment through the return routine. The trap vector is
      only needed after the first instruction, hence under a later. *)
  Lemma switcher_exception_entry_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
    (∀ r, is_Some (rmap !! r)) ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ lword_of_word mtcc_vec ∗
    trap_entry_out w ∗
    registers_pointsto rmap ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    ▷ trap_vector_safe (lword_of_word mtcc_vec) ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais (⊤ ∖ ↑N_trap) ∗
    cstack_frag cstk
    ⊢ interp_conf W C.
  Proof.
    iIntros (Hdisj Hfull_rmap Hframe)
      "(HPC & Hout & Hrmap & #Hinv_switcher & #Hstatic & #Htrap & Hworld_interp & Hcont & Hna
        & Hcstk)".
    rewrite /interp_conf.
    iApply (switcher_exception_path_spec Nswitcher ⊤ with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna Hworld_interp Hcont Hcstk]");
      [set_solver | set_solver | done | done |].
    iNext; iIntros (rmap' Hfull_rmap' Hca0 Hca1) "HPC Hrmap Hna".
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [done | done | done | done |].
    iSplit; iApply interp_int.
  Qed.

  (** The trap vector of the machine, the exception entry of the switcher,
      is safe. The proof is by Löb induction: the unwind needs the trap
      vector to be safe only after the first instruction of the exception
      entry. The exception path opens the invariant of the switcher while
      trap entry holds [N_trap]. *)
  Lemma switcher_mtcc_vec_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (lword_of_word mtcc_vec).
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iLöb as "IH".
    iIntros "!>" (W C cstk Ws Cs regs w Hfull_rmap Hframe)
      "HPC Hout Hrmap Hworld_interp Hcont Hna Hcstk".
    iApply (switcher_exception_entry_unwind with
             "[$HPC $Hout $Hrmap $Hinv_switcher $Hstatic $IH $Hworld_interp $Hcont $Hna $Hcstk]");
      done.
  Qed.

  (** The exception entry of the switcher is a safe trap vector. *)
  Lemma switcher_trap_vector_safe (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ trap_vector_safe (switcher_label_pc "exception_entry_asm").
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic]".
    iPoseProof "Hstatic" as "(_ & _ & %Hmtcc)".
    rewrite -Hmtcc.
    iApply (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hstatic]"); done.
  Qed.

  (** The callee's stack is smaller than the minimum stack size of the
      entry point: block 20 sets the return values, and the return routine
      pops the frame already pushed. No register needs to be safe. *)
  Lemma switcher_call_stack_too_small_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) :
    Nswitcher ## N_trap ->
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
    iIntros (Hdisj Hfull_rmap Hframe)
      "(HPC & Hrmap & #Hinv_switcher & #Hstatic & Hworld_interp & Hcont & Hna & Hcstk)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    rewrite /registers_pointsto.
    getRegValList [ca0;ca1].
    iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
    iApply (switcher_call_block_20_spec with "[- $HPC $Hca0 $Hca1 $Hcode]").
    iNext; iIntros "(HPC & Hca0 & Hca1 & _)".
    iInsertList "Hrmap" [ca0;ca1].
    iApply (switcher_return_unwind with
             "[$HPC $Hrmap $Hinv_switcher $Hstatic $Htrap $Hworld_interp $Hcont $Hna $Hcstk]");
      [|by simplify_map_eq|by simplify_map_eq|done|].
    { intros r. rewrite !lookup_insert_is_Some'. naive_solver. }
    iSplit; iApply interp_int.
  Qed.

  (** A fault closes through the exception path of the switcher: after
      trap entry, the switcher spills the registers, sets the return values
      and jumps to the return routine, which must then be safe. The
      resources come under an update at the time of the fault; the
      non-atomic token [F] provides the trap-entry token, and the exception
      path opens the invariant of the switcher with the rest of [F]. The
      continuation receives the registers as the exception path leaves them,
      with the return values set. *)
  Lemma trap_safe_exception_entry (Nswitcher : namespace) (F : coPset) (w : LWord) :
    ↑Nswitcher ⊆ F →
    ↑N_trap ⊆ F →
    Nswitcher ## N_trap →
    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       ∃ rmap : LReg,
         ⌜∀ r, is_Some (rmap !! r)⌝ ∗
         na_own cerise_nais F ∗
         registers_pointsto rmap ∗
         (∀ rmap' : LReg,
            ⌜∀ r, is_Some (rmap' !! r)⌝ -∗
            ⌜rmap' !! ca0 = Some (WInt ECOMPARTMENTFAIL : LWord)⌝ -∗
            ⌜rmap' !! ca1 = Some (WInt 0 : LWord)⌝ -∗
            PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return -∗
            registers_pointsto rmap' -∗
            na_own cerise_nais F -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros (HF HFtrap Hdisj) "#Hinv_switcher #Hstatic Hres".
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    iMod "Hres" as (rmap Hfull_rmap) "(Hna & Hrmap & Hcont)".
    iDestruct (trap_entry_res_split F with "Hna") as "[Htok Hna]"; first done.
    iModIntro. iFrame "Htok". iIntros "!> Hout HPC".
    iApply (switcher_exception_path_spec Nswitcher F with
             "[$Hinv_switcher $Hstatic $HPC $Hrmap $Hout $Hna $Hcont]"); done.
  Qed.

  (** A fault in trusted code is safe: after exception entry, the exception
      entry of the switcher unwinds the call of the faulting compartment.
      No register needs to be safe. The resources come under an update at
      the time of the fault (for instance, to close an invariant). *)
  Lemma trap_safe_unwind
    (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (w : LWord) :
    Nswitcher ## N_trap ->
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
    iIntros (Hdisj Hfull_rmap Hframe) "#Hinv_switcher #Hstatic Hres".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
    iApply (interp_trap_safe with "Htrap Hres"); done.
  Qed.

  (** A fault that cannot happen is safe: the update yields a contradiction,
      which is eliminated at the time of the fault. *)
  Lemma trap_safe_absurd (w : LWord) :
    (|={⊤}=> False) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    iIntros "Hfalse".
    iApply trap_safe_entry_intro.
    iSplit; last by iIntros "!> %Hv".
    by iMod "Hfalse".
  Qed.

  (** The return-to-switcher entry point is safe to execute: the registers
      are re-filtered, then the return routine runs ([switcher_return_unwind]). *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp_expr interp (interp_cont interp) W C (WCap true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv_switcher #Hstatic] %cstk %Ws %Cs %rmap0
             [Hregs (HPC & Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)]".
    iPoseProof (switcher_mtcc_vec_safe Nswitcher Hdisj with "[$Hinv_switcher $Hstatic]")
      as "#Htrap".
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
    Nswitcher ## N_trap ->
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static
    ⊢ interp W C (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros (Hdisj) "[#Hinv #Hstatic]".
    rewrite interp_unfold /=.
    iSplit; first (iPureIntro; exact switcher_not_heap_range).
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "[$Hinv $Hstatic]"); done.
  Qed.


End Switcher_Exception_Stub.
