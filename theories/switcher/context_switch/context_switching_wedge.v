From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import logrel switcher_preamble handoff switcher_link.
From griotte Require Import context_switching_support context_switching_hyps.

(** * The wedge of the context-switch thread

    A fault of the context-switch thread enters the switcher's trap vector
    with mtdc at its home, zero. The exception entry swaps zero into [csp]
    and branches to [.Lexception_reentered], which wedges mtcc with an
    untagged word and reads through the null [csp]: the read faults, trap
    entry installs the untagged mtcc, whose fetch faults again, and the
    machine stops. No memory is written. *)

Section ctx_wedge.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg : sealStoreG Σ} {stsg : STSG Σ} {relg : relGS Σ} {cstackg : CSTACKG Σ}
    {cthreads : CmptThreads} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (* TODO: move to switcher_link.v *)
  (** [cspecialrw r, mtdc, r] at the context-switch thread, with its
      token: the ghost value is then its home, and the token is paid,
      whatever is written. *)
  Lemma wp_specialrw_swap_mtdc_ctx_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r
      (v : LWord) m m' dq (Φ : tval CtxK → iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    mtdc_match m' v →
    ▷ PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
    ▷ pc_a ↦ₐ{dq} w ∗
    ▷ r ↦ᵣ[CtxSwitch] v ∗
    ▷ mtdc ↦ₜ[CtxSwitch] m ∗
    ▷ unwedged ∗
    ▷ mtdc_lent_at (th := CtxSwitch) -∗
    ▷ (∀ vm : LWord,
         ⌜mtdc_match m vm⌝ ∗
         PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         r ↦ᵣ[CtxSwitch] vm ∗
         mtdc ↦ₜ[CtxSwitch] m' ∗
         unwedged -∗
         Φ NextIV) -∗
    WP Instr Executable @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm') "(HPC & Hpc_a & Hr & Hmtdc & HU & Hlent) HΦ".
    iApply (wp_specialrw_swap_mtdc_link (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
              (CL := crit_link_full CtxSwitch) _ _ _ _ _ _ _ _ _ _ _ m m' _ unwedged unwedged
              (mtdc_lent_at (th := CtxSwitch)) True%I
             with "[$HPC $Hpc_a $Hr $Hmtdc $HU $Hlent]"); try done.
    - apply ctx_link_transfer_unwedged.
    - iIntros "[_ Hl] !>". iSplitL; [by iRight | done].
    - iNext. iIntros (vm) "(Hmatch & HPC & Hpc_a & Hr & Hmtdc & HU & _)".
      iApply "HΦ". iFrame.
  Qed.

  (* TODO: move to switcher_link.v *)
  (** The part of the context-switch thread. *)
  Lemma posture_part_ctx :
    @posture_part Σ MP (ceriseG_of CtxSwitch) CtxSwitch (crit_link_full CtxSwitch)
      (crit_route_full CtxSwitch) ⊣⊢
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    mtdc_lent_at (th := CtxSwitch).
  Proof. done. Qed.

  (** Zero, written to mtcc, is untagged. *)
  #[local] Lemma legalise_mtcc_zero : get_tag (legalise mtcc (WInt 0)) = false.
  Proof. reflexivity. Qed.

  (** [cspecialrw csp, mtdc, csp] at the context-switch thread, mtdc at its
      home zero, then [beqz sp]: [csp] receives zero, mtdc the faulting
      stack pointer, and the PC reaches [.Lexception_reentered]; the mtdc
      token is paid. *)
  Lemma ctx_fault_swap (wcsp : LWord) E Φ :
    PC ↦ₚ[CtxSwitch] switcher_label_pc "exception_entry_asm" ∗
    switcher_code_at CtxSwitch ∗
    csp ↦ᵣ[CtxSwitch] wcsp ∗
    mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    mtdc_lent_at (th := CtxSwitch) ∗
    unwedged ∗
    ▷ ( PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_reentered" ∗
        csp ↦ᵣ[CtxSwitch] lword_of_word (WInt 0) ∗
        mtdc ↦ₜ[CtxSwitch] ExceptionScratch wcsp ∗
        unwedged -∗
        WP Exec @[CtxSwitch] E {{ Φ }} )
    ⊢ WP Exec @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros "(HPC & #Hswitcher & Hcsp & Hmtdc & Hlent & HU & Hpost)".
    pin_thread_instances CtxSwitch.
    switcher_open_label "exception_entry_asm" "Hswitcher" as "Hcode" a_entry Ha_entry.
    (* SpecialRW csp mtdc csp *)
    iInstrApply "Hcode"
      (wp_specialrw_swap_mtdc_ctx_open _ _ _ _ _ _ _ _ _ csp wcsp
         (ExceptionScratch (lword_of_word (WInt 0))) (ExceptionScratch wcsp))
      with "[$HPC $Hcsp $Hmtdc $HU $Hlent]" as (vm) "(%Hmatch & HPC & Hcsp & Hmtdc & HU)".
    { apply mtdc_match_ExceptionScratch. }
    cbn in Hmatch; subst vm.
    (* Jeq .Lexception_reentered csp 0 *)
    iInstr "Hcode".
    { jump_to (a_switcher_call ^+ switcher_label_offset ".Lexception_reentered")%a
        by switcher_addr_eq. }
    iApply "Hpost". iFrame.
  Qed.

  (** From [.Lexception_reentered] at the context-switch thread, with MIE
      disabled and what it hands over: mtcc is wedged, the read through the
      null [csp] faults, trap entry installs the untagged mtcc, whose fetch
      faults, and the machine stops. *)
  Lemma ctx_wedge_spec (wcsp : LWord) :
    PC ↦ₚ[CtxSwitch] switcher_label_pc ".Lexception_reentered" ∗
    csp ↦ᵣ[CtxSwitch] wcsp ∗
    MIE ↦ₜ[CtxSwitch] InterruptDisabled ∗
    handover_res (ceriseg := ceriseG_of CtxSwitch) ∗
    switcher_code_at CtxSwitch
    ⊢ safe[CtxSwitch].
  Proof.
    iIntros "(HPC & Hcsp & HMIE & Hho & #Hswitcher)".
    pin_thread_instances CtxSwitch.
    iDestruct (handover_res_unfold with "Hho") as (p c v b) "(_ & HU & Hvol)".
    switcher_open_label ".Lexception_reentered" "Hswitcher" as "Hcode" a_re Ha_re.
    (* Mov csp 0 *)
    iInstr "Hcode".
    destruct (decide (csp = cnull)) as [Hcsp_null|_]; first done.
    (* SpecialRW cnull mtcc csp *)
    pose proof legalise_mtcc_zero as Hlegal.
    iInstrStart "Hcode".
    iInstrApply (wp_writesr_mtcc_wedge _ _ _ _ _ _ _ _ _ csp (WInt 0))
      with "[$HPC $Hcsp $HU]" as "(HPC & Hcsp & #Hwedged)".
    iDestruct (map_of_regs_1 with "Hcsp") as "Hmap".
    (* CLoad csp csp 0 *)
    iInstrStart "Hcode".
    iInstrApply (wp_load_fail_const_imm _ _ _ _ _ _ _ _ csp csp 0
                   {[csp := lword_of_word (WInt 0)]})
      with "[$HPC $Hmap]" as "(HPC & _)".
    1,2: done.
    (* The PC of the switcher is tagged: trap entry installs the wedged mtcc *)
    iApply (wp_trap_wedged with "Hwedged HPC HMIE Hvol"); first done.
    iIntros "!>" (wv Hwv) "HPC _ _".
    (* The fetch at the untagged mtcc faults, and the machine stops *)
    iApply (wp_bind (@fill (tlang_ectx _) [SeqCtx])).
    iApply (wp_notCorrectPC_tag with "HPC"); first done.
    iIntros "!> HPC /=".
    iApply (wp_trap_halt_wedged with "Hwedged HPC"); first done.
    iIntros "!> _". by rewrite HO_faulted.
  Qed.

  (** The trap vector is safe for any fault of the context-switch thread,
      from the switcher's code and the trap vector's address. *)
  Lemma ctx_trap_vector_safe_holds :
    mtcc_vec = Cap XSRW_ Local b_switcher e_switcher
                 (a_switcher_call ^+
                    asm_label_offset switcher_asm ".Lswitch_csp_check" "exception_entry_asm")%a →
    switcher_code_at CtxSwitch ⊢ ctx_trap_vector_safe.
  Proof.
    intros Hvec. rewrite /ctx_trap_vector_safe /trap_vector_safe /trap_vector_safe_pre.
    iIntros "#Hcode !>" (cstk regs w Hfull) "_ HPC HMIE Hpost Hregs _ _".
    pin_thread_instances CtxSwitch.
    iDestruct "Hpost" as (b c v) "(_ & _ & Hpost)".
    iDestruct (posture_res_gen_unfold with "Hpost")
      as "[(%p & %c' & %v' & %b' & _ & _ & _ & _ & Hho) Hpart]".
    iEval (rewrite posture_part_ctx) in "Hpart".
    iDestruct "Hpart" as "[Hmtdc Hlent]".
    iDestruct "Hho" as "(Hcrit & HU & Hvol)".
    destruct (Hfull csp) as [wcsp Hwcsp].
    iDestruct (big_sepM_delete (λ k y, k ↦ᵣ[CtxSwitch] y)%I _ csp with "Hregs")
      as "[Hcsp _]"; first exact Hwcsp.
    rewrite Hvec.
    iApply (ctx_fault_swap wcsp
             with "[$HPC $Hcode $Hcsp $Hmtdc $Hlent $HU HMIE Hcrit Hvol]").
    iIntros "!> (HPC & Hcsp & _ & HU)".
    iApply (ctx_wedge_spec with "[$HPC $Hcsp $HMIE $Hcode Hcrit HU Hvol]").
    iApply (handover_res_intro p c' v' b'). iFrame.
  Qed.
End ctx_wedge.
