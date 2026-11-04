From iris.proofmode Require Import proofmode.
From griotte Require Import rules.
From griotte Require Import switcher_link context_switch_layout context_switch_layout_instance.
From griotte Require Import ctx_support.

(** * Support of the resume path of the context-switch thread

    The unseal of a word with the key in the destination register, the
    mtdc write of the context-switch thread from its home, the PC that the
    resume path installs, and the save area and the resume values of the
    context-switch layout of the switcher, by their definitions. *)

Section ctx_resume_unseal.
  Context
    {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread}
    {CL : ∀ t, CritLink Σ t} `{MP : MachineParameters}.

  (* TODO: move to wp_rules_interp.v *)
  (** [UnSeal r1 r1 r2], the key in [r1], which receives the result: the
      three outcomes of [wp_unseal_unknown_sealed]. *)
  Lemma wp_unseal_unknown_sealed_dst_key {dq : dfrac} E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2
      psr gsr bsr esr asr wsealed :
    decodeInstrW wi.(lw) = UnSeal r1 r1 r2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true →
    (bsr <= asr < esr)%ot →
    r1 ≠ r2 →
    r1 ≠ cnull →
    r2 ≠ cnull →

    {{{ PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        r1 ↦ᵣ[th] SealRange psr gsr bsr esr asr ∗
        r2 ↦ᵣ[th] wsealed }}}
      Instr Executable @[th] E
    {{{ retv, RET retv;
        (⌜retv = NextIV⌝ ∗
         PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
         pc_a ↦ₐ{dq} wi ∗
         r1 ↦ᵣ[th] lclear_tag wsealed ∗
         r2 ↦ᵣ[th] wsealed ∗
         ⌜is_sealed wsealed.(lw) = false⌝) ∨
        (∃ ot wsb π,
           ⌜retv = NextIV⌝ ∗
           PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
           pc_a ↦ₐ{dq} wi ∗
           r1 ↦ᵣ[th] WSealable (unseal_sb gsr wsb) @@? π ∗
           r2 ↦ᵣ[th] wsealed ∗
           ⌜wsealed = WSealed ot wsb @@? π⌝ ∗
           ⌜get_tag_sealable wsb = true⌝ ∗
           ⌜withinBounds bsr esr ot = true⌝) ∨
        ∃ ot sb π,
          ⌜retv = NextIV⌝ ∗
          PC ↦ₚ[th] Cap pc_p pc_g pc_b pc_e pc_a' ∗
          pc_a ↦ₐ{dq} wi ∗
          r1 ↦ᵣ[th] WSealable (clear_tag_sealable (unseal_sb gsr sb)) @@? π ∗
          r2 ↦ᵣ[th] wsealed ∗
          ⌜wsealed = WSealed ot sb @@? π⌝ ∗
          ⌜get_tag_sealable sb && withinBounds bsr esr ot = false⌝ }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr Hr12 Hr1_null Hr2_null φ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".
    iDestruct (map_of_regs_2 with "Hr1 Hr2") as "[Hmap %]".
    iApply (wp_UnSeal with "[$HPC $Hmap $Hpc_a]"); eauto.
    { by unfold regs_of, operands_of; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hmap)".
    destruct Hspec as [p g b e a πs o sb π Hsr' Hsd Htag Hperm Hwb Hinc ->
                      |t p g b e a πs o sb π Hsr' Hsd Hinvalid Hinc ->
                      | w1 w2 Hw1 Hw2 Hk Hinc -> | Hfail].
    - iApply "Hφ". iRight. iLeft.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      iExists o, sb, π.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    - iApply "Hφ". iRight. iRight.
      rewrite !llookup_reg_not_cnull // in Hsr' Hsd. simplify_map_eq.
      iExists o, sb, π.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      match goal with Hinvalid : _ && withinBounds _ _ _ = false |- _ =>
        rewrite Hpsr !andb_true_r /= in Hinvalid
      end.
      iFrame; done.
    - iApply "Hφ". iLeft.
      rewrite !llookup_reg_not_cnull // in Hw1 Hw2. simplify_map_eq.
      rewrite !insert_insert_eq.
      iRegsMap "Hmap".
      iFrame; done.
    - exfalso. destruct Hfail; try incrementPC_inv; simplify_map_eq; congruence.
  Qed.
End ctx_resume_unseal.

Section ctx_resume_mtdc.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (* TODO: move to switcher_link.v *)
  (** [cspecialw mtdc, src] at the context-switch thread, from its home
      zero: its token is paid into the clause of mtdc. *)
  Lemma wp_writesr_mtdc_ctx_open E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w src (v : LWord) m' dq
      (Φ : tval CtxK → iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW cnull mtdc (inr src) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    mtdc_home_at (th := CtxSwitch) = ExceptionScratch (lword_of_word (WInt 0)) →
    mtdc_match m' v →
    ▷ PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
    ▷ pc_a ↦ₐ{dq} w ∗
    ▷ src ↦ᵣ[CtxSwitch] v ∗
    ▷ mtdc ↦ₜ[CtxSwitch] ExceptionScratch (lword_of_word (WInt 0)) ∗
    ▷ mtdc_lent_at (th := CtxSwitch) ∗
    ▷ unwedged -∗
    ▷ (PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
       pc_a ↦ₐ{dq} w ∗
       src ↦ᵣ[CtxSwitch] v ∗
       mtdc ↦ₜ[CtxSwitch] m' ∗
       unwedged -∗
       Φ NextIV) -∗
    WP Instr Executable @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hsrc Hhome Hmatch) "(HPC & Hpc_a & Hsrc & Hmtdc & HL & HU) HΦ".
    iApply (wp_writesr_mtdc_link (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
              (CL := crit_link_full CtxSwitch) _ _ _ _ _ _ _ _ _ _ _
              (ExceptionScratch (lword_of_word (WInt 0))) m' _ unwedged unwedged
              (mtdc_lent_at (th := CtxSwitch)) True%I
             with "[$HPC $Hpc_a $Hsrc $Hmtdc $HU $HL]"); try done.
    - apply ctx_link_transfer_unwedged.
    - rewrite -Hhome. apply mtdc_clause_open.
    - iNext. iIntros "(HPC & Hpc_a & Hsrc & Hmtdc & HU & _)". iApply "HΦ". iFrame.
  Qed.
End ctx_resume_mtdc.

(* TODO: move to context_switch_layout_instance.v *)
(** The word a Lea writes is [lea_word] of its source. *)
Lemma lea_result_lw (w w' : LWord) (z : Z) :
  lea_result w z = Some w' → w'.(lw) = lea_word w.(lw) z.
Proof.
  destruct w as [w π]. rewrite /lea_result /lea_word /=.
  intros Hres. destruct w as [| [ ] | | ]; repeat case_match; by simplify_eq.
Qed.

(* TODO: move to context_switch_layout_instance.v *)
(** The resume PC of the save area [ws]: the saved mepcc, one word further
    after an [ecall], legalised. *)
Lemma resume_pc_word_install (ws : list LWord) :
  length ws = 21%nat →
  (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) = MCAUSE_ECALL_MACHINE →
   legalise_pc (lea_word (save_area_word ws TrustedStack_offset_mepcc).(lw) 1) =
   resume_pc_word ws) ∧
  (get_a (save_area_word ws TrustedStack_offset_mcause).(lw) ≠ MCAUSE_ECALL_MACHINE →
   legalise_pc (save_area_word ws TrustedStack_offset_mepcc).(lw) = resume_pc_word ws).
Proof.
  intros _. rewrite /resume_pc_word. split; intros Hc.
  - by rewrite decide_True.
  - by rewrite decide_False.
Qed.

Section ctx_resume_layout.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  (* TODO: move to context_switch_layout_instance.v *)
  (** The registers of the save area [ws], [cnull] apart, are the
      registers that a thread parked with [ws] resumes with. *)
  Lemma regs_resume_regs_of (th : Thread) (ws : list LWord) :
    length ws = 21%nat →
    cnull ↦ᵣ[th] lnull ∗
    ([∗ list] r ∈ exception_spill_regs ++ [csp],
       r ↦ᵣ[th] save_area_word ws (TrustedStack_offset_reg r)) ⊣⊢
    regs[th] (resume_regs_of ws).
  Proof.
    intros _. rewrite /resume_regs_of.
    rewrite big_sepM_list_to_map; last first.
    { rewrite -list_fmap_compose. apply all_registers_NoDup. }
    rewrite big_sepL_fmap.
    rewrite (big_opL_permutation _ all_registers (cnull :: exception_spill_regs ++ [csp]));
      last by apply (bool_decide_unpack _).
    rewrite big_sepL_cons.
    assert (cnull ∉ exception_spill_regs ++ [csp]) as Hnull by (by apply (bool_decide_unpack _)).
    f_equiv.
    - cbn. by case_decide.
    - apply big_sepL_proper. intros k r Hr. cbn.
      case_decide as Heq; last done.
      subst r. exfalso. apply Hnull. by eapply list_elem_of_lookup_2.
  Qed.

  (* TODO: move to context_switch_layout_instance.v *)
  (** The save area of user thread [t] in the context-switch layout of the
      switcher. *)
  Lemma save_area_at_full (t : nat) (ws : list LWord) :
    @save_area_at Σ MP ceriseb crit_link_full crit_route_full context_switch_layout_full t ws ⊣⊢
    ⌜saved_mie_ok ws⌝ ∗ save_area_holed (UserThread t) ws.
  Proof. reflexivity. Qed.

  (* TODO: move to context_switch_layout_instance.v *)
  (** The resume values of the context-switch layout of the switcher. *)
  Lemma resume_ok_full_eq (ws : list LWord) (v : resume_vals) :
    @resume_ok Σ MP ceriseb crit_link_full crit_route_full context_switch_layout_full ws v ↔
    resume_ok_full ws v.
  Proof. reflexivity. Qed.
End ctx_resume_layout.
