From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte Require Import switcher_preamble switcher_exception_states handoff switcher_link.
From griotte Require Import context_switch_layout_instance.

(** * Support of the paths of the context-switch thread

    The save area that the exception entry of the context-switch thread
    writes for a parked user thread, the mtdc swaps of the context-switch
    thread, and the facts of the state interpretation they use. *)

(** In a section with no thread, the instance search of [iInstr] finds no
    instance: pin those of thread [th] at the start of the proof. It poses
    [th_pin], [cg], [CLc], [CRc]; the instance search takes the most recent
    local [Thread]. *)
Ltac pin_thread_instances th :=
  lazymatch goal with
  | ceriseb : ceriseBaseG ?Σ |- _ =>
      pose (th_pin := th);
      pose (cg := @ceriseG_of Σ ceriseb th);
      pose (CLc := crit_link_full (Σ := Σ) (ceriseb := ceriseb) th);
      pose (CRc := crit_route_full (Σ := Σ) (ceriseb := ceriseb) th)
  end.

(** The code of the switcher, at the instance of the thread [th], for the
    sections with no thread. *)
Notation switcher_code_at th :=
  (codefrag_pers (ceriseg := ceriseG_of th) a_switcher_call switcher_instrs).

Section ctx_support.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}.

  (** The home of user thread [B]'s mtdc: its trusted stack. *)
  Definition tstack_home (B : nat) : mtdc_val :=
    Capₗ RWL _ (@b_trusted_stack (tlayout_of (UserThread B)))
      (@e_trusted_stack (tlayout_of (UserThread B))) (@b_trusted_stack (tlayout_of (UserThread B))).

  (** The trusted stack capability of user thread [B], at locality [g]. *)
  Definition tstack_cap (g : Locality) (B : nat) : Word :=
    Cap RWL g (@b_trusted_stack (tlayout_of (UserThread B)))
      (@e_trusted_stack (tlayout_of (UserThread B))) (@b_trusted_stack (tlayout_of (UserThread B))).

  (** The words x1–x15 of a register map, in the order of the save area. *)
  Definition spill_words (lreg : LReg) : list LWord :=
    (λ r, default lnull (lreg !! r)) <$>
      [cra; csp; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5].

  (** The save area [ws] after the spill of the registers [lreg], MEPCC
      [wm], mstatus (MIE disabled, MPIE [b]) and the cause [cause]. *)
  Definition ctx_spill (ws : list LWord) (lreg : LReg) (wm : LWord) (b : InterruptStatus)
      (cause : Z) : list LWord :=
    exception_spill ws wm (spill_words lreg)
      (lword_of_word (WInt (mstatus_enc InterruptDisabled b))) (lword_of_word (WInt cause)).

  (** The save area [ws] after the rejoin alone: the stack pointer [wcsp],
      MEPCC, mstatus and the cause; the register words are kept. *)
  Definition rejoin_spill (ws : list LWord) (wcsp wm : LWord) (b : InterruptStatus)
      (cause : Z) : list LWord :=
    <[0 := wm]> (<[2 := wcsp]>
      (<[17 := lword_of_word (WInt (mstatus_enc InterruptDisabled b))]>
        (<[18 := lword_of_word (WInt cause)]> ws))).

  (** The words of the save area: the PC, mstatus and the cause, and the
      registers, at their offsets. *)
  Lemma resume_ok_ctx_spill (ws : list LWord) (lreg : LReg) (wm : LWord) (b : InterruptStatus)
      (c : Z) :
    length ws = 21%nat →
    dom lreg = all_registers_s →
    lreg !! cnull = Some lnull →
    resume_regs_of (ctx_spill ws lreg wm b c) = lreg ∧
    saved_mie_ok (ctx_spill ws lreg wm b c) ∧
    mpie_of (get_a (save_area_word (ctx_spill ws lreg wm b c) TrustedStack_offset_mstatus).(lw))
      = b.
  Proof.
    intros Hlen Hdom Hnull.
    destruct ws as
      [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10
      [|w11 [|w12 [|w13 [|w14 [|w15 [|w16 [|w17 [|w18 [|w19 [|w20 [] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ];
      try done.
    split_and!.
    - apply map_eq. intros r. rewrite /resume_regs_of.
      assert (is_Some (lreg !! r)) as [v Hv].
      { apply elem_of_dom. rewrite Hdom. apply elem_of_list_to_set, all_registers_correct. }
      rewrite Hv. apply elem_of_list_to_map_1.
      { rewrite -list_fmap_compose. apply all_registers_NoDup. }
      apply list_elem_of_fmap. exists r. split; last apply all_registers_correct.
      f_equal. case_decide as Hne.
      { subst r. rewrite Hnull in Hv. by simplify_eq. }
      pose proof (all_registers_correct r) as Hr.
      rewrite /all_registers !elem_of_cons elem_of_nil in Hr.
      repeat (destruct Hr as [-> | Hr]);
        first [ by destruct Hne | done
              | rewrite /save_area_word /ctx_spill /exception_spill /spill_words /=; by rewrite Hv ].
    - intros w Hw. rewrite /ctx_spill /exception_spill /= in Hw. simplify_eq.
      by rewrite /= mie_of_mstatus_enc.
    - by rewrite /save_area_word /ctx_spill /exception_spill /= mpie_of_mstatus_enc.
  Qed.

  (** The save area of [th], cell by cell. *)
  Lemma save_area_holed_cells (th : Thread) (ws : list LWord) :
    length ws = 21%nat →
    save_area_holed th ws ⊣⊢
    [∗ list] k ↦ w ∈ ws,
      if decide (k = Z.to_nat TrustedStack_offset_hazardPointers) then emp
      else (@b_trusted_stack (tlayout_of th) ^+ (k : Z))%a ↦ₐ w.
  Proof.
    intros Hlen. rewrite /save_area_holed.
    pose proof (trusted_stack_frames_fit (tlayout := tlayout_of th)) as [n Hfit].
    etrans.
    { apply (big_sepL2_proper _
               (λ k _ w, if decide (k = Z.to_nat TrustedStack_offset_hazardPointers) then emp
                         else (@b_trusted_stack (tlayout_of th) ^+ (k : Z))%a ↦ₐ w)%I).
      intros k a w Ha Hw.
      pose proof (lookup_lt_Some _ _ _ Hw) as Hk. rewrite Hlen in Hk.
      rewrite (finz_seq_between_lookup _ _ k 21) in Ha; [|lia|tstack_unfold; solve_addr].
      by simplify_eq. }
    rewrite big_sepL2_const_sepL_r finz_seq_between_length /finz.dist Hlen.
    iSplit; [iIntros "[_ $]" | iIntros "$"; iPureIntro; tstack_unfold; solve_addr].
  Qed.

End ctx_support.

(** The facts of the state interpretation that the parks use. *)
Section ctx_support_si.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** MEPCC holds a word that is valid as a PC. *)
  Lemma mepcc_word_ok E (w : LWord) :
    mepcc ↦ₓ w ⊢ |~{E}~> (mepcc ↦ₓ w ∗ ⌜pc_ok w.(lw)⌝).
  Proof.
    iIntros "Hm". iApply (si_upd_ghost with "Hm"). iIntros (σ) "Hσ Hm".
    iAssert (⌜pc_ok w.(lw)⌝)%I as %Hok.
    { iDestruct (SI_open with "Hσ") as (lpc lreg lsreg lmem R C) "(%Her & _ & _ & Hsys & _)".
      iDestruct (sys_interp_valid_1 with "Hsys Hm") as %[Hv _].
      iPureIntro. by eapply (er_sreg_pc_ok _ _ _ _ _ _ _ Her mepcc). }
    by iFrame.
  Qed.

  (** [cnull] holds [lnull]. *)
  Lemma cnull_lnull E (w : LWord) :
    cnull ↦ᵣ w ⊢ |~{E}~> (cnull ↦ᵣ w ∗ ⌜w = lnull⌝).
  Proof.
    iIntros "Hcnull". iApply (si_upd_ghost with "Hcnull"). iIntros (σ) "Hσ Hcnull".
    iAssert (⌜w = lnull⌝)%I as %Hw.
    { iDestruct (SI_open with "Hσ") as (lpc lreg lsreg lmem R C) "(%Her & _ & Hr & _)".
      iDestruct (gen_heap_valid with "Hr Hcnull") as %Hv.
      iPureIntro. by eapply (er_cnull _ _ _ _ _ _ _ Her). }
    by iFrame.
  Qed.
End ctx_support_si.
