From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import switcher_preamble switcher_exception_states handoff switcher_link.
From griotte Require Import context_switch_layout_instance.

(** * Support of the paths of the context-switch thread

    The save area that the exception entry of the context-switch thread
    writes for a parked user thread, the mtdc swaps of the context-switch
    thread, and the facts of the state interpretation they use. *)

(** In a section with no thread, the instance search of [iInstr] finds no
    instance: pin those of thread [th] at the start of the proof. *)
Ltac pin_thread_instances th :=
  lazymatch goal with
  | ceriseb : ceriseBaseG ?Σ |- _ =>
      pose (th_pin := th);
      pose (cg := @ceriseG_of Σ ceriseb th);
      pose (CLc := crit_link_full (Σ := Σ) (ceriseb := ceriseb) th);
      pose (CRc := crit_route_full (Σ := Σ) (ceriseb := ceriseb) th)
  end.

(* TODO: move to resources.v *)
#[global] Instance mtdc_val_eq_dec : EqDecision mtdc_val.
Proof. solve_decision. Qed.

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

  (* TODO: move to context_switch_layout.v *)
  (** What a thread hands over, at given values, is the same at the
      instance of any thread. *)
  Lemma handover_at_thread_indep (th th' : Thread) (p c : LWord) (v : Z) (b : InterruptStatus) :
    handover_at (ceriseg := ceriseG_of th) p c v b ⊣⊢
    handover_at (ceriseg := ceriseG_of th') p c v b.
  Proof. rewrite /handover_at /volatile_csr_at /ceriseG_of. reflexivity. Qed.

  (* TODO: move to switcher_link.v *)
  (** An mtdc write of the context-switch thread keeps its link, given the
      unwedged token: the token excludes the branch at InterruptEnabled,
      whose [handover_res] holds it. *)
  Lemma ctx_link_transfer_unwedged :
    @link_transfer Σ CtxSwitch (crit_link_full CtxSwitch) mtdc_written unwedged unwedged.
  Proof.
    iIntros (σ σ' Hw) "[Hl HU]".
    rewrite !crit_link_full_unfold /crit_link_def /mtdc_written Hw.
    destruct (mie_st σ).
    - iAssert (@handover_res Σ (ceriseG_of CtxSwitch)) with "[Hl]" as "Hho".
      { case_decide; [iDestruct "Hl" as "[$ _]" | iExact "Hl"]. }
      iDestruct (handover_res_unfold with "Hho") as (p c v b) "(_ & HU' & _)".
      iDestruct (unwedged_excl with "HU HU'") as %[].
    - iModIntro. by iFrame.
  Qed.

  (* TODO: move to switcher_link.v *)
  (** [cspecialrw r, mtdc, r] at the context-switch thread, from an mtdc
      value [m] that is not its home: the token of the context-switch
      thread comes out if the written value [m'] is its home. *)
  Lemma wp_specialrw_swap_mtdc_ctx_away E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r
      (v : LWord) m m' dq (Φ : tval CtxK → iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m ≠ mtdc_home_at (th := CtxSwitch) →
    mtdc_match m' v →
    ▷ PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
    ▷ pc_a ↦ₐ{dq} w ∗
    ▷ r ↦ᵣ[CtxSwitch] v ∗
    ▷ mtdc ↦ₜ[CtxSwitch] m ∗
    ▷ unwedged -∗
    ▷ (∀ vm : LWord,
         ⌜mtdc_match m vm⌝ ∗
         PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         r ↦ᵣ[CtxSwitch] vm ∗
         mtdc ↦ₜ[CtxSwitch] m' ∗
         unwedged ∗
         (if decide (m' = mtdc_home_at (th := CtxSwitch)) then mtdc_lent_at (th := CtxSwitch)
          else True) -∗
         Φ NextIV) -∗
    WP Instr Executable @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm Hm') "(HPC & Hpc_a & Hr & Hmtdc & HU) HΦ".
    iApply (wp_specialrw_swap_mtdc_link (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
              (CL := crit_link_full CtxSwitch) _ _ _ _ _ _ _ _ _ _ _ m m' _ unwedged unwedged
              True%I (if decide (m' = mtdc_home_at (th := CtxSwitch))
                      then mtdc_lent_at (th := CtxSwitch) else True)%I
             with "[$HPC $Hpc_a $Hr $Hmtdc $HU]"); try done.
    - apply ctx_link_transfer_unwedged.
    - case_decide as Hhome.
      + subst m'. by apply mtdc_clause_close.
      + by apply mtdc_clause_ex.
  Qed.

  (* TODO: move to switcher_link.v *)
  (** [cspecialrw r, mtdc, r] at the context-switch thread, writing its
      home: its token comes back, or stays with it if the home was already
      there. *)
  Lemma wp_specialrw_swap_mtdc_ctx_home E pc_p pc_g pc_b pc_e pc_a pc_π pc_a' w r
      (v : LWord) m m' dq (Φ : tval CtxK → iProp Σ) :
    decodeInstrW w.(lw) = SpecialRW r mtdc (inr r) →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    has_sreg_access pc_p = true →
    (pc_a + 1)%a = Some pc_a' →
    r ≠ cnull →
    m' = mtdc_home_at (th := CtxSwitch) →
    mtdc_match m' v →
    ▷ PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
    ▷ pc_a ↦ₐ{dq} w ∗
    ▷ r ↦ᵣ[CtxSwitch] v ∗
    ▷ mtdc ↦ₜ[CtxSwitch] m ∗
    ▷ unwedged ∗
    ▷ (if decide (m = mtdc_home_at (th := CtxSwitch)) then mtdc_lent_at (th := CtxSwitch)
       else True) -∗
    ▷ (∀ vm : LWord,
         ⌜mtdc_match m vm⌝ ∗
         PC ↦ₚ[CtxSwitch] Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π ∗
         pc_a ↦ₐ{dq} w ∗
         r ↦ᵣ[CtxSwitch] vm ∗
         mtdc ↦ₜ[CtxSwitch] m' ∗
         unwedged ∗
         mtdc_lent_at (th := CtxSwitch) -∗
         Φ NextIV) -∗
    WP Instr Executable @[CtxSwitch] E {{ Φ }}.
  Proof.
    iIntros (Hinstr Hvpc Hxsr Hpca' Hr Hm' Hmatch) "(HPC & Hpc_a & Hr & Hmtdc & HU & HL) HΦ".
    iApply (wp_specialrw_swap_mtdc_link (ceriseg := ceriseG_of CtxSwitch) (th := CtxSwitch)
              (CL := crit_link_full CtxSwitch) _ _ _ _ _ _ _ _ _ _ _ m m' _ unwedged unwedged
              (if decide (m = mtdc_home_at (th := CtxSwitch))
               then mtdc_lent_at (th := CtxSwitch) else True)%I
              (mtdc_lent_at (th := CtxSwitch))
             with "[$HPC $Hpc_a $Hr $Hmtdc $HU $HL]"); try done.
    - apply ctx_link_transfer_unwedged.
    - subst m'. case_decide as Hhome.
      + subst m. iIntros "[$ $]". done.
      + by apply mtdc_clause_close.
  Qed.

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

  (** The save area of [th], of a list of 21 words, cell by cell. *)
  Lemma save_area_holed_explicit (th : Thread)
      (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 : LWord) :
    save_area_holed th
      [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9; w10; w11; w12; w13; w14; w15; w16; w17; w18;
       w19; w20] ⊣⊢
    @b_trusted_stack (tlayout_of th) ↦ₐ w0 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 1)%a ↦ₐ w1 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 2)%a ↦ₐ w2 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 3)%a ↦ₐ w3 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 4)%a ↦ₐ w4 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 5)%a ↦ₐ w5 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 6)%a ↦ₐ w6 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 7)%a ↦ₐ w7 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 8)%a ↦ₐ w8 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 9)%a ↦ₐ w9 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 10)%a ↦ₐ w10 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 11)%a ↦ₐ w11 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 12)%a ↦ₐ w12 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 13)%a ↦ₐ w13 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 14)%a ↦ₐ w14 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 15)%a ↦ₐ w15 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 17)%a ↦ₐ w17 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 18)%a ↦ₐ w18 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 19)%a ↦ₐ w19 ∗
    (@b_trusted_stack (tlayout_of th) ^+ 20)%a ↦ₐ w20.
  Proof.
    rewrite save_area_holed_cells //.
    rewrite (_ : Z.to_nat TrustedStack_offset_hazardPointers = 16%nat); last done.
    cbn. rewrite finz_add_0_default.
    repeat (case_decide; try (exfalso; lia)).
    iSplit.
    - iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & _ & $ & $ & $ & $ & _)".
    - iIntros "($ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $ & $)".
  Qed.

End ctx_support.

(** The facts of the state interpretation that the parks use. *)
Section ctx_support_si.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (* TODO: move to rules_vcsr.v *)
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

  (* TODO: move to rules_base.v *)
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
