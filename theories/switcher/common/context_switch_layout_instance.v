From iris.proofmode Require Import proofmode.
From griotte Require Import context_switch_layout switcher_link.

(** * The context-switch layout of the switcher

    The save area of a user thread is the register save area of its
    trusted stack, without its word [hazardPointers], and its saved MIE is
    InterruptDisabled. A thread parked with a save area resumes with the
    registers and the MIE it holds. *)

(** The word [k] of a save area. *)
Definition save_area_word (ws : list LWord) (k : Z) : LWord := default lnull (ws !! Z.to_nat k).

(** The registers that a thread parked with the save area [ws] resumes
    with: x1–x15 from the words 1 to 15; [cnull] holds [lnull]. *)
Definition resume_regs_of (ws : list LWord) : LReg :=
  list_to_map
    ((λ r, (r, if decide (r = cnull) then lnull
               else save_area_word ws (TrustedStack_offset_reg r))) <$> all_registers).

Lemma resume_regs_of_dom ws : dom (resume_regs_of ws) = all_registers_s.
Proof.
  rewrite /resume_regs_of dom_list_to_map_L -list_fmap_compose /all_registers_s.
  f_equal.
Qed.

(** The values that a thread parked with the save area [ws] resumes with:
    its registers as [resume_regs_of], and its MIE the saved MPIE of the
    word [mstatus]. The PC is not constrained here: the resume path of the
    switcher fixes it. *)
Definition resume_ok_full (ws : list LWord) (v : resume_vals) : Prop :=
  v.(rv_regs) = resume_regs_of ws ∧
  v.(rv_mie) = mpie_of (get_a (save_area_word ws TrustedStack_offset_mstatus).(lw)).

Lemma resume_ok_full_dom ws v :
  resume_ok_full ws v → dom v.(rv_regs) = all_registers_s.
Proof. intros [-> _]. apply resume_regs_of_dom. Qed.

Section context_switch_layout_instance.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {swlayout : switcherLayout}.

  Lemma csl_full_posture_part t :
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (crit_link_full (UserThread t)) (crit_route_full (UserThread t)) ⊣⊢
    (∃ ws, ⌜saved_mie_ok ws⌝ ∗ save_area_holed (UserThread t) ws) ∗
    mtdc_lent_at (th := UserThread t).
  Proof.
    by rewrite (posture_part_user (UserThread t)) // /save_area_part /mtdc_lent_at /ceriseG_of.
  Qed.

  Lemma csl_full_link_disabled th σ :
    mie_st σ = InterruptDisabled →
    ⊢ @crit_link Σ th (crit_link_full th) σ.
  Proof. intros Hdis. rewrite crit_link_full_unfold /crit_link_def Hdis. done. Qed.

  Lemma csl_full_link_user_enabled t σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ (UserThread t) (crit_link_full (UserThread t)) σ ⊣⊢
    handover_res (ceriseg := ceriseG_of (UserThread t)) ∗
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (crit_link_full (UserThread t)) (crit_route_full (UserThread t)).
  Proof.
    intros Hen. rewrite crit_link_full_unfold /crit_link_def Hen.
    rewrite (posture_part_user (UserThread t)) //.
  Qed.

  Lemma csl_full_link_ctx_enabled σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ CtxSwitch (crit_link_full CtxSwitch) σ ⊢
    handover_res (ceriseg := ceriseG_of CtxSwitch).
  Proof.
    intros Hen. rewrite crit_link_full_unfold /crit_link_def Hen.
    case_decide; [by iIntros "[$ _]" | done].
  Qed.

  (** The save area of user thread [t] holds its saved-MIE fact. *)
  #[global] Instance context_switch_layout_full :
    ContextSwitchLayout Σ crit_link_full crit_route_full := {|
    save_area_at t ws := (⌜saved_mie_ok ws⌝ ∗ save_area_holed (UserThread t) ws)%I;
    resume_ok := resume_ok_full;
    csl_posture_part := csl_full_posture_part;
    csl_link_disabled := csl_full_link_disabled;
    csl_link_user_enabled := csl_full_link_user_enabled;
    csl_link_ctx_enabled := csl_full_link_ctx_enabled;
  |}.
End context_switch_layout_instance.
