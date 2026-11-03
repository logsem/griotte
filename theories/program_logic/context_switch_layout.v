From iris.proofmode Require Import proofmode.
From griotte Require Export handoff.

(** * The context-switch layout

    What the switches between threads need to know about the switcher, for
    the link families [CL], [CR]: the register save area of a user thread
    and the values a thread parked with it may resume with, the agreement
    of the save area with the posture part of [CR], and the shape of the
    links at each value of MIE. The switcher gives the instance. *)
Class ContextSwitchLayout Σ `{MP : MachineParameters} {ceriseb : ceriseBaseG Σ}
    (CL : ∀ t, CritLink Σ t) (CR : ∀ t, @CritRoute Σ MP (ceriseG_of t) t (CL t)) := {
  (** The save area of user thread [t], holding [ws], with the facts the
      switcher keeps about it; among them, its saved MIE is
      InterruptDisabled. *)
  save_area_at : nat → list LWord → iProp Σ;
  (** The values [v] that a thread parked with the save area [ws] may
      resume with. *)
  resume_ok : list LWord → resume_vals → Prop;
  (** The posture part of a user thread is its save area and its mtdc
      token. The interrupt, yield and exit hand-ins take the token out of
      the parked thread's posture, to pin its mtdc at home, and put it back;
      resuming a suspended thread builds its posture part from its save
      area. *)
  csl_posture_part t :
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (CL (UserThread t)) (CR (UserThread t)) ⊣⊢
    (∃ ws, save_area_at t ws) ∗
    mtdc_lent_at (th := UserThread t);
  (** With interrupts disabled, the link of any thread is trivial. Every
      hand-in gives the context-switch thread its link this way (it starts
      with interrupts disabled), and so does the hand-back to a thread that
      resumes with interrupts disabled. *)
  csl_link_disabled th σ :
    mie_st σ = InterruptDisabled →
    ⊢ @crit_link Σ th (CL th) σ;
  (** With interrupts enabled, the link of a user thread is exactly what
      it hands over and its posture part. The interrupt hand-in takes both
      out of the interrupted thread's link; the hand-back to a thread that
      resumes with interrupts enabled builds its link from them. *)
  csl_link_user_enabled t σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ (UserThread t) (CL (UserThread t)) σ ⊣⊢
    handover_res (ceriseg := ceriseG_of (UserThread t)) ∗
    @posture_part Σ MP (ceriseG_of (UserThread t)) (UserThread t)
      (CL (UserThread t)) (CR (UserThread t));
  (** With interrupts enabled, the link of the context-switch thread holds
      what it hands over. In the resume window, the hand-back to a thread
      that resumes with interrupts enabled takes it from there. *)
  csl_link_ctx_enabled σ :
    mie_st σ = InterruptEnabled →
    @crit_link Σ CtxSwitch (CL CtxSwitch) σ ⊢
    handover_res (ceriseg := ceriseG_of CtxSwitch);
}.
#[export] Hint Mode ContextSwitchLayout + - - + + : typeclass_instances.

(** What a thread hands over is the same at the instance of any thread. *)
Lemma handover_res_thread_indep {Σ} {ceriseb : ceriseBaseG Σ} (th th' : Thread) :
  handover_res (ceriseg := ceriseG_of th) ⊣⊢ handover_res (ceriseg := ceriseG_of th').
Proof.
  rewrite !handover_res_unfold /handover_at /volatile_csr_at /ceriseG_of. reflexivity.
Qed.
