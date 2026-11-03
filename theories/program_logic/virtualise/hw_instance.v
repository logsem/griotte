From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Import named_props_extra.
From griotte Require Import hw_lang.
From griotte Require Export handoff.

(** * The Iris instance of the hardware

    The hardware language [griotte_hw_lang] runs one thread at a time. Its
    state interpretation is the running thread's, with the context-switch
    thread's resources while a user thread runs; each hardware step gives
    two later credits. *)

(** The switch window of the context-switch thread: its resuming [mret]
    has run, the next step returns [ResumedV]. *)
Definition window {k} (e : thread_langs.expr k) : Prop :=
  e = Seq (Instr (TSw ResumedS)) ∨ e = Instr (TSw ResumedS).

Section hw_state_interp.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t}.

  (** The running thread, and whether the context-switch thread is in its
      switch window: an authority and a fragment, halves of a ghost
      variable. *)
  Definition running_auth (th : Thread) : iProp Σ := ghost_var γ_running (1/2) th.
  Definition running_frag (th : Thread) : iProp Σ := ghost_var γ_running (1/2) th.
  Definition resume_window_auth (w : bool) : iProp Σ := ghost_var γ_resume_window (1/2) w.
  Definition resume_window_frag (w : bool) : iProp Σ := ghost_var γ_resume_window (1/2) w.

  (** Outside its switch window, the context-switch thread runs with
      interrupts disabled. *)
  Definition resume_window_si (th : Thread) (σ : ExecConf) : iProp Σ :=
    ∃ w,
      resume_window_auth w ∗
      ⌜th = CtxSwitch → w = false → mie_st σ = InterruptDisabled⌝.

  (** The state interpretation of thread [th]'s instance. *)
  Definition thread_si (th : Thread) (σ : ExecConf) : iProp Σ :=
    state_interp (irisGS_gen := memG_irisG (th := th) (ceriseg := ceriseG_of th) (CL := CL th))
      σ 0 [] 0.

  (** The hardware's state interpretation: the running thread's, and the
      context-switch thread's resources while another thread runs. *)
  Definition SI_hw (σ : ExecConf) : iProp Σ :=
    ∃ th,
      "Hrun" ∷ running_auth th ∗
      "Hwin" ∷ resume_window_si th σ ∗
      "Hsi" ∷ thread_si th σ ∗
      "Hidle" ∷ (if th is CtxSwitch then True else idle_CtxSwitch).

  (** Two later credits per hardware step. *)
  Definition hw_irisGS : irisGS_gen HasLc griotte_hw_lang Σ := {|
    iris_invGS := cb_invG;
    state_interp (σ : state griotte_hw_lang) _ _ _ := SI_hw σ;
    fork_post _ := True%I;
    num_laters_per_step _ := 1;
    state_interp_mono _ _ _ _ := fupd_intro _ _;
  |}.

  (** What [virtualise] holds besides the WP of the running thread: the
      fragments of the running thread and of the switch window; a user
      thread is the running one in [cur], and the context-switch thread in
      its switch window is at the end of its resuming [mret]. *)
  Definition thread_res (th : Thread) (e : thread_langs.expr (kind_of th)) : iProp Σ :=
    running_frag th ∗
    ∃ w,
      resume_window_frag w ∗
      match th with
      | UserThread t => cur_frag (Some (UserThread t, Running))
      | CtxSwitch => ⌜w = true → window e⌝
      end.

  (** The state interpretation of a thread's instance ignores its step
      counters. *)
  Lemma thread_si_any th σ ns κs nt :
    state_interp (irisGS_gen := memG_irisG (th := th) (ceriseg := ceriseG_of th) (CL := CL th))
      σ ns κs nt ⊣⊢
    thread_si th σ.
  Proof. done. Qed.

  Lemma running_agree th th' : running_auth th -∗ running_frag th' -∗ ⌜th = th'⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %?. Qed.

  Lemma running_update th'' th th' :
    running_auth th -∗
    running_frag th'
    ==∗
    running_auth th'' ∗
    running_frag th''.
  Proof. iIntros "Ha Hf". iApply (ghost_var_update_halves with "Ha Hf"). Qed.

  Lemma resume_window_agree w w' :
    resume_window_auth w -∗ resume_window_frag w' -∗ ⌜w = w'⌝.
  Proof. iIntros "Ha Hf". by iDestruct (ghost_var_agree with "Ha Hf") as %?. Qed.

  Lemma resume_window_update w'' w w' :
    resume_window_auth w -∗
    resume_window_frag w'
    ==∗
    resume_window_auth w'' ∗
    resume_window_frag w''.
  Proof. iIntros "Ha Hf". iApply (ghost_var_update_halves with "Ha Hf"). Qed.
End hw_state_interp.

(** The WP of the hardware. *)
Notation "'WP_hw' e @ E {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ hw_irisGS) NotStuck E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[hv' 'WP_hw'  e  '/' @  E  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP_hw' e {{ Φ } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ hw_irisGS) NotStuck ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'[hv' 'WP_hw'  e  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP_hw' e @ E {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ hw_irisGS) NotStuck E e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP_hw'  e  '/' @  E  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'WP_hw' e {{ v , Q } }" :=
  (@wp _ _ _ _ (@wp' _ _ _ hw_irisGS) NotStuck ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200, v at level 200 as pattern,
   format "'[hv' 'WP_hw'  e  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(** A fancy update stated with only a base in scope is at the base's
    [cb_invG]; typeclass search does not unify it with [hw_irisGS]'s
    [iris_invGS], a [Definition]: this instance eliminates such an update
    under [WP_hw], as [elim_modal_base_fupd_wp] under a thread's WP. *)
#[export] Instance elim_modal_base_fupd_wp_hw `{MP : MachineParameters} {Σ}
    {ceriseb : ceriseBaseG Σ} {CL : ∀ t, CritLink Σ t} p E e (P : iProp Σ) Φ :
  ElimModal True p false
    (@fupd _ (@bi_fupd_fupd _ (@uPred_bi_fupd HasLc Σ (@cb_invG Σ ceriseb))) E E P) P
    (WP_hw e @ E {{ Φ }}) (WP_hw e @ E {{ Φ }}).
Proof. exact (elim_modal_fupd_wp (irisGS_gen0 := hw_irisGS) p NotStuck E e P Φ). Qed.

Section hw_lifting.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} `{MP : MachineParameters}
    {CL : ∀ t, CritLink Σ t}.

  (** One hardware step at a non-value: two credits, two laters. *)
  Lemma hw_goal_wp (e : griotte_lang.expr) :
    language.to_val (l := griotte_hw_lang) e = None →
    (∀ σ, SI_hw σ ={⊤,∅}=∗
       ⌜reducible (Λ := griotte_hw_lang) e σ⌝ ∗
       ∀ e2 σ2,
         ⌜prim_step (l := griotte_hw_lang) e σ [] e2 σ2 []⌝ -∗
         £ 2 -∗
         |={∅}▷=>^2 |={∅,⊤}=> SI_hw σ2 ∗ WP_hw e2 {{ _, True }}) ⊢
    WP_hw e {{ _, True }}.
  Proof.
    iIntros (Hv) "H". iApply wp_lift_step_fupdN; first done.
    iIntros (σ ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "[$ H]". iModIntro.
    iIntros (e2 σ2 efs Hst) "Hc".
    destruct (hw_prim_step_inv _ _ _ _ _ _ Hst) as (-> & -> & _).
    iSpecialize ("H" with "[%] Hc"); first done.
    iApply (step_fupdN_wand with "H"). iIntros "H". iMod "H" as "[$ $]". by iModIntro.
  Qed.
End hw_lifting.
