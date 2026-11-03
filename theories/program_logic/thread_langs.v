(** The thread languages: one language per kind of thread, and their
    simulation by the hardware language [griotte_hw_lang].

    Not trusted, but it fixes what the simulation connects: read it with
    [hw_lang.v].

    - [kind]: [UserK] for a user thread, [CtxK] for the context-switch
      thread; [kind_of] on [Thread].
    - [texpr k], [tval k]: [griotte_lang]'s expressions and values, plus
      the switch values [TSwV s] ([YieldV], [ExitV], [ResumedV]). The kind
      is a phantom index: it makes [tlang k] a distinct canonical language
      per kind.
    - The switch instructions ([sw_of], [is_switch_instr], decidable): for
      a user thread, the exit marker
      [SpecialRW cnull mcause (inl MCAUSE_THREAD_EXIT)] (exit) and [Ecall]
      (yield); for the context-switch thread, [Mret] (resume). An
      instruction step produces the switch value only when the decoded
      instruction is a switch instruction of the kind and [step] returns
      [NextI] ([tres]); the state is the real post-state.
    - The context-switch device ([blocked]): the context-switch thread has
      no instruction step that is not a decoded [Mret] and ends with
      interrupts enabled.
    - [tlang k]: an ectxi language over [step], with the [Seq] context of
      [griotte_lang] and one more base step, the collapse
      [TSeq (TInstr (TSw s))] to [TInstr (TSw s)].
    - [hw_of], [wellshaped]; simulation (a) ([sim_a]), (b) ([sim_b],
      [sim_b_hw]); [wellshaped_step]; thread determinism
      ([tlang_base_determ]); a user thread never gets stuck
      ([user_reducible]); the context-switch thread is stuck exactly at the
      device ([ctx_reducible_iff]); interrupts and ticks find a thread at
      [TExec] or a switch value ([async_at_thread]).

    Sources. The switch instructions follow CHERIoT's switcher ([entry.S]):
    the exit marker is its [csrw mcause, MCAUSE_THREAD_EXIT], an immediate
    write; [mret] ends the resume path. *)
From griotte Require Import resources.
From iris.program_logic Require Import language ectx_language ectxi_language.
From griotte Require Import griotte_lang hw_lang.
Set Warnings "-redundant-canonical-projection".

(** * Kinds of threads *)

Inductive kind := UserK | CtxK.

#[global] Instance kind_eq_dec : EqDecision kind.
Proof. solve_decision. Defined.

Definition kind_of (th : Thread) : kind :=
  match th with
  | UserThread _ => UserK
  | CtxSwitch => CtxK
  end.

(** * Switch values *)

(** The ways a thread's turn ends: a yield ([ecall] by a user thread), a
    thread exit (the exit marker), a resume of a user thread ([mret] by
    the context-switch thread). *)
Inductive sw := YieldS | ExitS | ResumedS.

#[global] Instance sw_eq_dec : EqDecision sw.
Proof. solve_decision. Defined.

(** The flag of a thread expression: a configuration flag, or a switch. *)
Inductive tflag := TF (c : ConfFlag) | TSw (s : sw).

#[global] Instance ConfFlag_eq_dec : EqDecision ConfFlag.
Proof. solve_decision. Defined.
#[global] Instance tflag_eq_dec : EqDecision tflag.
Proof. solve_decision. Defined.

Inductive texpr (k : kind) :=
| TInstr (f : tflag)
| TSeq (e : texpr k).
Arguments TInstr {k} f.
Arguments TSeq {k} e.

Inductive tval (k : kind) :=
| THaltedV
| TFaultedV
| TNextIV
| TSwV (s : sw).
Arguments THaltedV {k}.
Arguments TFaultedV {k}.
Arguments TNextIV {k}.
Arguments TSwV {k} s.

Notation YieldV := (TSwV YieldS).
Notation ExitV := (TSwV ExitS).
Notation ResumedV := (TSwV ResumedS).

(** The program of a thread, as [Exec] for [griotte_lang]. *)
Notation TExec := (TSeq (TInstr (TF Executable))).

Definition tof_val {k} (v : tval k) : texpr k :=
  match v with
  | THaltedV => TInstr (TF Halted)
  | TFaultedV => TInstr (TF Faulted)
  | TNextIV => TInstr (TF NextI)
  | TSwV s => TInstr (TSw s)
  end.

Definition tto_val {k} (e : texpr k) : option (tval k) :=
  match e with
  | TInstr (TF Halted) => Some THaltedV
  | TInstr (TF Faulted) => Some TFaultedV
  | TInstr (TF NextI) => Some TNextIV
  | TInstr (TSw s) => Some (TSwV s)
  | _ => None
  end.

Lemma tto_of_val {k} (v : tval k) : tto_val (tof_val v) = Some v.
Proof. by destruct v. Qed.

Lemma tof_to_val {k} (e : texpr k) v : tto_val e = Some v → tof_val v = e.
Proof. destruct e as [ [ []|s]|e]; intros Hv; simplify_eq/=; done. Qed.

(** * Switch instructions *)

(** The exit marker, [csrw mcause, MCAUSE_THREAD_EXIT], as the opsem
    decodes it. Another destination or a register source is an ordinary
    instruction. *)
Definition exit_marker : instr := SpecialRW cnull mcause (inl MCAUSE_THREAD_EXIT).

(** The switch instructions of each kind, with the switch they make. *)
Definition sw_of (k : kind) (i : instr) : option sw :=
  match k with
  | UserK =>
      if decide (i = exit_marker) then Some ExitS
      else if decide (i = Ecall) then Some YieldS
      else None
  | CtxK => if decide (i = Mret) then Some ResumedS else None
  end.

Definition is_switch_instr (k : kind) (i : instr) : Prop := is_Some (sw_of k i).

#[global] Instance is_switch_instr_dec k i : Decision (is_switch_instr k i).
Proof. rewrite /is_switch_instr. apply _. Defined.

(** The evaluation context of a thread: the [Seq] of the program. *)
Inductive tectx_item (k : kind) := TSeqCtx.
Arguments TSeqCtx {k}.

Definition tfill_item {k} (Ki : tectx_item k) (e : texpr k) : texpr k :=
  match Ki with TSeqCtx => TSeq e end.

Section thread_langs.
  Context `{MachineParameters}.

  (** The instruction that the PC points to, decoded. [step] executes it
      when the PC is a correct PC. *)
  Definition decoded_instr (σ : ExecConf) : option instr :=
    match pcc σ with
    | WCap _ _ _ _ _ a => decodeInstrW <$> mem σ !! a
    | _ => None
    end.

  (** The result of an instruction step with outcome [c] from [σ], in a
      thread of kind [k]: the switch value when the decoded instruction
      is a switch instruction of the kind and the step succeeded. *)
  Definition tres (k : kind) (σ : ExecConf) (c : ConfFlag) : tflag :=
    match c, decoded_instr σ ≫= sw_of k with
    | NextI, Some s => TSw s
    | _, _ => TF c
    end.
  #[local] Arguments tres : simpl never.

  (** The context-switch device: an instruction step of the context-switch
      thread from [σ] to [σ'] that is not a decoded [Mret] and ends with
      interrupts enabled. The thread language has no such step. *)
  Definition ctx_blocked (σ σ' : ExecConf) : Prop :=
    decoded_instr σ ≠ Some Mret ∧ irq_enabled σ'.

  Definition blocked (k : kind) (σ σ' : ExecConf) : Prop :=
    match k with
    | UserK => False
    | CtxK => ctx_blocked σ σ'
    end.

  #[global] Instance blocked_dec k σ σ' : Decision (blocked k σ σ').
  Proof. destruct k; cbn; apply _. Defined.

  (** * The thread languages *)

  Inductive tbase (k : kind) :
      texpr k → ExecConf → list Empty_set → texpr k → ExecConf → list (texpr k) → Prop :=
  | TS_instr σ c σ' :
      step (Executable, σ) (c, σ') →
      ¬ blocked k σ σ' →
      tbase k (TInstr (TF Executable)) σ [] (TInstr (tres k σ c)) σ' []
  | TS_seq σ :
      tbase k (TSeq (TInstr (TF NextI))) σ [] (TSeq (TInstr (TF Executable))) σ []
  | TS_halt σ :
      tbase k (TSeq (TInstr (TF Halted))) σ [] (TInstr (TF Halted)) σ []
  | TS_trap σ :
      trap_halts σ = false →
      tbase k (TSeq (TInstr (TF Faulted))) σ []
        (TSeq (TInstr (TF Executable))) (enter_exc (trap_cause σ, trap_tval σ) σ) []
  | TS_trap_halt σ :
      trap_halts σ = true →
      tbase k (TSeq (TInstr (TF Faulted))) σ [] (TInstr (TF Faulted)) σ []
  (* The collapse of a switch: the switch value reaches the top level. *)
  | TS_switch σ s :
      tbase k (TSeq (TInstr (TSw s))) σ [] (TInstr (TSw s)) σ [].

  Lemma tval_stuck k e σ κ e' σ' efs :
    tbase k e σ κ e' σ' efs → tto_val e = None.
  Proof. intros Hb. by inversion Hb. Qed.

  Lemma tfill_item_val k (Ki : tectx_item k) e :
    is_Some (tto_val (tfill_item Ki e)) → is_Some (tto_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

  #[local] Instance tfill_item_inj k (Ki : tectx_item k) : Inj (=) (=) (tfill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.

  Lemma tbase_ctx_step_val k (Ki : tectx_item k) e σ1 κ e2 σ2 efs :
    tbase k (tfill_item Ki e) σ1 κ e2 σ2 efs → is_Some (tto_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

  Lemma tfill_item_no_val_inj k (Ki1 Ki2 : tectx_item k) e1 e2 :
    tto_val e1 = None → tto_val e2 = None →
    tfill_item Ki1 e1 = tfill_item Ki2 e2 → Ki1 = Ki2.
  Proof. intros. by destruct Ki1, Ki2. Qed.

  Lemma tlang_mixin k :
    EctxiLanguageMixin (@tof_val k) (@tto_val k) (@tfill_item k) (tbase k).
  Proof.
    constructor;
      apply _ || eauto using tto_of_val, tof_to_val, tval_stuck,
        tfill_item_val, tfill_item_no_val_inj, tbase_ctx_step_val.
  Qed.

End thread_langs.

Canonical Structure tlang_ectxi `{MachineParameters} (k : kind) :=
  EctxiLanguage (tlang_mixin k).
Canonical Structure tlang_ectx `{MachineParameters} (k : kind) :=
  EctxLanguageOfEctxi (tlang_ectxi k).
Canonical Structure tlang `{MachineParameters} (k : kind) :=
  LanguageOfEctx (tlang_ectx k).

Section thread_lang_pure.
  Context `{MachineParameters}.

  (** [pure_base_step_pure_step] is given the language: canonical
      resolution would pick [griotte_lang]'s. *)
  #[local] Ltac solve_exec_pure k :=
    intros ?; apply nsteps_once, (pure_base_step_pure_step (Λ := tlang_ectx k));
    constructor;
      [intros; subst; do 3 eexists; econstructor; eauto
      |intros ????? Hbase; inversion Hbase; done].

  #[global] Instance tpure_seq_done k :
    PureExec True 1 (TSeq (TInstr (TF NextI)) : texpr k) TExec.
  Proof. solve_exec_pure k. Qed.
  #[global] Instance tpure_seq_halted k :
    PureExec True 1 (TSeq (TInstr (TF Halted)) : texpr k) (TInstr (TF Halted)).
  Proof. solve_exec_pure k. Qed.
  (** The collapse of a switch. *)
  #[global] Instance tpure_seq_switch k s :
    PureExec True 1 (TSeq (TInstr (TSw s)) : texpr k) (TInstr (TSw s)).
  Proof. solve_exec_pure k. Qed.
End thread_lang_pure.

Section thread_lang_props.
  Context `{MachineParameters}.
  #[local] Arguments tres : simpl never.

  (** * Switch values and instruction results *)

  Lemma tres_switch k σ c s :
    tres k σ c = TSw s →
    c = NextI ∧ ∃ i, decoded_instr σ = Some i ∧ sw_of k i = Some s.
  Proof.
    rewrite /tres. destruct (decoded_instr σ ≫= sw_of k) as [s'|] eqn:Hb;
      destruct c; intros Heq; simplify_eq.
    split; [done|]. by apply bind_Some.
  Qed.

  (** An instruction that is not a switch instruction of the kind gives
      the outcome of [step]: the generic instruction rules need this as a
      decode side condition. *)
  Lemma tres_no_switch k σ c :
    (∀ i, decoded_instr σ = Some i → ¬ is_switch_instr k i) →
    tres k σ c = TF c.
  Proof.
    rewrite /tres /is_switch_instr. intros Hns.
    destruct (decoded_instr σ) as [i|] eqn:Hi; simpl; last by destruct c.
    destruct (sw_of k i) as [s|] eqn:Hs; last by destruct c.
    exfalso. apply (Hns i); [done|]. rewrite Hs. by eexists.
  Qed.

  (** A failed step is never a switch. *)
  Lemma tres_not_next k σ c : c ≠ NextI → tres k σ c = TF c.
  Proof. rewrite /tres. by destruct c. Qed.

  (** The context-switch thread enables interrupts only by [Mret]. *)
  Lemma ctx_instr_irq_enabled σ κ e' σ' efs :
    tbase CtxK (TInstr (TF Executable)) σ κ e' σ' efs →
    irq_enabled σ' → decoded_instr σ = Some Mret.
  Proof.
    intros Hb Hen. inversion Hb; subst.
    destruct (decide (decoded_instr σ = Some Mret)) as [|Hne]; [done|].
    exfalso.
    match goal with Hnb : ¬ blocked _ _ _ |- _ => apply Hnb end.
    by split.
  Qed.

  (** A user thread has no device. *)
  Lemma user_not_blocked σ σ' : ¬ blocked UserK σ σ'.
  Proof. by intros []. Qed.

  (** * Determinism *)

  Lemma tlang_base_determ k e σ κ κ' e1 e2 σ1 σ2 efs efs' :
    tbase k e σ κ e1 σ1 efs → tbase k e σ κ' e2 σ2 efs' →
    κ = κ' ∧ e1 = e2 ∧ σ1 = σ2 ∧ efs = efs'.
  Proof.
    intros Hb1 Hb2.
    destruct Hb1 as [σx c1 σ1' Hs1 _|σx|σx|σx Hth1|σx Hth1|σx s1];
      inversion Hb2 as [σy c2 σ2' Hs2 _|σy|σy|σy Hth2|σy Hth2|σy s2]; simplify_eq; try done.
    - destruct (step_deterministic _ _ _ _ _ _ Hs1 Hs2) as [-> ->]. done.
    - congruence.
    - congruence.
  Qed.

  Lemma tprim_step_nil k (e : texpr k) σ κ e' σ' efs :
    @language.prim_step (tlang k) e σ κ e' σ' efs → κ = [] ∧ efs = [].
  Proof. intros Hs. destruct Hs as [K e1 e2 _ _ Hb]. by inversion Hb. Qed.

  Lemma tprim_val_stuck k (e : texpr k) σ κ e' σ' efs :
    @language.prim_step (tlang k) e σ κ e' σ' efs → tto_val e = None.
  Proof.
    intros Hs. change (@language.to_val (tlang k) e = None).
    by eapply language.val_stuck.
  Qed.

  (** * The hardware image of a thread expression *)

  (** Inside the program, a switch expression is the hardware's
      [Instr NextI]. *)
  Fixpoint hw_in {k} (e : texpr k) : expr :=
    match e with
    | TInstr (TF c) => Instr c
    | TInstr (TSw _) => Instr NextI
    | TSeq e => Seq (hw_in e)
    end.

  (** On whole programs: a switch value at the top level is the hardware's
      [Exec], the state where the next instruction (or an interrupt)
      happens. *)
  Definition hw_of {k} (e : texpr k) : expr :=
    match e with
    | TInstr (TSw _) => Exec
    | _ => hw_in e
    end.

  (** Well-shaped: a whole program [TSeq (TInstr f)], or a value. *)
  Definition wellshaped {k} (e : texpr k) : Prop :=
    (∃ f, e = TSeq (TInstr f)) ∨ is_Some (tto_val e).

  Lemma hw_of_switch {k} s : hw_of (TInstr (TSw s) : texpr k) = Exec.
  Proof. done. Qed.

  Lemma hw_in_tres k σ c : hw_in (TInstr (tres k σ c) : texpr k) = Instr c.
  Proof. rewrite /tres. by destruct c, (decoded_instr σ ≫= sw_of k). Qed.

  Lemma tfill_seq_instr {k} (K : list (tectx_item k)) (e : texpr k) f :
    @ectxi_language.fill (tlang_ectxi k) K e = TSeq (TInstr f) →
    K = [] ∨ (K = [TSeqCtx] ∧ e = TInstr f).
  Proof.
    induction K as [|Ki K _] using rev_ind; [by left|].
    rewrite fill_app /=. destruct Ki. intros [= He]. right.
    destruct K as [|Ki' K _] using rev_ind; [by subst|].
    rewrite fill_app /= in He. destruct Ki'. done.
  Qed.

  (** The instruction step under the program's [Seq]. *)
  Lemma sim_instr k σ c σ' :
    step (Executable, σ) (c, σ') →
    hw_core (hw_of (TSeq (TInstr (TF Executable)) : texpr k)) σ
            (hw_of (TSeq (TInstr (tres k σ c)) : texpr k)) σ'.
  Proof.
    intros Hs. rewrite /tres.
    destruct c, (decoded_instr σ ≫= sw_of k); apply HC_seq, HC_base; by constructor.
  Qed.

  (** Well-shapedness is preserved. *)
  Lemma wellshaped_step k (e : texpr k) σ κ e' σ' efs :
    wellshaped e → @language.prim_step (tlang k) e σ κ e' σ' efs → wellshaped e'.
  Proof.
    rewrite /wellshaped. intros [ [f ->]|[v Hv] ] Hs; last first.
    { apply tprim_val_stuck in Hs. congruence. }
    destruct Hs as [K e1 e2 He1 -> Hb].
    destruct (tfill_seq_instr K e1 f (eq_sym He1)) as [->|[-> ->] ].
    - simpl in He1. subst e1. inversion Hb; subst;
        [left; by eexists|right; by eexists|left; by eexists|right; by eexists
        |right; by eexists].
    - inversion Hb; subst. left; by eexists.
  Qed.

  (** Simulation (a): every step of a well-shaped thread expression is a
      hardware step, up to [hw_of]. *)
  Lemma sim_a k (e : texpr k) σ κ e' σ' efs :
    wellshaped e →
    @language.prim_step (tlang k) e σ κ e' σ' efs →
    hw_core (hw_of e) σ (hw_of e') σ'.
  Proof.
    intros [ [f ->]|[v Hv] ] Hs; last first.
    { apply tprim_val_stuck in Hs. congruence. }
    destruct Hs as [K e1 e2 He1 -> Hb].
    destruct (tfill_seq_instr K e1 f (eq_sym He1)) as [->|[-> ->] ].
    - simpl in He1. subst e1. inversion Hb; subst; apply HC_base; by constructor.
    - inversion Hb; subst.
      match goal with H : step _ _ |- _ => by apply sim_instr end.
  Qed.

  Lemma sim_a_hw k (e : texpr k) σ κ e' σ' efs :
    wellshaped e →
    @language.prim_step (tlang k) e σ κ e' σ' efs →
    hw_prim_step (hw_of e) σ [] (hw_of e') σ' [].
  Proof. intros Hw Hs. split_and!; [done|done|]. by eapply HS_core, sim_a. Qed.

  (** Simulation (b): a hardware step from [hw_of e] that is neither an
      interrupt nor a tick is matched by a step of the thread, when the
      thread can step. *)
  Lemma sim_b k (e : texpr k) σ h' σ' :
    wellshaped e →
    @reducible (tlang k) e σ →
    hw_core (hw_of e) σ h' σ' →
    ∃ e'', @language.prim_step (tlang k) e σ [] e'' σ' [] ∧ hw_of e'' = h'.
  Proof.
    intros Hw (κ & e1 & σ1 & efs & Hs) Hh.
    destruct (tprim_step_nil _ _ _ _ _ _ _ Hs) as [-> ->].
    destruct (hw_core_det _ _ _ _ _ _ (sim_a _ _ _ _ _ _ _ Hw Hs) Hh) as [<- <-].
    by exists e1.
  Qed.

  Lemma sim_b_hw k (e : texpr k) σ κ h' σ' efs :
    wellshaped e →
    @reducible (tlang k) e σ →
    hw_prim_step (hw_of e) σ κ h' σ' efs →
    ¬ (hw_of e = Exec ∧ h' = Exec ∧ async_step σ σ') →
    ∃ e'', @language.prim_step (tlang k) e σ [] e'' σ' [] ∧ hw_of e'' = h'.
  Proof.
    intros Hw Hr Hh Hna.
    destruct (hw_prim_step_inv _ _ _ _ _ _ Hh) as (_ & _ & [Hc|(He & -> & Ha)]).
    - by eapply sim_b.
    - exfalso. by apply Hna.
  Qed.


  (** A user thread steps from every well-shaped non-value: it has no
      device. *)
  Lemma user_reducible σ (e : texpr UserK) :
    wellshaped e → tto_val e = None → @reducible (tlang UserK) e σ.
  Proof.
    intros [ [f ->]|[v Hv] ] Hnv; [|congruence].
    destruct f as [ [] | s].
    - destruct (normal_always_step σ) as (c & σ' & Hs).
      exists [], (TSeq (TInstr (tres UserK σ c))), σ', [].
      apply (fill_prim_step (Λ := tlang_ectx UserK) [TSeqCtx] (TInstr (TF Executable))).
      apply (base_prim_step (Λ := tlang_ectx UserK)).
      apply TS_instr; [done|apply user_not_blocked].
    - exists [], (TInstr (TF Halted)), σ, [].
      apply (base_prim_step (Λ := tlang_ectx UserK)). constructor.
    - destruct (trap_halts σ) eqn:Hth.
      + exists [], (TInstr (TF Faulted)), σ, [].
        apply (base_prim_step (Λ := tlang_ectx UserK)). by constructor.
      + exists [], TExec, (enter_exc (trap_cause σ, trap_tval σ) σ), [].
        apply (base_prim_step (Λ := tlang_ectx UserK)). by constructor.
    - exists [], TExec, σ, [].
      apply (base_prim_step (Λ := tlang_ectx UserK)). constructor.
    - exists [], (TInstr (TSw s)), σ, [].
      apply (base_prim_step (Λ := tlang_ectx UserK)). constructor.
  Qed.

  (** The context-switch thread is stuck exactly at the device. *)
  Lemma ctx_reducible_iff σ :
    @reducible (tlang CtxK) TExec σ ↔
    ∀ c σ', step (Executable, σ) (c, σ') → ¬ ctx_blocked σ σ'.
  Proof.
    split.
    - intros (κ & e' & σ1 & efs & Hs) c σ' Hstep Hb.
      destruct Hs as [K e1 e2 He1 -> Hbase].
      destruct (tfill_seq_instr K e1 (TF Executable) (eq_sym He1)) as [->|[-> ->] ].
      + simpl in He1. subst e1. inversion Hbase.
      + inversion Hbase as [σx c' σ'' Hstep' Hnb| | | | |]; subst.
        destruct (step_deterministic _ _ _ _ _ _ Hstep Hstep') as [-> ->].
        by apply Hnb.
    - intros Hnb. destruct (normal_always_step σ) as (c & σ' & Hs).
      exists [], (TSeq (TInstr (tres CtxK σ c))), σ', [].
      apply (fill_prim_step (Λ := tlang_ectx CtxK) [TSeqCtx] (TInstr (TF Executable))).
      apply (base_prim_step (Λ := tlang_ectx CtxK)).
      apply TS_instr; [done|]. exact (Hnb c σ' Hs).
  Qed.

  (** Interrupts and ticks happen at [Exec] ([hw_async_only_exec]): for a
      thread, at [TExec] or at a switch value. *)
  Lemma async_at_thread {k} (e : texpr k) :
    wellshaped e → hw_of e = Exec → e = TExec ∨ ∃ s, e = TInstr (TSw s).
  Proof.
    intros [ [f ->]|[v Hv] ] Hh.
    - destruct f as [ [] | s]; simplify_eq/=. by left.
    - destruct e as [ [ [] | s] | e']; simplify_eq/=; eauto.
  Qed.

End thread_lang_props.
