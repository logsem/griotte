(** The hardware language [griotte_hw_lang].

    TRUSTED. This file defines what the adequacy theorem quantifies over:
    the steps that the whole machine may take.

    What it is. A plain Iris [language] (no evaluation contexts) whose
    expressions, values and states are those of [griotte_lang], and whose
    step relation is the step of the whole configuration:
    - [HS_core]: a step of [griotte_lang] under any number of [Seq]
      ([hw_core]; [hw_core_prim_step] and [prim_step_hw_core] show that it
      is exactly [griotte_lang]'s [prim_step], observations and forks
      empty);
    - [HS_async]: at [Exec] (= [Seq (Instr Executable)]) only, an
      interrupt or a tick of [mtime], as the opsem's [async_step] (its
      constructors [step_irq] and [step_tick]). An interrupt needs MIE
      enabled, has either cause of [irq_causes], and enters the handler
      through [enter_irq]; a tick needs nothing. The state after either is
      again at [Exec], so any number of interrupts and ticks may happen
      between two instructions ([hw_ticks]).
    The determinism lemma covers [hw_core] ([hw_core_det]): the machine is
    deterministic except for when interrupts and ticks happen and which
    interrupt cause is taken.

    Sources. cheriot-sail's [handle_trap_extension] (an interrupt saves
    PCC as it is, before the fetch); sail-riscv's [step] (interrupts are
    polled at the start of a step, through [dispatchInterrupt] and
    [handle_interrupt]), [loop] (the clock ticks between steps), [tick_clock]
    (a tick adds one to [mtime]) and [platform_wfi] (a wait for an
    interrupt jumps [mtime] to [mtimecmp], which repeated ticks cover).

    Assumptions. [griotte_hw_lang] is a [Definition], not a canonical
    structure: [griotte_lang] already is the canonical language of
    [expr], and a second canonical structure on the same type would make
    every [WP] on [expr] ambiguous. A WP over the hardware language names
    it explicitly. *)
From stdpp Require Import relations.
From iris.program_logic Require Import language ectx_language ectxi_language.
From griotte Require Import griotte_lang.

Section hw_lang.
  Context `{MachineParameters}.

  (** * The step of [griotte_lang] under evaluation contexts *)

  (** A base step of [griotte_lang] under any number of [Seq]. *)
  Inductive hw_core : expr → ExecConf → expr → ExecConf → Prop :=
  | HC_base e σ e' σ' :
      griotte_lang.prim_step e σ [] e' σ' [] →
      hw_core e σ e' σ'
  | HC_seq e σ e' σ' :
      hw_core e σ e' σ' →
      hw_core (Seq e) σ (Seq e') σ'.

  Lemma hw_core_val e σ e' σ' :
    hw_core e σ e' σ' → griotte_lang.to_val e = None.
  Proof. destruct 1 as [? ? ? ? Hb|]; [by eapply val_stuck|done]. Qed.

  (** [ectx_item] and [fill_item] are [griotte_lang]'s (imported last). *)
  Lemma hw_core_fill (K : list ectx_item) e1 σ e2 σ' :
    hw_core e1 σ e2 σ' →
    hw_core (@ectxi_language.fill cap_ectxi_lang K e1) σ
            (@ectxi_language.fill cap_ectxi_lang K e2) σ'.
  Proof.
    revert e1 e2.
    induction K as [|Ki K IH]; intros e1 e2 Hc; [done|].
    apply (IH (fill_item Ki e1) (fill_item Ki e2)).
    destruct Ki. by apply HC_seq.
  Qed.

  (** [hw_core] is [griotte_lang]'s step, without observations or forks. *)
  Lemma hw_core_prim_step e σ e' σ' :
    hw_core e σ e' σ' →
    @language.prim_step griotte_lang e σ [] e' σ' [].
  Proof.
    induction 1 as [e σ e' σ' Hb|e σ e' σ' _ IH].
    - by apply (base_prim_step (Λ := cap_ectx_lang)).
    - by apply (fill_prim_step (Λ := cap_ectx_lang) [SeqCtx] e σ [] e' σ' []).
  Qed.

  Lemma prim_step_hw_core e σ κ e' σ' efs :
    @language.prim_step griotte_lang e σ κ e' σ' efs →
    κ = [] ∧ efs = [] ∧ hw_core e σ e' σ'.
  Proof.
    intros Hs. destruct Hs as [K e1 e2 -> -> Hb].
    assert (κ = [] ∧ efs = []) as [-> ->] by (inversion Hb; auto).
    split_and!; [done|done|].
    apply hw_core_fill, HC_base, Hb.
  Qed.

  (** Determinism of the hardware language minus interrupts and ticks. *)
  Lemma hw_core_det e σ e1 σ1 e2 σ2 :
    hw_core e σ e1 σ1 → hw_core e σ e2 σ2 → e1 = e2 ∧ σ1 = σ2.
  Proof.
    intros Hcore1. revert e2 σ2.
    induction Hcore1 as [e σ e1 σ1 Hb1|e σ e1 σ1 Hcore1 IH]; intros e2 σ2 Hcore2;
      inversion Hcore2 as [? ? ? ? Hb2|? ? ? ? Hcore2']; subst.
    - by destruct (griotte_lang_determ _ _ _ _ _ _ _ _ _ _ Hb1 Hb2)
        as (_ & -> & -> & _).
    - (* A base step from [Seq e] needs [e] to be a value. *)
      exfalso. apply (base_ctx_step_val SeqCtx) in Hb1.
      apply hw_core_val in Hcore2'. rewrite Hcore2' in Hb1. by destruct Hb1.
    - exfalso. apply (base_ctx_step_val SeqCtx) in Hb2.
      apply hw_core_val in Hcore1. rewrite Hcore1 in Hb2. by destruct Hb2.
    - by destruct (IH _ _ Hcore2') as [-> ->].
  Qed.

  (** * The hardware step *)

  (** The step of the machine: an instruction step, the collapse of a
      [Seq] or a trap entry ([HS_core]), or, between two instructions, an
      interrupt or a tick ([HS_async]). *)
  Inductive hw_step : expr → ExecConf → expr → ExecConf → Prop :=
  | HS_core e σ e' σ' :
      hw_core e σ e' σ' →
      hw_step e σ e' σ'
  | HS_async σ σ' :
      async_step σ σ' →
      hw_step Exec σ Exec σ'.

  Definition hw_prim_step (e : expr) (σ : ExecConf) (κ : list Empty_set)
      (e' : expr) (σ' : ExecConf) (efs : list expr) : Prop :=
    κ = [] ∧ efs = [] ∧ hw_step e σ e' σ'.

  Lemma hw_prim_step_inv e σ κ e' σ' efs :
    hw_prim_step e σ κ e' σ' efs →
    κ = [] ∧ efs = [] ∧
    (hw_core e σ e' σ' ∨ (e = Exec ∧ e' = Exec ∧ async_step σ σ')).
  Proof.
    intros (-> & -> & Hs). split_and!; [done|done|].
    destruct Hs as [? ? ? ? Hc|? ? Ha]; [by left|by right].
  Qed.

  Lemma hw_lang_mixin :
    LanguageMixin griotte_lang.of_val griotte_lang.to_val hw_prim_step.
  Proof.
    split.
    - apply to_of_val.
    - apply of_to_val.
    - intros e σ κ e' σ' efs (_ & _ & Hs).
      destruct Hs as [? ? ? ? Hc|? ? _]; [by eapply hw_core_val|done].
  Qed.

  (** * Interrupts and ticks *)

  Lemma hw_irq_step c σ :
    c ∈ irq_causes → irq_enabled σ →
    hw_prim_step Exec σ [] Exec (enter_irq c σ) [].
  Proof. intros Hc Hen. split_and!; [done|done|]. by apply HS_async, step_irq. Qed.

  Lemma hw_tick_step σ : hw_prim_step Exec σ [] Exec (tick σ) [].
  Proof. split_and!; [done|done|]. apply HS_async, step_tick. Qed.

  (** Ticks may repeat at one instruction boundary. *)
  Lemma hw_ticks n σ :
    nsteps (λ σ1 σ2, hw_prim_step Exec σ1 [] Exec σ2 []) n σ (Nat.iter n tick σ).
  Proof.
    revert σ. induction n as [|n IH]; intros σ; [constructor|].
    rewrite Nat.iter_succ_r. apply nsteps_l with (tick σ); [|apply IH].
    apply hw_tick_step.
  Qed.

  (** Interrupts and ticks happen only at [Exec], and a step that is not
      one of them is a [griotte_lang] step. *)
  Lemma hw_async_only_exec e σ κ e' σ' efs :
    hw_prim_step e σ κ e' σ' efs → ¬ hw_core e σ e' σ' →
    e = Exec ∧ e' = Exec ∧ async_step σ σ'.
  Proof.
    intros Hs Hnc. destruct (hw_prim_step_inv _ _ _ _ _ _ Hs) as (_ & _ & [Hc|Ha]);
      [contradiction|done].
  Qed.

  (** With interrupts disabled, the only step between two instructions
      besides the next instruction is a tick. *)
  Lemma async_step_disabled σ σ' :
    async_step σ σ' → ¬ irq_enabled σ → σ' = tick σ.
  Proof. intros Ha Hd. inversion Ha; subst; [contradiction|done]. Qed.

  (** * Invariants *)

  Lemma hw_core_sys_pc_ok e σ e' σ' :
    hw_core e σ e' σ' → sys_pc_ok σ → sys_pc_ok σ'.
  Proof.
    induction 1 as [? ? ? ? Hb|? ? ? ? _ IH]; intros Hinv;
      [by eapply prim_step_sys_pc_ok|by apply IH].
  Qed.

  Lemma hw_prim_step_sys_pc_ok e σ κ e' σ' efs :
    sys_pc_ok σ → hw_prim_step e σ κ e' σ' efs → sys_pc_ok σ'.
  Proof.
    intros Hinv (_ & _ & Hs). destruct Hs as [? ? ? ? Hc|? ? Ha].
    - by eapply hw_core_sys_pc_ok.
    - by eapply async_step_sys_pc_ok.
  Qed.

End hw_lang.

(** The hardware language. Not canonical: see the header. *)
Definition griotte_hw_lang `{MachineParameters} : language := Language hw_lang_mixin.

Section hw_lang_props.
  Context `{MachineParameters}.

  (** The machine can always take a step from [Exec]. *)
  Lemma hw_exec_reducible σ : @reducible griotte_hw_lang Exec σ.
  Proof.
    destruct (normal_always_step σ) as (c & σ' & Hs).
    exists [], (Seq (Instr c)), σ', []. split_and!; [done|done|].
    apply HS_core, HC_seq, HC_base. by constructor.
  Qed.

  (** Every whole-program shape [Seq (Instr c)] can step. *)
  Lemma hw_seq_reducible σ c : @reducible griotte_hw_lang (Seq (Instr c)) σ.
  Proof.
    destruct c.
    - apply hw_exec_reducible.
    - exists [], (Instr Halted), σ, []. split_and!; [done|done|].
      apply HS_core, HC_base. constructor.
    - destruct (trap_halts σ) eqn:Hth.
      + exists [], (Instr Faulted), σ, []. split_and!; [done|done|].
        apply HS_core, HC_base. by constructor.
      + exists [], Exec, (enter_exc (trap_cause σ, trap_tval σ) σ), [].
        split_and!; [done|done|]. apply HS_core, HC_base. by constructor.
    - exists [], Exec, σ, []. split_and!; [done|done|].
      apply HS_core, HC_base. constructor.
  Qed.

End hw_lang_props.
