From iris.program_logic Require Import language.
From griotte Require Import machine_parameters machine_base griotte_opsem griotte_lang
  machine_run hw_lang.

(** * Runs of the interpreter as runs of the hardware language

    [machine_run] computes runs of [griotte_lang]. Every step of
    [griotte_lang] is a step of [griotte_hw_lang] ([HS_core]), so these runs
    are runs of the hardware. [machine_run_irq] adds one interrupt, taken
    where [machine_run_until] stops. *)

Section hw_machine_run.
  Context `{MP : MachineParameters}.

  (** A step of [griotte_lang] is a step of the hardware language. *)
  Lemma erased_step_hw (ρ ρ' : cfg griotte_lang) :
    erased_step ρ ρ' → @erased_step griotte_hw_lang ρ ρ'.
  Proof.
    intros [κ Hs].
    destruct Hs as [e1 σ1 e2 σ2 efs t1 t2 -> -> Hprim].
    apply prim_step_hw_core in Hprim as (-> & -> & Hc).
    exists []. econstructor; [done|done|].
    split_and!; [done|done|]. by apply HS_core.
  Qed.

  Lemma rtc_erased_step_hw (ρ ρ' : cfg griotte_lang) :
    rtc erased_step ρ ρ' → rtc (@erased_step griotte_hw_lang) ρ ρ'.
  Proof.
    induction 1 as [|ρ1 ρ2 ρ3 Hs _ IH]; [done|].
    eapply rtc_l; [by apply erased_step_hw|done].
  Qed.

  (** A run that [machine_run] computes, without interrupts. *)
  Lemma machine_run_hw_correct fuel (σ : ExecConf) cf' :
    machine_run fuel (Executable, σ) = Some cf' →
    ∃ σ', rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) ([Instr cf'], σ').
  Proof.
    intros Hrun.
    destruct (machine_run_correct _ _ _ _ Hrun) as [σ' Hsteps].
    exists σ'. by apply rtc_erased_step_hw.
  Qed.

  (** The interpreter, stopped at the first state, before an instruction,
      that [stop] accepts; [None] if the machine halts, stops after a fault
      or runs out of fuel first. *)
  Fixpoint machine_run_until (stop : ExecConf → bool) (fuel : nat) (c : Conf) :
      option ExecConf :=
    match fuel with
    | 0 => None
    | S fuel =>
      match c with
      | (Faulted, φ) =>
          if trap_halts φ then None
          else machine_run_until stop fuel (Executable, enter_exc (trap_cause φ, trap_tval φ) φ)
      | (Halted, _) => None
      | (NextI, φ) => machine_run_until stop fuel (Executable, φ)
      | (Executable, φ) =>
          if stop φ then Some φ else
          match φ with
          | MkExecConf pc r sr m st td =>
              if isCorrectPCb pc
              then (
                  let a := match pc with
                           | WCap _ _ _ _ _ a => a
                           | _ => addresses.top (* dummy *)
                           end
                  in
                  let p := match pc with
                           | WCap _ p _ _ _ _ => p
                           | _ => RWX (* dummy *)
                           end
                  in
                  match m !! a with
                  | None => machine_run_until stop fuel (Faulted, φ)
                  | Some wa =>
                      let c' := exec (decodeInstrW wa) p φ in
                      machine_run_until stop fuel (c'.1, c'.2)
                  end
                ) else machine_run_until stop fuel (Faulted, φ)
          end
      end
    end.

  Lemma machine_run_until_correct stop fuel cf (φ φ' : ExecConf) :
    machine_run_until stop fuel (cf, φ) = Some φ' →
    rtc erased_step ([Seq (Instr cf)], φ) ([griotte_lang.Exec], φ').
  Proof.
    revert cf φ. induction fuel as [|fuel IHfuel]; first (cbn; done).
    cbn. intros cf φ Hc.
    destruct cf; simplify_eq.
    - (* Executable: the stop, or the fetch and the instruction. A halted
         machine gives [None], closed by [simplify_eq]. *)
      destruct (stop φ) eqn:Hstop; [by simplify_eq|].
      destruct φ as [wpc r sr m st td].
      destruct (isCorrectPCb wpc) eqn:HPC.
      + apply isCorrectPCb_isCorrectPC in HPC.
        inversion HPC as [p g b e a Hbounds Hx Hwpc]; subst wpc.
        destruct (m !! a) as [wa | ] eqn:HeMem.
        * eapply rtc_l; last eapply IHfuel, Hc.
          apply erased_step_seq_instr. constructor. eapply step_exec_instr; eauto.
        * eapply rtc_l; last eapply IHfuel, Hc.
          apply erased_step_seq_instr. constructor. eapply step_exec_memfail; eauto.
      + apply isCorrectPCb_nisCorrectPC in HPC.
        eapply rtc_l; last eapply IHfuel, Hc.
        apply erased_step_seq_instr. constructor. by eapply step_exec_corrfail.
    - (* Faulted: the machine stops, or enters the exception handler. *)
      destruct (trap_halts _) eqn:Hhalt; simplify_eq.
      eapply rtc_l; last eapply IHfuel, Hc.
      apply erased_step_seq. by constructor.
    - (* NextI *)
      eapply rtc_l; last eapply IHfuel, Hc.
      apply erased_step_seq. constructor.
  Qed.

  (** A run with one interrupt of cause [c]: up to the first state that
      [stop] accepts, the interrupt there, if interrupts are enabled, then
      the rest of the run. *)
  Definition machine_run_irq (stop : ExecConf → bool) (fuel1 : nat) (c : Z)
      (fuel2 : nat) (σ : ExecConf) : option ConfFlag :=
    match machine_run_until stop fuel1 (Executable, σ) with
    | Some σ1 =>
        if decide (mie_of (get_a (sreg_word σ1 mstatus)) = InterruptEnabled)
        then machine_run fuel2 (Executable, enter_irq c σ1)
        else None
    | None => None
    end.

  Lemma machine_run_irq_hw_correct stop fuel1 c fuel2 (σ : ExecConf) cf' :
    c ∈ irq_causes →
    machine_run_irq stop fuel1 c fuel2 σ = Some cf' →
    ∃ σ', rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) ([Instr cf'], σ').
  Proof.
    intros Hcause. rewrite /machine_run_irq.
    destruct (machine_run_until stop fuel1 (Executable, σ)) as [σ1|] eqn:Hu; [|done].
    case_decide as Hen; [|done].
    intros Hrun.
    destruct (machine_run_hw_correct _ _ _ Hrun) as [σ' Hrest].
    exists σ'.
    eapply rtc_trans; [by apply rtc_erased_step_hw, (machine_run_until_correct _ _ _ _ _ Hu)|].
    eapply rtc_l; [|exact Hrest].
    exists []. eapply (step_atomic (Λ := griotte_hw_lang) _ _ _ _ _ [] []); [done|done|].
    by apply hw_irq_step.
  Qed.
End hw_machine_run.

(** The interpreter with one interrupt of cause [c], taken at the first
    state that [stop1] accepts if interrupts are enabled there, stopped
    at the next state that [stop2] accepts. *)
Definition machine_run_irq_until `{MP : MachineParameters} (stop1 : ExecConf → bool)
    (fuel1 : nat) (c : Z) (stop2 : ExecConf → bool) (fuel2 : nat) (σ : ExecConf) :
    option ExecConf :=
  match machine_run_until stop1 fuel1 (Executable, σ) with
  | Some σ1 =>
      if decide (mie_of (get_a (sreg_word σ1 mstatus)) = InterruptEnabled)
      then machine_run_until stop2 fuel2 (Executable, enter_irq c σ1)
      else None
  | None => None
  end.

Lemma machine_run_irq_until_hw_correct `{MP : MachineParameters} stop1 fuel1 c stop2 fuel2
    (σ σ2 : ExecConf) :
  c ∈ irq_causes →
  machine_run_irq_until stop1 fuel1 c stop2 fuel2 σ = Some σ2 →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) ([griotte_lang.Exec], σ2).
Proof.
  intros Hcause. rewrite /machine_run_irq_until.
  destruct (machine_run_until stop1 fuel1 (Executable, σ)) as [σ1|] eqn:Hu; [|done].
  case_decide as Hen; [|done].
  intros Hrun.
  eapply rtc_trans; [by apply rtc_erased_step_hw, (machine_run_until_correct _ _ _ _ _ Hu)|].
  eapply rtc_l; [|by apply rtc_erased_step_hw, (machine_run_until_correct _ _ _ _ _ Hrun)].
  exists []. eapply (step_atomic (Λ := griotte_hw_lang) _ _ _ _ _ [] []); [done|done|].
  by apply hw_irq_step.
Qed.
