From iris.program_logic Require Import language.
From griotte Require Import machine_parameters machine_base griotte_lang.

(* The operational semantics as an interpreter: this effectively "runs" the
   machine until it halts or stops after a fault (or we run out of fuel). A
   fault enters the exception handler, unless neither the PC nor MTCC is
   tagged: the machine then stops. *)

Fixpoint machine_run `{MachineParameters} (fuel: nat) (c: Conf): option ConfFlag :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | (Faulted, φ) =>
        if trap_halts φ then Some Faulted
        else machine_run fuel (Executable, enter_exc (trap_cause φ, trap_tval φ) φ)
    | (Halted, _) => Some Halted
    | (NextI, φ) => machine_run fuel (Executable, φ)
    | (Executable, (pc, r, sr, m, st)) =>
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
            | None => machine_run fuel (Faulted, (pc, r, sr, m, st))
            | Some wa =>
                let i := decodeInstrW wa in
                let c' := exec i p (pc, r, sr, m, st) in
                machine_run fuel (c'.1,  c'.2)
            end
          ) else machine_run fuel (Faulted, (pc, r, sr, m, st))
    end
  end.

(* One step of the configuration [Seq (Instr cf)], from a base step of
   [Instr cf] under [Seq]. *)
Lemma erased_step_seq_instr `{MachineParameters} c c' (φ φ' : ExecConf) :
  griotte_lang.prim_step (Instr c) φ [] (Instr c') φ' [] →
  erased_step ([Seq (Instr c)], φ) ([Seq (Instr c')], φ').
Proof.
  intros Hstep. exists [].
  eapply step_atomic with (t1:=[]); [reflexivity|reflexivity|]. cbn.
  by eapply ectx_language.Ectx_step with (K:=[SeqCtx]).
Qed.

(* One step of a single-thread configuration, from a base step. *)
Lemma erased_step_seq `{MachineParameters} e (φ φ' : ExecConf) e' :
  griotte_lang.prim_step e φ [] e' φ' [] →
  erased_step ([e], φ) ([e'], φ').
Proof.
  intros Hstep. exists [].
  eapply step_atomic with (t1:=[]); [reflexivity|reflexivity|]. cbn.
  by eapply ectx_language.Ectx_step with (K:=[]).
Qed.

Lemma machine_run_correct `{MachineParameters} fuel cf (φ: ExecConf) cf':
  machine_run fuel (cf, φ) = Some cf' →
  ∃ φ', rtc erased_step
            ([Seq (Instr cf)], φ)
            ([Instr cf'], φ').
Proof.
  revert cf cf' φ. induction fuel as [|fuel IHfuel]; first (cbn; done).
  cbn. intros cf cf' [[[[wpc r] sr] m] st] Hc.
  destruct cf; simplify_eq.
  - (* Executable: the fetch and the instruction, then the rest of the run. *)
    destruct (isCorrectPCb wpc) eqn:HPC.
    + apply isCorrectPCb_isCorrectPC in HPC.
      inversion HPC as [p g b e a Hbounds Hx Hwpc]; subst wpc.
      destruct (m !! a) as [wa | ] eqn:HeMem.
      * eapply IHfuel in Hc as [φ' Hc]. eexists.
        eapply rtc_l; last eapply Hc.
        apply erased_step_seq_instr. constructor. eapply step_exec_instr; eauto.
      * eapply IHfuel in Hc as [φ' Hc]. eexists.
        eapply rtc_l; last eapply Hc.
        apply erased_step_seq_instr. constructor. eapply step_exec_memfail; eauto.
    + apply isCorrectPCb_nisCorrectPC in HPC.
      eapply IHfuel in Hc as [φ' Hc]. eexists.
      eapply rtc_l; last eapply Hc.
      apply erased_step_seq_instr. constructor. by eapply step_exec_corrfail.
  - (* Halted *)
    eexists. eapply rtc_once. apply erased_step_seq. constructor.
  - (* Faulted: the machine stops, or enters the exception handler. *)
    destruct (trap_halts _) eqn:Hhalt; simplify_eq.
    + eexists. eapply rtc_once. apply erased_step_seq. by constructor.
    + eapply IHfuel in Hc as [φ' Hc]. eexists.
      eapply rtc_l; last eapply Hc.
      apply erased_step_seq. by constructor.
  - (* NextI *)
    apply IHfuel in Hc as [φ' Hc]. eexists.
    eapply rtc_l; last eapply Hc.
    apply erased_step_seq. constructor.
Qed.
