From iris.program_logic Require Import language.
From griotte Require Import machine_parameters machine_base griotte_lang.

(* The operational semantics as an interpreter: this effectively "runs" the
   machine until it fails or halts (or we run out of fuel). *)

Fixpoint machine_run `{MachineParameters} (fuel: nat) (c: Conf): option ConfFlag :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | (Faulted, _) => Some Faulted
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
            | None => Some Faulted
            | Some wa =>
                let i := decodeInstrW wa in
                let c' := exec i p (pc, r, sr, m, st) in
                machine_run fuel (c'.1,  c'.2)
            end
          ) else (
          Some Faulted
        )
    end
  end.

Lemma machine_run_correct `{MachineParameters} fuel cf (φ: ExecConf) cf':
  machine_run fuel (cf, φ) = Some cf' →
  ∃ φ', rtc erased_step
            ([Seq (Instr cf)], φ)
            ([Instr cf'], φ').
Proof.
  revert cf cf' φ. induction fuel; first (cbn; done).
  cbn. intros ? ? [[[[wpc r] sr] m] st] Hc.
  destruct cf; simplify_eq.
  - destruct (isCorrectPCb wpc) eqn:HPC.
      * apply isCorrectPCb_isCorrectPC in HPC.
        destruct wpc eqn:Hr; [by inversion HPC| | by inversion HPC | by inversion HPC]. destruct sb as [t p g b e a | ]; last by inversion HPC.
        destruct t; last by inversion HPC.
        destruct (m !! a) as [wa | ] eqn:HeMem.
        ** eapply IHfuel in Hc as [φ' Hc]. eexists.
           eapply rtc_l; last eapply Hc.
           unfold erased_step. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity.
           constructor. eapply step_exec_instr; eauto.
        ** eexists. eapply rtc_l.
           *** unfold erased_step. exists [].
               eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
               eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
               constructor. eapply step_exec_memfail; eauto.
           *** eapply rtc_once. exists []. simplify_eq.
               eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
               eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
               constructor.
      * simplify_eq. apply isCorrectPCb_nisCorrectPC in HPC.
        eexists. eapply rtc_l.
        ** unfold erased_step. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
           constructor. eapply step_exec_corrfail; eauto.
        ** eapply rtc_once. exists [].
           eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
           eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
           constructor.
  - eexists. eapply rtc_once. exists [].
    eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
    eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
    econstructor.
  - eexists. eapply rtc_once. exists [].
    eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
    eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
    econstructor.
  - apply IHfuel in Hc as [φ' Hc]. eexists.
    eapply rtc_l.
    + exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor.
    + cbn. apply Hc.
Qed.
