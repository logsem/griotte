From stdpp Require Import base.
From iris.program_logic Require Import language.
From cap_machine Require Import machine_parameters machine_base cap_lang.

(* The operational semantics as an interpreter: this effectively "runs" the
   machine until it fails or halts (or we run out of fuel). *)

Definition isCorrectPCb (w: Word): bool :=
  match w with
  | WCap p g b e a =>
    (b <=? a)%a && (a <? e)%a && executeAllowed p
  | _ => false
  end.

Lemma isCorrectPCb_isCorrectPC w :
  isCorrectPCb w = true ↔ isCorrectPC w.
Proof.
  rewrite /isCorrectPCb. destruct_word w.
  1,3,4,5 : split; try congruence; inversion 1.
  { rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt.
    split.
    { intros [? ?]. constructor. solve_addr. naive_solver. }
    { inversion 1; subst. split. solve_addr. naive_solver. } }
Qed.

Lemma isCorrectPCb_nisCorrectPC w :
  isCorrectPCb w = false ↔ ¬ isCorrectPC w.
Proof.
  destruct (isCorrectPCb w) eqn:HH.
  { apply isCorrectPCb_isCorrectPC in HH. split; congruence. }
  { split; auto. intros _. intros ?%isCorrectPCb_isCorrectPC. congruence. }
Qed.


Fixpoint machine_run `{MachineParameters} (fuel: nat) (c: Conf): option ConfFlag :=
  match fuel with
  | 0 => None
  | S fuel =>
    match c with
    | (Failed, _) => Some Failed
    | (Halted, _) => Some Halted
    | (NextI, φ) => machine_run fuel (Executable, φ)
    | (Executable, (r, sr, m)) =>
      match r !! PC with
      | None => Some Failed
      | Some pc =>
        if isCorrectPCb pc
        then (
            let a := match pc with
                     | WCap _ _ _ _ a => a
                     | _ => top (* dummy *)
                     end
            in
            let p := match pc with
                     | WCap p _ _ _ _ => p
                     | _ => RWX (* dummy *)
                     end
            in
            match m !! a with
            | None => Some Failed
            | Some wa =>
                let i := decodeInstrW wa in
                let c' := exec i p (r, sr, m) in
                machine_run fuel (c'.1,  c'.2)
            end
          ) else (
          Some Failed
        )
      end
    end
  end.

Lemma machine_run_correct `{MachineParameters} fuel cf (φ: ExecConf) cf':
  machine_run fuel (cf, φ) = Some cf' →
  ∃ φ', rtc erased_step
            ([Seq (Instr cf)], φ)
            ([Instr cf'], φ').
Proof.
  revert cf cf' φ. induction fuel.
  { cbn. done. }
  { cbn. intros ? ? [ [r sr] m ] Hc.
    destruct cf; simplify_eq.
    destruct (r !! PC) as [wpc | ] eqn:HePC.
    2: {
      eexists. eapply rtc_l. unfold erased_step. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
      constructor. constructor; auto.
      eapply rtc_once. exists []. simplify_eq.
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      constructor. }
    destruct (isCorrectPCb wpc) eqn:HPC.
    { apply isCorrectPCb_isCorrectPC in HPC.
      destruct wpc eqn:Hr; [by inversion HPC| | by inversion HPC | by inversion HPC]. destruct sb as [p g b e a | ]; last by inversion HPC.
      destruct (m !! a) as [wa | ] eqn:HeMem.
      2: {
        eexists. eapply rtc_l. unfold erased_step. exists [].
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
        constructor. eapply step_exec_memfail; eauto.
        eapply rtc_once. exists []. simplify_eq.
        eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
        eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
        constructor. }
      eapply IHfuel in Hc as [φ' Hc]. eexists.
      eapply rtc_l. unfold erased_step. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity.
      constructor. eapply step_exec_instr; eauto. eapply Hc.
    }
    { simplify_eq. apply isCorrectPCb_nisCorrectPC in HPC.
      eexists. eapply rtc_l. unfold erased_step. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[SeqCtx]). 1,2: reflexivity. cbn.
      constructor. eapply step_exec_corrfail; eauto.
      eapply rtc_once. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      constructor. }
    { eexists. eapply rtc_once. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor. }
    { eexists. eapply rtc_once. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor. }
    { apply IHfuel in Hc as [φ' Hc]. eexists.
      eapply rtc_l. exists [].
      eapply step_atomic with (t1:=[]). 1,2: reflexivity. cbn.
      eapply ectx_language.Ectx_step with (K:=[]). 1,2: reflexivity. cbn.
      econstructor. cbn. apply Hc. } }
Qed.
