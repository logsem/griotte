From griotte Require Export opsem.griotte_opsem.

Definition isCorrectPCb (w: Word): bool :=
  match w with
  | WCap p g b e a =>
    (b <=? a)%a && (a <? e)%a && executeAllowed p
  | _ => false
  end.

Definition machine_step `{MachineParameters} (c : Conf) : option Conf :=
  match c with
  | (Executable, (r, sr, m) as phi) =>
      match r !! PC with
      | None => Some (Failed, phi)
      | Some pc =>
          if isCorrectPCb pc then
            match pc with
            | WCap p _ _ _ a =>
                match m !! a with
                | None => Some (Failed, phi)
                | Some wa => Some (exec (decodeInstrW wa) p phi)
                end
            | _ => Some (Failed, phi)
            end
          else Some (Failed, phi)
      end
  | _ => None
  end.

Lemma isCorrectPCb_isCorrectPC w :
  isCorrectPCb w = true ↔ isCorrectPC w.
Proof.
  rewrite /isCorrectPCb. destruct_word w.
  1,3,4,5 : split; try congruence; inversion 1.
  rewrite !andb_true_iff !Z.leb_le !Z.ltb_lt.
  split; [intros [? ?]; constructor; [solve_addr | naive_solver]|].
  inversion 1; subst. split; [solve_addr | naive_solver].
Qed.

Lemma isCorrectPCb_nisCorrectPC w :
  isCorrectPCb w = false ↔ ¬ isCorrectPC w.
Proof.
  destruct (isCorrectPCb w) eqn:HH.
  - apply isCorrectPCb_isCorrectPC in HH. split; congruence.
  - split; auto. intros _. intros ?%isCorrectPCb_isCorrectPC. congruence.
Qed.

Theorem machine_step_sound `{MachineParameters} c c' :
  machine_step c = Some c' → step c c'.
Proof.
  intros Hstep. destruct c as [cf [[r sr] m]].
  destruct cf; try discriminate. cbn in Hstep.
  destruct (r !! PC) as [pc|] eqn:Hpc.
  - destruct (isCorrectPCb pc) eqn:Hcorrect.
    + apply isCorrectPCb_isCorrectPC in Hcorrect.
      destruct pc as [z|[p g b e a|sp g b e o]|p g b e a|o sb];
        try by inversion Hcorrect.
      destruct (m !! a) as [wa|] eqn:Hmem.
      * destruct (exec (decodeInstrW wa) p (r, sr, m)) as [cf' phi'] eqn:Hexec.
        inversion Hstep; subst.
        eapply (step_exec_instr (r, sr, m) p g b e a
                  (decodeInstrW wa) (cf', phi') wa); eauto.
      * inversion Hstep; subst. eapply step_exec_memfail; eauto.
    + inversion Hstep; subst. eapply step_exec_corrfail; eauto.
      by apply isCorrectPCb_nisCorrectPC.
  - inversion Hstep; subst. by apply step_exec_regfail.
Qed.

Theorem machine_step_complete `{MachineParameters} c c' :
  step c c' -> machine_step c = Some c'.
Proof.
  intros Hstep. inversion Hstep; subst; destruct φ as [[r sr] m]; cbn in *.
  - rewrite /machine_step /= H0. reflexivity.
  - rewrite /machine_step /= H0.
    apply isCorrectPCb_nisCorrectPC in H1. rewrite H1. reflexivity.
  - rewrite /machine_step /= H0.
    destruct (isCorrectPCb (WCap p g b e a)); [rewrite H1 | ]; reflexivity.
  - rewrite /machine_step /= H0.
    assert (Hcorrect : isCorrectPCb (WCap p g b e a) = true).
    { apply isCorrectPCb_isCorrectPC. exact H2. }
    rewrite Hcorrect H1.
    destruct (exec (decodeInstrW wa) p (r, sr, m)). reflexivity.
Qed.
