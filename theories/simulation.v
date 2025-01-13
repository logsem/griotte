From iris.program_logic Require Import language.
From stdpp Require Import list.

Section simulation.

  Definition final_state `{L: language} (s: cfg L) (v: val L): Prop :=
    exists e, fst s = [e] /\ to_val e = Some v.

  Lemma final_state_stuck `{L: language}:
    forall n κs (s: cfg L) v s',
      final_state s v ->
      nsteps n s κs s' ->
      n = 0 /\ s = s'.
  Proof.
    intros. inversion H0; auto.
    subst n. inversion H1. subst s.
    subst ρ1. eapply val_stuck in H8.
    inversion H. destruct H3.
    simpl in H3. 
    eapply app_eq_unit in H3.
    destruct H3.
    - destruct H3; subst t1.
      destruct t2; inversion H9.
      subst x; congruence.
    - destruct H3; congruence.
  Qed.

  Record forward_simulation `{L1: language} `{L2: language}
         (initial_state1: cfg L1)
         (initial_state2: cfg L2)
         (fsim: cfg L1 -> cfg L2 -> Prop)
         (fsim_val: val L1 -> val L2 -> Prop): Prop :=
    mk_fsim {
        fsim_init_states: fsim initial_state1 initial_state2;
        fsim_step: forall s1 s2 s1', fsim s1 s1' -> erased_step s1 s2 ->
                                exists s2', rtc erased_step s1' s2' /\ fsim s2 s2';
        fsim_final_states: forall s s' v, final_state s v -> fsim s s' -> exists v', final_state s' v' /\ fsim_val v v'
    }.

  Record forward_simulation_tc `{L1: language} `{L2: language}
         (initial_state1: cfg L1)
         (initial_state2: cfg L2)
         (fsim: cfg L1 -> cfg L2 -> Prop)
         (fsim_val: val L1 -> val L2 -> Prop): Prop :=
    mk_fsim_tc {
      fsim_tc_init_states: fsim initial_state1 initial_state2;
      fsim_tc_step: forall s1 s2 s1', fsim s1 s1' -> erased_step s1 s2 ->
                           exists s2', tc erased_step s1' s2' /\ fsim s2 s2';
      fsim_tc_final_states: forall s s' v, final_state s v -> fsim s s' -> exists v', final_state s' v' /\ fsim_val v v'
  }.

  Lemma fsim_tc_fsim:
  forall L1 L2 (initial_state1: cfg L1) (initial_state2: cfg L2) fsim fsim_val,
    forward_simulation_tc initial_state1 initial_state2 fsim fsim_val ->
    forward_simulation initial_state1 initial_state2 fsim fsim_val.
  Proof.
    intros. destruct H. econstructor; eauto.
    intros. eapply fsim_tc_step0 in H0; eauto.
    destruct H0 as [s2' [A B]]. exists s2'; split; auto.
    eapply tc_rtc; eauto.
  Qed.

  Lemma fsim_terminates:
    forall L1 L2 (initial_state1: cfg L1) (initial_state2: cfg L2) fsim fsim_val (Hsim: forward_simulation initial_state1 initial_state2 fsim fsim_val) s v,
      rtc erased_step initial_state1 s ->
      final_state s v ->
      exists s' v', rtc erased_step initial_state2 s' /\ final_state s' v' /\ fsim_val v v'.
  Proof.
    intros L1 L2 init_state1 init_state2 fsim fsim_val Hsim s v Hsteps Hfinal.
    revert Hsim. revert init_state2. induction Hsteps; intros init_state2 Hsim.
    - eapply (fsim_final_states _ _ _ _ Hsim) in Hfinal; eauto.
      destruct Hfinal as [v' [A B]].
      exists init_state2, v'. split; [left|split; eauto].
      eapply fsim_init_states; eauto.
    - eapply (fsim_step _ _ _ _ Hsim) in H; [|eapply fsim_init_states; eauto].
      destruct H as [y' [HA HB]].
      assert (Hsim': forward_simulation y y' fsim fsim_val).
      { econstructor.
        - eapply HB.
        - intros. eapply fsim_step; eauto.
        - intros. eapply fsim_final_states; eauto. }
      generalize (IHHsteps Hfinal y' Hsim'). intros [s' [v' [HC [HD HE]]]].
      exists s', v'; split; auto.
      eapply rtc_transitive; eauto.
  Qed.

  Definition determ `{L: language} (s: cfg L): Prop :=
    forall s', rtc erased_step s s' -> (forall s1 s2, erased_step s' s1 -> erased_step s' s2 -> s1 = s2).

  Lemma determ_step_preserves:
    forall L (s s': cfg L),
      erased_step s s' ->
      determ s ->
      determ s'.
  Proof.
    intros. red; intros.
    eapply H0; [eapply rtc_l; eauto|eauto..].
  Qed.

  Lemma fsim_backwards:
    forall L1 L2 (initial_state1: cfg L1) (initial_state2: cfg L2) (fsim: cfg L1 -> cfg L2 -> Prop) fsim_val (Hdeterm: determ initial_state2)
    (Hsafe: forall s1 s2, fsim s1 s2 -> (exists s1', erased_step s1 s1') \/ (exists v, final_state s1 v)),
      forward_simulation_tc initial_state1 initial_state2 fsim fsim_val ->
      (forall s s' v', final_state s' v' -> fsim s s' -> exists v, final_state s v /\ fsim_val v v') ->
      forward_simulation initial_state2 initial_state1 (fun s1 s2 => determ s1 /\ exists n κs s1', nsteps n s1 κs s1' /\ fsim s2 s1') (flip fsim_val).
  Proof.
    intros. econstructor.
    - split; auto. exists O, [], initial_state2. split; [econstructor|eapply fsim_tc_init_states; eauto].
    - intros. destruct H1 as [C [n [κs [s1'' [A B]]]]].
      inversion A; subst; clear A.
      + destruct (Hsafe _ _ B).
        * destruct H1 as [s'' D]. generalize D; intros D'.
          eapply fsim_tc_step in D'; eauto.
          destruct D' as [s1''' [E F]].
          inversion E; subst; clear E.
          { assert (s2 = s1''') by (eapply C; eauto; eapply rtc_refl).
            subst s2. exists s''. split; [eapply rtc_once; eauto|].
            split; [eapply determ_step_preserves; eauto|].
            exists 0, [], s1'''. split; auto. econstructor. }
          { assert (s2 = y) by (eapply C; eauto; eapply rtc_refl). subst s2.
            exists s''. split; [eapply rtc_once; eauto|].
            eapply tc_rtc in H3. eapply erased_steps_nsteps in H3.
            destruct H3 as [n [κs A]].
            split; [eapply determ_step_preserves; eauto|].
            exists n, κs, s1'''. split; auto. }
        * destruct H1. eapply fsim_tc_final_states in B; eauto.
          destruct B as [v' [D E]].
          assert (exists κs, nsteps (S 0) s1'' κs s2).
          { inversion H2. exists (x0 ++ []). econstructor; eauto.
            eapply nsteps_refl. }
          destruct H3 as [κs F].
          eapply final_state_stuck in D; eauto.
          destruct D as [? ?]; congruence.
      + exists s1'. split; [eapply rtc_refl|].
        assert (s2 = ρ2).
        { eapply C; eauto; [eapply rtc_refl|]. econstructor; eauto. }
        subst ρ2. split; eauto. eapply determ_step_preserves; eauto.
    - intros. destruct H2 as [C [n [κs [s1' [A B]]]]].
      eapply final_state_stuck in A; eauto. destruct A as [A A'].
      subst s1'. eapply H0 in H1; eauto.
  Qed.

End simulation.
