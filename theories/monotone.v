From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Export invariants na_invariants saved_prop.
From cap_machine Require Export logrel region_invariants_transitions.
Import uPred.

Section monotone.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {switcherg :switcherG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma region_state_pub_perm W W' a :
    related_sts_pub_world W W'
    → (std W) !! a = Some Permanent
    -> (std W') !! a = Some Permanent.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated a Permanent y Hstate Hy).
    apply std_rel_pub_rtc_Permanent in Hrelated; subst; auto.
  Qed.

  Lemma region_state_pub_temp W W' a :
    related_sts_pub_world W W'
    → (std W) !! a = Some Temporary
    -> (std W') !! a = Some Temporary.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated _ Temporary y Hstate Hy).
    apply std_rel_pub_rtc_Temporary in Hrelated; subst; auto.
  Qed.

  Lemma region_state_priv_perm W W' a :
    related_sts_priv_world W W'
    → (std W) !! a = Some Permanent
    -> (std W') !! a = Some Permanent.
  Proof.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some ((std W') !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom;eauto. }
    specialize (Hrelated a Permanent y Hstate Hy).
    eapply std_rel_rtc_Permanent in Hrelated;subst;auto.
  Qed.

  Lemma region_state_nwl_monotone W W' a l :
    related_sts_pub_world W W' →
    region_state_nwl W a l -> region_state_nwl W' a l.
  Proof.
    rewrite /region_state_nwl.
    intros  Hrelated Hstate; simplify_eq.
    destruct l.
    - eapply region_state_pub_perm; eauto.
    - destruct Hstate as [Hstate|Hstate].
      + eapply region_state_pub_perm in Hstate; eauto.
      + eapply region_state_pub_temp in Hstate; eauto.
  Qed.

  Lemma region_state_nwl_monotone_nl W W' a :
    related_sts_priv_world W W' →
    region_state_nwl W a Global -> region_state_nwl W' a Global.
  Proof.
    rewrite /region_state_nwl.
    intros Hrelated Hstate; simplify_eq.
    eapply region_state_priv_perm;eauto.
  Qed.

  Lemma region_state_pwl_monotone W W' a :
    related_sts_pub_world W W' →
    region_state_pwl W a -> region_state_pwl W' a.
  Proof.
    rewrite /region_state_pwl /region_state_nwl.
    intros Hrelated Hstate; simplify_eq.
    eapply region_state_pub_temp in Hstate; eauto.
  Qed.

  Lemma region_state_nwl_future W W' l l' p a:
    LocalityFlowsTo l' l ->
    (if isWL p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜region_state_nwl W' a l'⌝.
  Proof.
    intros Hlflows Hloc. iIntros "Hfuture %".
    rewrite /future_world.
    destruct l'; simpl; iDestruct "Hfuture" as %Hf; iPureIntro.
    - assert (l = Global) as -> by (destruct l; simpl in Hlflows; tauto).
      destruct (isWL p) eqn:HpwlU; try congruence.
      eapply region_state_nwl_monotone_nl; last eauto; eauto.
    - destruct (isWL p).
      + subst l.
        rewrite /region_state_nwl.
        right; eapply region_state_pub_temp; eauto.
      + generalize (region_state_nwl_monotone _ _ _ _ Hf H).
        destruct l; auto.
  Qed.

  Lemma region_state_future W W' l l' p p' a:
    PermFlowsTo p' p ->
    LocalityFlowsTo l' l ->
    (if isWL p then l = Local else True) ->
    (@future_world Σ l' W W') -∗
    ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝ -∗
    ⌜if isWL p' then region_state_pwl W' a else region_state_nwl W' a l'⌝.
  Proof.
    intros Hpflows Hlflows Hloc. iIntros "Hfuture %Hstate".
    case_eq (isWL p'); intros Hpwlp'.
    - assert (isWL p = true) as Hpwl.
      { destruct_perm p; destruct_perm p'; simpl in Hpwlp'; try congruence; simpl in Hpflows; try tauto. }
      rewrite Hpwl in Hstate, Hloc; subst l.
      destruct l'; simpl in Hlflows; try tauto.
      rewrite /future_world.
      simpl; iDestruct "Hfuture" as "%"; iPureIntro.
      eapply region_state_pwl_monotone; last eauto; eauto.
    - iApply (region_state_nwl_future with "Hfuture"); eauto.
  Qed.

  Lemma region_state_Revoked_monotone (W W' : WORLD) (a : Addr) :
    related_sts_pub_world W W' →
    (std W) !! a = Some Revoked ->
    (std W') !! a = Some Revoked ∨
    (std W') !! a = Some Temporary ∨
    (std W') !! a = Some Permanent.
  Proof.
    rewrite /region_state_pwl /std.
    intros Hrelated Hstate.
    destruct Hrelated as [ [Hdom_sta Hrelated ] _]. simpl in *.
    assert (is_Some (W'.1 !! a)) as [y Hy].
    { rewrite -elem_of_dom. apply elem_of_subseteq in Hdom_sta. apply Hdom_sta. rewrite elem_of_dom ;eauto. }
    specialize (Hrelated _ Revoked y Hstate Hy).
    apply std_rel_pub_rtc_Revoked in Hrelated; auto.
    destruct Hrelated as [Hperm | [Hmono | Hrev] ]; subst; auto.
  Qed.

  Lemma monoReq_mono_pub_nwl W W' C (P : D) a p g:
    related_sts_pub_world W W'
    -> region_state_nwl W a g
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    destruct g.
    - pose proof (region_state_pub_perm _ _ _ Hrelated Hstate) as Hnext_state.
      by rewrite Hstate Hnext_state.
    - destruct Hstate as [Hstate|Hstate].
      + pose proof (region_state_pub_perm _ _ _ Hrelated Hstate) as Hnext_state.
        by rewrite Hstate Hnext_state.
      + pose proof (region_state_pub_temp _ _ _ Hrelated Hstate) as Hnext_state.
        by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_mono_pub_pwl W W' C (P : D) a p:
    related_sts_pub_world W W'
    -> region_state_pwl W a
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    pose proof (region_state_pub_temp _ _ _ Hrelated Hstate) as Hnext_state.
    by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_mono_priv_nwl W W' C (P : D) a p:
    related_sts_priv_world W W'
    -> region_state_nwl W a Global
    -> monoReq W C a p P
    -∗ monoReq W' C a p P.
  Proof.
    intros Hrelated Hstate; simplify_eq.
    iIntros "HmonoW"; rewrite /monoReq.
    pose proof (region_state_priv_perm _ _ _ Hrelated Hstate) as Hnext_state.
    by rewrite Hstate Hnext_state.
  Qed.

  Lemma monoReq_nwl_future W W' C l l' p p' a P:
    LocalityFlowsTo l' l
    -> PermFlowsTo p p'
    -> (if isWL p then l = Local else True)
    -> (@future_world Σ l' W W')
    -∗ ⌜if isWL p then region_state_pwl W a else region_state_nwl W a l⌝
    -∗ monoReq W C a p' P
    -∗ monoReq W' C a p' P.
  Proof.
    intros Hlflows Hflp Hloc. iIntros "Hfuture %Hstate HmonoR".
    rewrite /future_world.
    destruct l'; simpl
    ; iDestruct "Hfuture" as %Hrelated
    ; destruct (isWL p) eqn:Hpwl
    ; simplify_map_eq
    ; try done.
    - destruct l ; try done.
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
    - iDestruct (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
    - iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
  Qed.

  Lemma interp_monotone_sd W W' C ot sb :
    ⌜related_sts_priv_world W W'⌝
    -∗ interp W C (WSealed ot sb) -∗ interp W' C (WSealed ot sb).
  Proof.
    iIntros (Hrelated) "#Hinterp".
    rewrite !fixpoint_interp1_eq /= /interp_sb.
    iDestruct "Hinterp" as (P Hpers) "(Hmono & Hseal_pred & HP & HPborrowed)".
    iFrame "#%".
    iApply later_sep_1; iNext.
    rewrite /future_priv_mono.
    iPoseProof "Hmono" as "Hmono'".
    iSpecialize ("Hmono" $! (WSealable sb)).
    iSpecialize ("Hmono'" $! (borrow (WSealable sb))).
    destruct (decide (borrow (WSealable sb) = switcher_ret_entry_point)).
    { exfalso. cbn in e.
      rewrite switcher_ret_correct in e.
      destruct sb ; cbn in e; congruence.
    }
    destruct (decide (WSealable sb = switcher_ret_entry_point)).
    { exfalso.
      by rewrite switcher_ret_correct in e.
    }
    iDestruct ("Hmono" $! W W' with "[] [] [$HP]") as "HP'"
    ; rewrite /safeC /=
    ; eauto.
    iDestruct ("Hmono'" $! W W' with "[] [] [HPborrowed]") as "HPborrowed'"
    ; rewrite /safeC /=
    ; eauto.
    iFrame "#".
  Qed.

  Lemma interp_monotone W W' C w :
    ⌜related_sts_pub_world W W'⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrelated) "#Hw".
    destruct w; [ | shelve | | ].
    { rewrite !fixpoint_interp1_eq /=; auto. }
    { rewrite !fixpoint_interp1_eq /=.
      destruct (decide (WSentry p g b e a = switcher_ret_entry_point)).
      + rewrite decide_True; last done.
        rewrite decide_True; last done.
        iModIntro. iIntros (r W'').
        iIntros "#Hrelated'".
        rewrite /future_world.
        iDestruct "Hrelated'" as "%Hrelated'".
        iAssert (future_world Local W W'')%I as "Hrelated".
        { rewrite /future_world.
          iPureIntro. apply related_sts_pub_trans_world with W'; auto. }
        iSpecialize ("Hw" $! r W'' with "Hrelated").
        iApply "Hw".
      + rewrite decide_False; last done.
        rewrite decide_False; last done.
        iModIntro. iIntros (r W'').
        destruct g.
        * iIntros "#Hrelated'".
          rewrite /future_world.
          iDestruct "Hrelated'" as "%Hrelated'".
          iAssert (future_world Global W W'')%I as "Hrelated".
          { rewrite /future_world.
            iPureIntro. apply related_sts_pub_priv_trans_world with W'; auto. }
          iSpecialize ("Hw" $! r W'' with "Hrelated").
          iApply "Hw".
        * iIntros "#Hrelated'".
          rewrite /future_world.
          iDestruct "Hrelated'" as "%Hrelated'".
          iAssert (future_world Local W W'')%I as "Hrelated".
          { rewrite /future_world.
            iPureIntro. apply related_sts_pub_trans_world with W'; auto. }
          iSpecialize ("Hw" $! r W'' with "Hrelated").
          iApply "Hw".
    }
    { apply related_sts_pub_priv_world in Hrelated.
      iApply (interp_monotone_sd with "[] [$Hw]"); eauto.
    }
    Unshelve.
    destruct sb; cycle 1.
    { rewrite !fixpoint_interp1_eq /=; auto. }
    destruct p eqn:Hp;auto; cycle 1.
    destruct rx,w; rewrite !fixpoint_interp1_eq /=; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_nwl_monotone W W');eauto.
    - destruct g; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_pwl_monotone W W');eauto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_nwl_monotone W W');eauto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_nwl_monotone W W');eauto.
    - destruct g; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_pwl_monotone W W');eauto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_nwl_monotone W W');eauto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_nwl_monotone W W');eauto.
    - destruct g; auto.
      iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_pub_pwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; eapply (region_state_pwl_monotone W W');eauto.
  Qed.

 Lemma interp_monotone_nl W W' C w :
    ⌜related_sts_priv_world W W'⌝
    -∗ ⌜isLocalWord w = false⌝
    -∗ ⌜w ≠ switcher_ret_entry_point⌝
    -∗ interp W C w -∗ interp W' C w.
  Proof.
    iIntros (Hrelated Hnl Hneq_switcher) "#Hw".
    destruct w; [ | shelve | | ].
    { rewrite !fixpoint_interp1_eq /=; auto. }
    { rewrite !fixpoint_interp1_eq /=.
      rewrite decide_False ; last done.
      rewrite decide_False ; last done.
      destruct g ; cbn in Hnl ; try done.
      iModIntro. iIntros (r W'').
      iIntros "#Hrelated'".
      rewrite /future_world.
      iDestruct "Hrelated'" as "%Hrelated'".
      iAssert (future_world Global W W'')%I as "Hrelated".
      { rewrite /future_world.
        iPureIntro. apply related_sts_priv_trans_world with W'; auto. }
      iSpecialize ("Hw" $! r W'' with "Hrelated").
      iApply "Hw".
    }
    { iApply (interp_monotone_sd with "[] [$Hw]"); eauto. }
    Unshelve.
    destruct sb; cycle 1.
    { rewrite !fixpoint_interp1_eq /=; auto. }
    destruct g ; cbn in Hnl ; try done.
    destruct p eqn:Hp;auto; cycle 1.
    destruct rx,w; rewrite !fixpoint_interp1_eq /=; auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; apply (region_state_nwl_monotone_nl W W');auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; apply (region_state_nwl_monotone_nl W W');auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; apply (region_state_nwl_monotone_nl W W');auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; apply (region_state_nwl_monotone_nl W W');auto.
    - iApply (big_sepL_mono with "Hw").
      iIntros (n y Hsome) "Hw".
      iDestruct "Hw" as (p' P Hpfl' Hpers) "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
      iDestruct (monoReq_mono_priv_nwl with "HmonoR") as "HmonoR'"; eauto.
      iExists p',P. iFrame "∗%".
      iPureIntro; apply (region_state_nwl_monotone_nl W W');auto.
  Qed.

  (* The validity of regions are monotone wrt private/public future worlds *)
  (* Lemma adv_monotone W W' b e : *)
  (*   related_sts_priv_world W W' → *)
  (*   ([∗ list] a ∈ finz.seq_between b e, read_write_cond a RX interp *)
  (*                     ∧ ⌜std W !! a = Some Permanent⌝) *)
  (*   -∗ ([∗ list] a ∈ finz.seq_between b e, read_write_cond a RX interp *)
  (*                     ∧ ⌜std W' !! a = Some Permanent⌝). *)
  (* Proof. *)
  (*   iIntros (Hrelated) "Hr". *)
  (*   iApply (big_sepL_mono with "Hr"). *)
  (*   iIntros (k y Hsome) "(Hy & Hperm)". *)
  (*   iFrame. *)
  (*   iDestruct "Hperm" as %Hperm. *)
  (*   iPureIntro. *)
  (*   apply (region_state_nwl_monotone_nl _ W') in Hperm; auto. *)
  (* Qed. *)

  (* Lemma adv_stack_monotone W W' b e : *)
  (*   related_sts_pub_world W W' -> *)
  (*   ([∗ list] a ∈ finz.seq_between b e, read_write_cond a RWLX interp *)
  (*                                    ∧ ⌜region_state_pwl W a⌝) *)
  (*   -∗ ([∗ list] a ∈ finz.seq_between b e, read_write_cond a RWLX interp *)
  (*                                      ∧ ⌜region_state_pwl W' a⌝). *)
  (* Proof. *)
  (*   iIntros (Hrelated) "Hstack_adv". *)
  (*   iApply (big_sepL_mono with "Hstack_adv"). *)
  (*   iIntros (k y Hsome) "(Hr & Htemp)". *)
  (*   iDestruct "Htemp" as %Htemp. *)
  (*   iFrame. iPureIntro. *)
  (*   apply (region_state_pwl_monotone _ W') in Htemp; auto. *)
  (* Qed. *)

  (* The general monotonicity statement that interp gives you when writing a word into a
     pointer (p0, l, a2, a1, a0) ; simply a bundling of all individual monotonicity statements *)
Lemma interp_monotone_generalW (W : WORLD) (C : CmptName) (ρ : region_type)
  (p p' p'' : Perm) (g g' : Locality) (b e a b' e' a' : Addr) :
  std W !! a' = Some ρ →
  withinBounds b' e' a' = true →
  PermFlowsTo p' p'' →
  canStore p' (WCap p g b e a) = true →
  interp W C (WCap p' g' b' e' a') -∗
  monotonicity_guarantees_region C interpC p'' (WCap p g b e a) ρ.
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl' Hconds) "#Hvdst".
  destruct ρ;simpl;auto.
  - destruct (isWL p'') eqn: HpwlP''.
    + iModIntro; simpl;auto ; iIntros (W0 W1) "(%&%) HIW0".
      iApply interp_monotone; last eauto; eauto.
    + rewrite /future_priv_mono.
      destruct ( decide (WCap p g b e a = switcher_ret_entry_point) ); cycle 1.
      * iModIntro; simpl;auto ; iIntros (W0 W1) "_ %HIW0".
        destruct g.
        ** iApply interp_monotone_nl; last eauto; eauto.
      (* The below case is a contradiction, since if g is local,
      p' must be WL and p' flows into the non-WL p''*)
        ** destruct_perm p' ; try (simpl in Hconds; by exfalso).
           all:destruct_perm p''; (by exfalso).
      * iModIntro; simpl;auto ; iIntros (W0 W1) "(%&%) HIW0".
        iApply interp_monotone; last eauto; eauto.
  - rewrite /future_priv_mono.
    destruct ( decide (WCap p g b e a = switcher_ret_entry_point) ).
    + iModIntro; iIntros (W0 W1) "(%&%) HIW0".
      iApply interp_monotone; last eauto; eauto.
    + iModIntro; iIntros (W0 W1) "_ %HIW0".
      destruct g.
      * iApply interp_monotone_nl; last eauto; eauto.
      * (*Trick here: value relation leads to a contradiction if p' is WL,
        since then its region cannot be permanent *)
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      simplify_eq.
Qed.

Lemma interp_monotone_generalSentry (W : WORLD) (C : CmptName) (ρ : region_type)
  (p p' p'' : Perm) (g g' : Locality) (b e a b' e' a' : Addr) :
  std W !! a' = Some ρ →
  withinBounds b' e' a' = true →
  PermFlowsTo p' p'' →
  canStore p' (WSentry p g b e a) = true →
  interp W C (WCap p' g' b' e' a') -∗
  monotonicity_guarantees_region C interpC p'' (WSentry p g b e a) ρ.
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl' Hconds) "#Hvdst".
  destruct ρ;simpl;auto.
  - destruct (isWL p'') eqn: HpwlP''.
    + iModIntro; simpl;auto ; iIntros (W0 W1) "(%&%) HIW0".
      iApply interp_monotone; last eauto; eauto.
    + rewrite /future_priv_mono.
      destruct ( decide (WSentry p g b e a = switcher_ret_entry_point) ); cycle 1.
      * iModIntro; simpl;auto ; iIntros (W0 W1) "_ %HIW0".
        destruct g.
        ** iApply interp_monotone_nl; last eauto; eauto.
      (* The below case is a contradiction, since if g is local,
      p' must be WL and p' flows into the non-WL p''*)
        ** destruct_perm p' ; try (simpl in Hconds; by exfalso).
           all:destruct_perm p''; (by exfalso).
      * iModIntro; simpl;auto ; iIntros (W0 W1) "(%&%) HIW0".
        iApply interp_monotone; last eauto; eauto.
  - rewrite /future_priv_mono.
    destruct ( decide (WSentry p g b e a = switcher_ret_entry_point) ).
    + iModIntro; iIntros (W0 W1) "(%&%) HIW0".
      iApply interp_monotone; last eauto; eauto.
    + iModIntro; iIntros (W0 W1) "_ %HIW0".
      destruct g.
      * iApply interp_monotone_nl; last eauto; eauto.
      * (*Trick here: value relation leads to a contradiction if p' is WL,
        since then its region cannot be permanent *)
      iDestruct ( writeLocalAllowed_valid_cap_implies with "Hvdst" ) as %Ha; eauto.
      simplify_eq.
Qed.



(* Analogous, but now we have the general monotonicity statement in case an integer z is written *)
Lemma interp_monotone_generalZ (W : WORLD) (C : CmptName) (ρ : region_type)
  (p p' : Perm) (g : Locality) (b e a : Addr) z:
  std W !! a = Some ρ →
  withinBounds b e a = true →
  PermFlowsTo p p' →
  interp W C (WCap p g b e a) -∗
  monotonicity_guarantees_region C interpC p' (WInt z) ρ.
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst".
  destruct ρ;auto.
  - destruct (isWL p') eqn: HpwlP1.
    + iModIntro; simpl ; iIntros (W0 W1) "(%&%) HIW0".
      iApply interp_monotone; last eauto; eauto.
    + rewrite /future_priv_mono switcher_ret_correct.
      rewrite decide_False //.
      iModIntro; simpl ; iIntros (W0 W1) "% % HIW0".
      iApply interp_monotone_nl; last eauto; eauto.
  - rewrite /future_priv_mono switcher_ret_correct.
    rewrite decide_False //.
    iModIntro; simpl ; iIntros (W0 W1) "% % HIW0".
    iApply interp_monotone_nl; last eauto; eauto.
Qed.

Lemma interp_monotone_generalSr (W : WORLD) (C : CmptName) (ρ : region_type)
  (p p' : Perm) (g : Locality) (b e a : Addr)
  (sp : SealPerms) (sg : Locality) (sb se sa : OType) :
  std W !! a = Some ρ →
  withinBounds b e a = true →
  PermFlowsTo p p' →
  interp W C (WCap p g b e a) -∗
  monotonicity_guarantees_region C interpC p' (WSealRange sp sg sb se sa) ρ.
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst".
  destruct ρ;auto.
  - destruct (isWL p') eqn: HpwlP1.
    + iModIntro; simpl ; iIntros (W0 W1) "(%&%) HIW0".
      rewrite /interpC /safeC /= !fixpoint_interp1_eq;done.
    + rewrite /future_priv_mono switcher_ret_correct.
      rewrite decide_False //.
      iModIntro; simpl ; iIntros (W0 W1) "% % HIW0".
      rewrite /interpC /safeC /= !fixpoint_interp1_eq;done.
  - rewrite /future_priv_mono switcher_ret_correct.
    rewrite decide_False //.
    iModIntro; simpl ; iIntros (W0 W1) "% % HIW0".
    rewrite /interpC /safeC /= !fixpoint_interp1_eq;done.
Qed.

Lemma interp_monotone_generalSd (W : WORLD) (C : CmptName) (ρ : region_type)
  (p p' : Perm) (g : Locality) (b e a : Addr)
  (ot : OType) (sb : Sealable) :
  std W !! a = Some ρ →
  withinBounds b e a = true →
  PermFlowsTo p p' →
  interp W C (WCap p g b e a) -∗
  monotonicity_guarantees_region C interpC p' (WSealed ot sb) ρ.
Proof.
  unfold monotonicity_guarantees_region.
  iIntros (Hstd Hwb Hfl') "#Hvdst".
  destruct ρ;auto.
  - destruct (isWL p') eqn: Hpwlp'.
    + iModIntro; simpl; iIntros (W0 W1) "%Hrelated HIW0".
      iApply interp_monotone_sd; last eauto; eauto.
      by apply related_sts_pub_priv_world in Hrelated.
    + rewrite /future_priv_mono switcher_ret_correct.
      rewrite decide_False //.
      iModIntro; simpl; iIntros (W0 W1) "%Hrelated % HIW0".
      iApply interp_monotone_sd; last eauto; eauto.
  - rewrite /future_priv_mono switcher_ret_correct.
    rewrite decide_False //.
    iModIntro; simpl; iIntros (W0 W1) "%Hrelated % HIW0".
    iApply interp_monotone_sd; last eauto; eauto.
Qed.

End monotone.
