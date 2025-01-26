From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine Require Import addr_reg region monotone.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma interp_weakeningEO W p p' g g' b b' e e' a a' :
    isSentry p = false ->
    p ≠ O →
    isSentry p' = false ->
    p' ≠ O →
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    (fixpoint interp1) W (WCap p g b e a) -∗
    (fixpoint interp1) W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE HpnotO HpnotE' HpnotO' Hb He Hp Hl. iIntros "HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (decide (p = O)) as [|_];try congruence.
    destruct (decide (p' = O)) as [|_];try congruence.
    rewrite HpnotE HpnotE'.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iSplit; cycle 1.
    { case_eq (pwl p'); intros Hpwl'; auto.
      assert (pwl p = true) as Hpwl by (destruct_perm p; destruct_perm p'; naive_solver).
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; try tauto. auto.
    }

    case_eq (pwl p'); intros Hpwl'; auto.
    - assert (pwl p = true) as Hpwl by (destruct_perm p; destruct_perm p'; naive_solver).
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; try tauto.
      clear Hl Hpwl_cond.
      destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
      { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
      rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
      rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
      iApply (big_sepL_impl with "A"); auto.
      iModIntro; iIntros (k x Hx) "Hw".
      iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)".
      rewrite Hpwl in Hstate.
      assert ( PermFlowsTo p' p'')
        as Hflp' by (eapply PermFlowsToTransitive; eauto).
      iExists p'',φ; iFrame "∗%".
      by destruct_perm p; destruct_perm p'; inv Hp; cbn; iFrame.
    - case_eq (pwl p); intros Hpwl; auto; rewrite Hpwl in Hpwl_cond; simplify_eq.
      + destruct g' ; inv Hl.
        destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)".
        assert ( PermFlowsTo p' p'')
          as Hflp' by (eapply PermFlowsToTransitive; eauto).
        assert (region_state_nwl W x Local)
          as Hstate' by (cbn in * ; naive_solver).
        iExists p'',φ; iFrame "∗%".
        by destruct_perm p; destruct_perm p'; inv Hp; cbn; iFrame.
      + destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & %Hstate)".
        assert ( PermFlowsTo p' p'')
          as Hflp' by (eapply PermFlowsToTransitive; eauto).
        assert (region_state_nwl W x g')
          as Hstate' by (destruct g,g'; inv Hl ; cbn in * ; naive_solver).
        iExists p'',φ; iFrame "∗%".
      by destruct_perm p; destruct_perm p'; inv Hp; cbn; iFrame.
  Qed.

  Lemma interp_weakeningE W p g g' b b' e e' a a' :
      isSentry p = false ->
      p <> O ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo E p ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      (fixpoint interp1) W (WCap p g b e a) -∗
      (fixpoint interp1) W (WCap E g' b' e' a').
  Proof.
    intros HpnotE HpnotO Hb He Hp Hl.
    iIntros "#IH HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    destruct (decide (p = O)) as [|_];try congruence.
    rewrite HpnotE.
    erewrite decide_False;auto; cbn.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iModIntro.
    rewrite /enter_cond /interp_expr /=.
    iIntros (r W') "#Hfuture". iNext.
    iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
    rewrite /interp_conf.
    iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
    iModIntro. rewrite fixpoint_interp1_eq /=.
    simpl. destruct (decide (b' < e'))%a.
    - rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
      rewrite !big_sepL_app. iDestruct "A" as "[_ [A2 _]]".
      iApply (big_sepL_impl with "A2"); auto.
      iModIntro; iIntros (k x Hx) "Hw".
      iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & #Hzcond & #Hrcond & #Hwcond & %Hstate)".
      assert (Hflows': PermFlowsTo RX p'').
      { eapply PermFlowsTo_trans; eauto.
        destruct p; simpl in *; auto; try congruence; try tauto; reflexivity. }
      iExists p'',φ.
      replace (readAllowed p) with true; cycle 1.
      { destruct_perm p ; cbn in *; try done. }
      iFrame "Hrel".
      repeat(iSplit; auto).
      iApply (region_state_nwl_future with "Hfuture"); eauto.
    - rewrite (finz_seq_between_empty b' e'); auto; solve_addr.
  Qed.

  Lemma interp_weakening W p p' g g' b b' e e' a a' :
    isSentry p = false ->
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    ftlr_IH -∗
    (fixpoint interp1) W (WCap p g b e a) -∗
    (fixpoint interp1) W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    destruct (decide (p' = O)).
    { subst; rewrite !fixpoint_interp1_eq !interp1_eq; auto. }
    destruct (decide (p = O)).
    { subst p; destruct_perm p'; simpl in Hp; try tauto. }
    destruct (isSentry p') eqn:Hsentryp'; cycle 1.
    { iApply (interp_weakeningEO _ p p' g g'); eauto. }
    { destruct p, p' ; cbn in * ; try congruence. iApply (interp_weakeningE _ (BPerm rx w) g g'); eauto. }
  Qed.

  Lemma interp_next_PC W p g b e a a' :
    isCorrectPC (WCap p g b e a) ->
    ftlr_IH -∗
    interp W (WCap p g b e a) -∗
    interp W (WCap p g b e a').
  Proof.
    iIntros (HcorrectPC) "#IH #Hinterp".
    iApply interp_weakening; eauto; try solve_addr; try done.
    by eapply isCorrectPC_nonE.
  Qed.

  Lemma safe_to_unseal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal (fixpoint interp1) b e -∗
    safe_to_unseal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal (fixpoint interp1) b e -∗
    safe_to_seal (fixpoint interp1) b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma interp_weakening_ot W p p' g g' b b' e e' a a':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    SealPermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    (fixpoint interp1) W (WSealRange p g b e a) -∗
    (fixpoint interp1) W (WSealRange p' g' b' e' a').
  Proof.
  intros Hb He Hp Hg. iIntros "#HA".
  rewrite !fixpoint_interp1_eq. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Qed.

End fundamental.
