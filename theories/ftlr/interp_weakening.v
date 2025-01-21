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
    p <> E ->
    p ≠ O →
    p' ≠ E →
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
    destruct (perm_eq_dec p O) as [|_];try congruence.
    destruct (perm_eq_dec p E) as [|_];try congruence.
    destruct (perm_eq_dec p' O) as [|_];try congruence.
    destruct (perm_eq_dec p' E) as [|_];try congruence.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iSplit; cycle 1.
    { case_eq (pwl p'); intros Hpwl'; auto.
      assert (pwl p = true) as Hpwl by (destruct p, p'; naive_solver).
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; try tauto. auto.
    }

    case_eq (pwl p'); intros Hpwl'; auto.
    - assert (pwl p = true) as Hpwl by (destruct p, p'; naive_solver).
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
      iDestruct "Hw" as (p'' Hflp'') "[#X %Hpwl_cond]".
      rewrite Hpwl in Hpwl_cond.
      assert ( PermFlows p' p'')
        as Hflp' by (eapply PermFlowsToPermFlows; eapply PermFlowsToTransitive; eauto).
      iExists p''; iFrame "%".
      destruct p,p'; inv Hp; cbn; iFrame "#"; iPureIntro.
    - case_eq (pwl p); intros Hpwl; auto; rewrite Hpwl in Hpwl_cond; simplify_eq.
      + destruct g' ; inv Hl.
        destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' Hflp'') "[#X %Hstate]".
        assert ( PermFlows p' p'')
          as Hflp' by (eapply PermFlowsToPermFlows; eapply PermFlowsToTransitive; eauto).
        iExists p''; iFrame "%".
        assert (region_state_nwl W x Local)
          as Hstate' by (cbn in * ; naive_solver).
        destruct p,p'; inv Hp; cbn; iFrame "#"; try done.
        all: iSplit;[|done].
        all: iSplit;[iPureIntro;apply _|iApply rcond_interp].
      + destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' Hflp'') "[#X %Hstate]".
        assert ( PermFlows p' p'')
          as Hflp' by (eapply PermFlowsToPermFlows; eapply PermFlowsToTransitive; eauto).
        iExists p''; iFrame "%".
        assert (region_state_nwl W x g')
          as Hstate' by (destruct g,g'; inv Hl ; cbn in * ; naive_solver).
        destruct p,p'; inv Hp; cbn; iFrame "#"; try done.
        all: iSplit;[|done].
        all: iSplit;[iPureIntro;apply _|iApply rcond_interp].
  Qed.

  Lemma interp_weakening W p p' g g' b b' e e' a a' :
      p <> E ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo p' p ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      (fixpoint interp1) W (WCap p g b e a) -∗
      (fixpoint interp1) W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    destruct (perm_eq_dec p E); try congruence.
    destruct (perm_eq_dec p' O).
    { subst.
      rewrite !fixpoint_interp1_eq !interp1_eq. auto. }
    destruct (perm_eq_dec p O).
    { subst p; destruct p'; simpl in Hp; try tauto. }
    destruct (perm_eq_dec p' E).
    { rewrite !fixpoint_interp1_eq !interp1_eq.
      destruct (perm_eq_dec p' O);try congruence.
      destruct (perm_eq_dec p' E);try congruence.
      destruct (perm_eq_dec p O);try congruence.
      destruct (perm_eq_dec p E);try congruence.
      iDestruct "HA" as "[#A %]".
      (* p' = E *) subst p'. iModIntro.
      rewrite /enter_cond /interp_expr /=.
      iIntros (r W') "#Hfuture". iNext.
      iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iModIntro. rewrite fixpoint_interp1_eq /=.
      simpl. destruct (decide (b' < e'))%a.
      - rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
        rewrite !big_sepL_app. iDestruct "A" as "[A1 [A2 A3]]".
        iApply (big_sepL_impl with "A2"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p' Hflp') "[#X %]".
        assert (Hflows': PermFlows RX p').
        { eapply PermFlows_trans; eauto.
          destruct p; simpl in *; auto; try congruence; try tauto; reflexivity. }
        destruct (writeAllowed p).
        { iExists p',interp.
          iSplitR; auto.
          iSplitR; first (iPureIntro; by apply _).
          iFrame "X".
          iSplitR; first iApply rcond_interp.
          iApply (region_state_nwl_future with "Hfuture"); eauto.
        }
        { iDestruct "X" as (P HpersP) "X".
          iExists p',P.
          iSplitR; auto.
          iSplitR; first (iPureIntro; by apply _).
          iFrame "X".
          iApply (region_state_nwl_future with "Hfuture"); eauto.
        }
      - rewrite /region_conditions (finz_seq_between_empty b' e'); auto. solve_addr.
    }
    iApply (interp_weakeningEO _ p p' g g'); eauto.
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
