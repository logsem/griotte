From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import addr_reg region monotone.
From cap_machine Require Export logrel ftlr_base.

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

  Lemma interp_weakening_from_E W g b e a :
      interp W (WCap E g b e a)
      -∗ interp W (WCap E Local b e a).
  Proof.
    iIntros "#Hinterp".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    replace (isO E) with false ; auto.
    replace (isSentry E) with true ; auto.
    iDestruct "Hinterp" as "#Hinterp".
    iModIntro.
    rewrite /enter_cond /interp_expr /=.
    iIntros (regs W' Hrelated).
    destruct g.
    - iAssert (future_world Global W W')%I as "%Hrelated'".
      { iPureIntro.
        apply related_sts_pub_priv_trans_world with W', related_sts_priv_refl_world; auto.
      }
      iSpecialize ("Hinterp" $! regs W' Hrelated').
      iDestruct "Hinterp" as "[Hinterp Hinterp_borrowed]".
      iSplitL; iFrame "#".
    - iAssert (future_world Local W W')%I as "%Hrelated'".
      { done. }
      iSpecialize ("Hinterp" $! regs W' Hrelated').
      iDestruct "Hinterp" as "[Hinterp Hinterp_borrowed]".
      iSplitL; iFrame "#".
  Qed.

  Lemma interp_weakeningEO W p p' g g' b b' e e' a a' :
    isSentry p = false ->
    isO p = false →
    isSentry p' = false ->
    isO p' = false →
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W (WCap p g b e a) -∗
    interp W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE HpnotO HpnotE' HpnotO' Hb He Hp Hl. iIntros "HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    rewrite HpnotO HpnotO' HpnotE HpnotE'.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iSplit; cycle 1.
    { case_eq (isWL p'); intros Hpwl'; auto.
      assert (isWL p = true) as Hpwl by (destruct_perm p; destruct_perm p'; naive_solver).
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; try tauto. auto.
    }

    case_eq (isWL p'); intros Hpwl'; auto.
    - assert (isWL p = true) as Hpwl by (destruct_perm p; destruct_perm p'; naive_solver).
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
      iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & #HmonoR & %Hstate)".
      rewrite Hpwl in Hstate.
      assert ( PermFlowsTo p' p'')
        as Hflp' by (eapply PermFlowsToTransitive; eauto).
      iExists p'',φ; iFrame "∗%#".
    - case_eq (isWL p); intros Hpwl; auto; rewrite Hpwl in Hpwl_cond; simplify_eq.
      + destruct g' ; inv Hl.
        destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & #HmonoR & %Hstate)".
        assert ( PermFlowsTo p' p'')
          as Hflp' by (eapply PermFlowsToTransitive; eauto).
        assert (region_state_nwl W x Local)
          as Hstate' by (cbn in * ; naive_solver).
        iExists p'',φ; iFrame "∗%#".
      + destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        rewrite !big_sepL_app; iDestruct "A" as "[_ [A _]]".
        iApply (big_sepL_impl with "A"); auto.
        iModIntro; iIntros (k x Hx) "Hw".
        iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & Hzcond & Hrcond & Hwcond & #HmonoR & %Hstate)".
        assert ( PermFlowsTo p' p'')
          as Hflp' by (eapply PermFlowsToTransitive; eauto).
        assert (region_state_nwl W x g')
          as Hstate' by (destruct g,g'; inv Hl ; cbn in * ; naive_solver).
        iExists p'',φ; iFrame "∗%#".
  Qed.

  Lemma interp_weakeningE W p g g' b b' e e' a a' :
      isSentry p = false ->
      isO p = false ->
      (b <= b')%a ->
      (e' <= e)%a ->
      PermFlowsTo E p ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      interp W (WCap p g b e a) -∗
      interp W (WCap E g' b' e' a').
  Proof.
    intros HpnotE HpnotO Hb He Hp Hl.
    iIntros "#IH HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    rewrite HpnotO HpnotE.
    replace (isO E) with false ; auto.
    replace (isSentry E) with true ; auto.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iModIntro.
    rewrite /enter_cond /interp_expr /=.
    iIntros (r W') "#Hfuture".
    iSplitR; iNext.
    - iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iModIntro. rewrite fixpoint_interp1_eq /=.
      destruct (decide (b' < e'))%a; cycle 1.
      { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
      rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
      rewrite !big_sepL_app. iDestruct "A" as "[_ [A2 _]]".
      iApply (big_sepL_impl with "A2"); auto.
      iModIntro; iIntros (k x Hx) "Hw".
      iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & #Hzcond & #Hrcond & #Hwcond & #HmonoR & %Hstate)".
      assert (Hflows': PermFlowsTo RX p'').
      { eapply PermFlowsTo_trans; eauto.
        destruct p; cbn in HpnotE ; try done.
        destruct dl; cbn in Hp; try done.
        destruct dro; cbn in Hp; try done.
        destruct rx; cbn in Hp; try done.
      }
      iExists p'',φ.
      replace (readAllowed p) with true; cycle 1.
      { destruct_perm p ; cbn in *; try done. }
      iFrame "Hrel".
      iDestruct ( (monoReq_nwl_future W W' g g' p p'' x φ)
                  with "[$Hfuture] [] [$HmonoR]") as "HmonoR'"; eauto.
      repeat(iSplit; auto).
      iApply (region_state_nwl_future with "Hfuture"); eauto.

    - iIntros "[[Hfull Hmap] [Hreg [Hregion [Hsts Hown]]]]".
      rewrite /interp_conf.
      iApply ("IH" with "Hfull Hmap Hreg Hregion Hsts Hown"); eauto.
      iModIntro. rewrite fixpoint_interp1_eq /=.
      destruct (decide (b' < e'))%a; cycle 1.
      { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
      rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
      rewrite !big_sepL_app. iDestruct "A" as "[_ [A2 _]]".
      iApply (big_sepL_impl with "A2"); auto.
      iModIntro; iIntros (k x Hx) "Hw".
      iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & #Hzcond & #Hrcond & #Hwcond & #HmonoR & %Hstate)".
      assert (Hflows': PermFlowsTo RX p'').
      { eapply PermFlowsTo_trans; eauto.
        destruct p; cbn in HpnotE ; try done.
        destruct dl; cbn in Hp; try done.
        destruct dro; cbn in Hp; try done.
        destruct rx; cbn in Hp; try done.
      }
      iExists p'',φ.
      replace (readAllowed p) with true; cycle 1.
      { destruct_perm p ; cbn in *; try done. }
      iFrame "Hrel".

      destruct (isWL p) eqn: Hpwl; cycle 1.
      { assert (if isWL p then g = Local else True) as Hpwl_cond' by (rewrite Hpwl //=).
        assert (
           if isWL p then region_state_pwl W x else region_state_nwl W x g
          ) as Hstate' by (rewrite Hpwl //=).
       iDestruct ( (monoReq_nwl_future W W' g g' p p'' x φ)
                  with "[$Hfuture] [] [$HmonoR]") as "HmonoR'"; eauto.
       repeat(iSplit; auto).
       iDestruct (region_state_nwl_future with "Hfuture") as "Hregion_state" ; eauto.
       iSpecialize ("Hregion_state" $! Hstate').
       destruct g'; cbn; [iLeft|]; done.
      }
      { assert (if isWL p then g = Local else True) as Hpwl_cond' by (rewrite Hpwl //=).
        assert (
           if isWL p then region_state_pwl W x else region_state_nwl W x g
          ) as Hstate' by (rewrite Hpwl //=).
        repeat(iSplit; auto).

        destruct g'; cbn.
        { (* contradiction *)
          destruct g; first congruence; done.
        }
        iDestruct "Hfuture" as "%Hfuture".
        iApply monoReq_mono_pub_pwl; eauto.

        destruct g'; cbn.
        { (* contradiction *)
          destruct g; first congruence; done.
        }
        iDestruct "Hfuture" as "%Hfuture".
        eapply region_state_pwl_monotone in Hstate; eauto.
      }
  Qed.

  Lemma interp_weakening W p p' g g' b b' e e' a a' :
    isSentry p = false ->
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    ftlr_IH -∗
    interp W (WCap p g b e a) -∗
    interp W (WCap p' g' b' e' a').
  Proof.
    intros HpnotE Hb He Hp Hl. iIntros "#IH HA".
    destruct (isO p') eqn:HpO'.
    { rewrite !fixpoint_interp1_eq !interp1_eq HpO'; auto. }
    destruct (isO p) eqn:HpO.
    { eapply notisO_flowsfrom in Hp ; eauto; congruence. }
    destruct (isSentry p') eqn:Hsentryp'; cycle 1.
    { iApply (interp_weakeningEO _ p p' g g'); eauto. }
    { destruct p, p' ; cbn in * ; try congruence.
      iApply (interp_weakeningE _ (BPerm rx w dl dro) g g'); eauto.
    }
  Qed.

  Lemma interp_next_PC W p g b e a a' :
    isCorrectPC (WCap p g b e a) ->
    interp W (WCap p g b e a) -∗
    interp W (WCap p g b e a').
  Proof.
    iIntros (HcorrectPC) "#Hinterp".
    inversion HcorrectPC as [p' g' b' e' a'' Hb' Hexec']; subst.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    assert (isSentry p = false) by (by eapply executeAllowed_nonSentry).
    iApply interp_weakeningEO; eauto; try solve_addr; try done.
  Qed.

  Lemma safe_to_unseal_weakening b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal interp b e -∗
    safe_to_unseal interp b' e'.
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
    safe_to_seal interp b e -∗
    safe_to_seal interp b' e'.
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
    interp W (WSealRange p g b e a) -∗
    interp W (WSealRange p' g' b' e' a').
  Proof.
  intros Hb He Hp Hg. iIntros "#HA".
  rewrite !fixpoint_interp1_eq. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Qed.

  Lemma interp_borrowed_sealed (W : WORLD) (ot : OType) (sb : Sealable) :
    interp W (WSealed ot sb) -∗ interp W (WSealed ot (borrow_sb sb)).
  Proof.
    iIntros "Hinterp".
    rewrite !fixpoint_interp1_eq /= /interp_sb.
    iDestruct "Hinterp" as (P HpersP) "(Hsealpred & _ & HPborrowed)".
    iDestruct "HPborrowed" as "#HPborrowed".
    replace (borrow (WSealable (borrow_sb sb)))
      with (WSealable (borrow_sb sb)).
    iFrame "∗#%".
    cbn.
    destruct sb; auto.
    destruct p; auto.
  Qed.

  Lemma interp_load_word W p w : interp W w ⊢ interp W (load_word p w).
  Proof.
    iIntros "Hinterp".
    destruct w.
    - by rewrite load_word_int.
    - destruct sb; try done; cbn; cycle 1.
      { rewrite load_word_sealrange.
        by rewrite !fixpoint_interp1_eq.
      }
      {
        destruct p0; [ rewrite load_word_cap | rewrite load_word_E ];cycle 1.
        { destruct (isDL p); last done.
          by iApply interp_weakening_from_E.
        }
        rewrite !fixpoint_interp1_eq !interp1_eq.

        destruct (isO (BPerm rx w dl dro)) eqn:HpO.
        { destruct rx,w; cbn in *; try done.
          by rewrite Tauto.if_same.
        }
        set (w' := (if isDRO p then Ow else w)).
        set (dl' := (if isDL p then DL else dl)).
        set (dro' := (if isDRO p then DRO else dro)).
        destruct (isO (load_word_perm p (BPerm rx w dl dro))); first done.
        replace (isSentry (BPerm rx w dl dro)) with false; auto.
        replace (isSentry (load_word_perm p (BPerm rx w dl dro))) with false; auto.

        iDestruct "Hinterp" as "[Hinterp %Hw]".
        iSplit; cycle 1.
        iPureIntro.
        {
          rewrite /load_word_perm.
          destruct (isDRO p); subst w'; cbn; try done.
          destruct w; try done.
          cbn in Hw.
          subst; by rewrite Tauto.if_same.
        }
        iApply (big_sepL_mono with "Hinterp").
        iIntros (k y Hky) "Ha".
        iDestruct "Ha" as
          (p' P' Hflp' HpersP')
            "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)".
        iExists p',P'.
        iFrame "∗".
        iSplit;[iPureIntro|].
        {
          transitivity (BPerm rx w dl dro); auto.
          apply load_word_perm_flows.
        }
        iSplit;[iFrame "%"|].
        iPureIntro.
        destruct (isWL (BPerm rx w dl dro)) eqn:Hpwl ; simplify_eq.
        { rewrite /load_word_perm.
          cbn in Hpwl; destruct w ; try congruence.
          destruct (isDRO p); subst w'; cbn; auto.
          rewrite Tauto.if_same; cbn.
          by right.
        }
        { assert (isWL (load_word_perm p (BPerm rx w dl dro)) = false) as ->.
          { cbn in *.
            subst w'.
            destruct (isDRO p); done.
          }
          destruct (isDL p); cbn; auto.
          destruct g; cbn in Hstate; naive_solver.
        }
      }
    - rewrite load_word_sealed.
      destruct (isDL p); auto.
      by iApply (interp_borrowed_sealed with "Hinterp").
  Qed.

  Lemma interp_borrow_word W w : interp W w ⊢ interp W (borrow w).
  Proof.
    iIntros "Hw".
    iDestruct (interp_load_word W RO_DL w with "Hw") as "Hw'".
    by cbn.
  Qed.

  Lemma interp_readonly_word W w : interp W w ⊢ interp W (readonly w).
  Proof.
    iIntros "Hw".
    iDestruct (interp_load_word W RO_DRO w with "Hw") as "Hw'".
    by cbn.
  Qed.

  Lemma interp_weakening_word_load (W : WORLD) (p p' : Perm) v :
    PermFlowsTo p p'
    -> fixpoint interp1 W (load_word p' v)
    -∗ fixpoint interp1 W (load_word p v).
  Proof.
    iIntros (Hfl) "#Hinterp".
    destruct v.
    - rewrite !load_word_int; done.
    - destruct sb; cycle 1.
      { rewrite !load_word_sealrange; cbn.
        by rewrite !fixpoint_interp1_eq /=.
      }
      destruct p0 as [ rx0 w0 dl0 dro0|]; cycle 1.
      { rewrite !load_word_E.
        destruct (isDL p') eqn:Hdl
        ; [ eapply isDL_flowsto in Hfl; eauto ; rewrite Hfl |]
        ; auto.
        destruct (isDL p); auto.
        by iApply interp_weakening_from_E.
      }
      rewrite !load_word_cap.
      destruct (isO (load_word_perm p (BPerm rx0 w0 dl0 dro0))) eqn:HnO.
      { rewrite !fixpoint_interp1_eq !interp1_eq.
        by rewrite HnO.
      }
      destruct (isSentry (BPerm rx0 w0 dl0 dro0)) eqn:Hnsentry.
      { cbn in Hnsentry ; congruence . }
      iApply (interp_weakeningEO with "Hinterp"); auto; try solve_addr.
      + eapply isO_flowsto ; eauto.
        apply load_word_perm_load_flows;auto.
      + apply load_word_perm_load_flows;auto.
      + destruct (isDL p) eqn:Hdl; auto.
        eapply notisDL_flowsfrom in Hfl; eauto.
        by rewrite Hfl.
    - rewrite !load_word_sealed.
      destruct (isDL p') eqn:Hdl'; cbn.
      + pose proof (isDL_flowsto p p' Hfl Hdl') as Hdl; rewrite Hdl.
        done.
      + iDestruct (interp_borrowed_sealed with "Hinterp") as "Hinterp'".
        destruct (isDL p); auto.
  Qed.

  (* Lemmas about interp  *)

  Lemma interp_int W n : ⊢ interp W (WInt n).
  Proof. iIntros. rewrite /interp fixpoint_interp1_eq //. Qed.

  Lemma persistent_cond_interp : persistent_cond interp.
  Proof.
    intros W; apply _.
  Qed.
  Lemma zcond_interp : ⊢ zcond interp.
  Proof.
    by iModIntro; iIntros (W1 W2 w) "_"; iApply interp_int.
  Qed.

  Lemma wcond_interp : ⊢ wcond interp interp.
  Proof.
    by iModIntro; iIntros (W1 w) "?".
  Qed.

  Lemma rcond_interp p : ⊢ rcond p interp interp.
  Proof.
    iModIntro; iIntros (W1 w) "?".
    by iApply interp_load_word.
  Qed.

End fundamental.
