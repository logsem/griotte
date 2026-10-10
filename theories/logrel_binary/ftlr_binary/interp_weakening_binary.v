From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import memory_region monotone_binary.
From griotte Require Export logrel_binary ftlr_base_binary.

(** Weakening lemmas for the binary [interp]. *)
Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Lemma enter_cond_weakening W C p b e a :
    (□ enter_cond W C p Global b e a (fixpoint interp1)) -∗
     □ enter_cond W C p Local b e a (fixpoint interp1).
  Proof.
    iIntros "#Hinterp".
    rewrite /enter_cond /interp_expr /=.
    iIntros (W' Hrelated).
    iAssert (future_world Global W W')%I as "%Hrelated'".
    { iPureIntro.
      apply related_sts_pub_priv_trans_world with W', related_sts_priv_refl_world; auto.
    }
    iIntros "!> %g' %Hflows".
    assert (  LocalityFlowsTo g' Global ) as Hflow'.
    { destruct g'; auto. }
    iSpecialize ("Hinterp" $! W' Hrelated' g' Hflow').
    iFrame "#".
  Qed.

  Lemma interp_weakening_from_sentry W C p g b e a :
      interp W C (WSentry p g b e a, WSentry p g b e a)
      -∗ interp W C (WSentry p Local b e a, WSentry p Local b e a).
  Proof.
    iIntros "#Hinterp".
    rewrite !interp_diag_eq // /interp1_diag /=.
    destruct g; auto.
    iApply enter_cond_weakening;auto.
  Qed.

  Lemma interp_weakeningEO W C p p' g g' b b' e e' a a' :
    isO p = false →
    isO p' = false →
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WCap p g b e a, WCap p g b e a) -∗
    interp W C (WCap p' g' b' e' a', WCap p' g' b' e' a').
  Proof.
    intros HpnotO HpnotO' Hb He Hp Hl. iIntros "HA".
    rewrite !fixpoint_interp1_eq !interp1_eq.
    rewrite HpnotO HpnotO'.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    replace (has_sreg_access p')
      with false by (symmetry; eapply nothas_sreg_access_flowsfrom; eauto).
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iSplit; cycle 1.
    { case_eq (isWL p'); intros Hpwl'; auto.
      pose proof (isWL_flowsto p' p Hp Hpwl') as Hpwl.
      rewrite Hpwl in Hpwl_cond.
      destruct g; try congruence.
      destruct g'; simpl in Hl; try tauto. auto.
    }

    case_eq (isWL p'); intros Hpwl'; auto.
    - pose proof (isWL_flowsto p' p Hp Hpwl') as Hpwl.
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

  Lemma interp_weakening W C p p' g g' b b' e e' a a' :
    (b <= b')%a ->
    (e' <= e)%a ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    ftlr_IH -∗
    interp W C (WCap p g b e a, WCap p g b e a) -∗
    interp W C (WCap p' g' b' e' a', WCap p' g' b' e' a').
  Proof.
    intros Hb He Hp Hl. iIntros "#IH HA".
    destruct (isO p') eqn:HpO'.
    { rewrite !fixpoint_interp1_eq !interp1_eq HpO'; auto. }
    destruct (isO p) eqn:HpO.
    { eapply notisO_flowsfrom in Hp ; eauto; congruence. }
    { iApply (interp_weakeningEO _ _ p p' g g'); eauto. }
  Qed.

  Lemma interp_weakeningSentry W C p g g' b b' e e' a a' :
      isO p = false ->
      (b <= b')%a ->
      (e' <= e)%a ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      interp W C (WCap p g b e a, WCap p g b e a) -∗
      interp W C (WSentry p g' b' e' a', WSentry p g' b' e' a').
  Proof.
    intros HpnotO Hb He Hl.
    iIntros "#IH HA".
    rewrite !fixpoint_interp1_eq !interp1_eq /=.
    rewrite HpnotO.
    destruct (has_sreg_access p) eqn:HpXSR; auto.
    iDestruct "HA" as "[#A %Hpwl_cond]".
    iSplit; first done.
    iModIntro.
    rewrite /enter_cond /interp_expr /=.
    iIntros (W') "#Hfuture %g'' %Hflows !>".
    iIntros (stk Ws Cs regs1 regs2)
      "(#Hspec & #Hreg & Hmap & Hsmap & Hj & Hworld_interp & Hcont & Hown & Hcstk & Hcstk_spec & %Hframe)".
    rewrite /interp_conf.
    iApply ("IH" with "Hspec Hreg Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Hcstk Hcstk_spec"); eauto.
    iModIntro. rewrite fixpoint_interp1_eq interp1_eq.
    destruct (isO p) eqn:HpO; auto.
    destruct (has_sreg_access p) eqn:HpXSR'; auto.
    iSplit; cycle 1.
    {
      destruct (isWL p) eqn:Hpwl; auto.
      simplify_eq.
      destruct g',g'' ; auto.
    }
    destruct (decide (b' < e'))%a; cycle 1.
    { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
    rewrite (isWithin_finz_seq_between_decomposition b' e' b e); try solve_addr.
    rewrite !big_sepL_app. iDestruct "A" as "[_ [A2 _]]".
    iApply (big_sepL_impl with "A2"); auto.
    iModIntro; iIntros (k x Hx) "Hw".
    iDestruct "Hw" as (p'' φ Hflp'' Hpersφ) "(Hrel & #Hzcond & #Hrcond & #Hwcond & #HmonoR & %Hstate)".
    iExists p'',φ.
    iFrame "Hrel".
    iDestruct ( (monoReq_nwl_future W W' C g g' p p'' x φ)
                with "[$Hfuture] [] [$HmonoR]") as "HmonoR'"; eauto.
    repeat(iSplit; auto).
    destruct g''.
    - destruct g';cbn in Hflows; last done.
      destruct g;cbn in Hl; last done.
      iDestruct "Hfuture" as "%Hfuture".
      destruct (isWL p); first done.
      iPureIntro; eapply region_state_nwl_monotone_nl; eauto.
    - destruct (isWL p); simplify_eq.
      + destruct g';cbn in Hflows; first done.
        iDestruct "Hfuture" as "%Hfuture".
        iPureIntro; eapply region_state_pwl_monotone; eauto.
      + destruct g'.
        * destruct g;cbn in Hl; last done.
          iDestruct "Hfuture" as "%Hfuture".
          eapply region_state_nwl_monotone_nl in Hstate; eauto.
          iPureIntro; by left.
        * iDestruct "Hfuture" as "%Hfuture".
          iPureIntro; eapply region_state_nwl_monotone; eauto.
          destruct g; last done.
          by left.
  Qed.

  Lemma interp_next_PC W C p g b e a a' :
    isCorrectPC (WCap p g b e a) ->
    interp W C (WCap p g b e a, WCap p g b e a) -∗
    interp W C (WCap p g b e a', WCap p g b e a').
  Proof.
    iIntros (HcorrectPC) "#Hinterp".
    inversion HcorrectPC as [p' g' b' e' a'' Hb' Hexec']; subst.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iApply interp_weakeningEO; eauto; try solve_addr; try done.
  Qed.

  Lemma interp_lea W C p g b e a a' :
    isO p = false ->
    interp W C (WCap p g b e a, WCap p g b e a) -∗
    interp W C (WCap p g b e a', WCap p g b e a').
  Proof.
    iIntros (Hisno) "#Hi".
    iApply interp_weakeningEO; eauto; try solve_addr; try done.
  Qed.

  Lemma safe_to_unseal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_unseal W C interp b e -∗
    safe_to_unseal W C interp b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_unseal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma safe_to_seal_weakening W C b e b' e':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    safe_to_seal W C interp b e -∗
    safe_to_seal W C interp b' e'.
  Proof.
    iIntros (Hb He) "HA".
    rewrite /safe_to_seal.
    destruct (decide (b' <= e')%ot).
    - rewrite /= (isWithin_finz_seq_between_decomposition b' e' b e); [|solve_addr].
      rewrite !big_sepL_app; iDestruct "HA" as "[_ [$ _]]".
    - iClear "HA"; rewrite !finz_seq_between_empty;[done |solve_addr].
  Qed.

  Lemma interp_weakening_ot W C p p' g g' b b' e e' a a':
    (b <= b')%ot ->
    (e' <= e)%ot ->
    SealPermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    interp W C (WSealRange p g b e a, WSealRange p g b e a) -∗
    interp W C (WSealRange p' g' b' e' a', WSealRange p' g' b' e' a').
  Proof.
  intros Hb He Hp Hg. iIntros "#HA".
  rewrite !interp_diag_eq // /interp1_diag. cbn.
  destruct (permit_seal p') eqn:Hseal; [eapply (permit_seal_flowsto _ p) in Hseal as ->; auto | ].
  all: destruct (permit_unseal p') eqn:Hunseal; [eapply (permit_unseal_flowsto _ p) in Hunseal as ->; auto | ]; iDestruct "HA" as "[Hs Hus]".
  all: iSplitL "Hs";
  [try iApply (safe_to_seal_weakening with "Hs") | try iApply (safe_to_unseal_weakening with "Hus")]; auto.
  Unshelve. all: exact W.
  Qed.

  Lemma interp_borrowed_sealed (W : WORLD) (C : CmptName) (ot1 ot2 : OType) (sb1 sb2 : Sealable) :
    interp W C (WSealed ot1 sb1, WSealed ot2 sb2) -∗
    interp W C (WSealed ot1 (borrow_sb sb1), WSealed ot2 (borrow_sb sb2)).
  Proof.
    iIntros "Hinterp".
    rewrite !interp_sealed_inv /interp_sb.
    iDestruct "Hinterp" as "[%Heq (%P & %HpersP & Hmono & Hsealpred & %Hloc & _ & HPborrowed)]".
    opose proof (HpersP (W,C,_)) as HpersPborrowed; cbn in HpersPborrowed.
    iDestruct "HPborrowed" as "#HPborrowed".
    replace (borrow (WSealable (borrow_sb sb1))) with (WSealable (borrow_sb sb1))
    by (destruct sb1; auto).
    replace (borrow (WSealable (borrow_sb sb2))) with (WSealable (borrow_sb sb2))
    by (destruct sb2; auto).
    iSplit; first done.
    iExists P.
    iFrame "∗#%".
    iPureIntro.
    by destruct sb1, sb2.
  Qed.

  Lemma interp_deeplocal_word W C (ww : Word * Word) :
    interp W C ww ⊢ interp W C (deeplocal ww.1, deeplocal ww.2).
  Proof.
    iIntros "#Hw".
    destruct ww as [w w2]; cbn.
    iDestruct (interp_eq_unless_sealed with "Hw") as "[<-|(%o & %sb1 & %sb2 & -> & ->)]"
    ; last done.
    destruct w; try done.
    destruct sb; try done; cbn; cycle 1.
    destruct p;try done; cbn; cycle 1.
    destruct (isO (BPerm rx w dl dro)) eqn:HpO.
    { destruct rx,w; cbn in *; try done.
      rewrite !fixpoint_interp1_eq //=.
    }
    iApply interp_weakeningEO; eauto; try done; try solve_addr.
    apply DL_flowsto.
  Qed.

  Lemma interp_borrow_word W C (ww : Word * Word) :
    interp W C ww ⊢ interp W C (borrow ww.1, borrow ww.2).
  Proof.
    iIntros "#Hw".
    destruct ww as [w w2]; cbn.
    iDestruct (interp_eq_unless_sealed with "Hw") as "[<-|(%o & %sb1 & %sb2 & -> & ->)]".
    2: by iApply (interp_borrowed_sealed with "Hw").
    destruct w; try done.
    - destruct sb; try done; cbn; cycle 1.
      { by rewrite !interp_diag_eq // /interp1_diag /=. }
      {
        destruct p.
        destruct (isO (BPerm rx w dl dro)) eqn:HpO.
        { destruct rx,w; cbn in *; try done.
          rewrite !fixpoint_interp1_eq //=.
        }
        iApply interp_weakeningEO; eauto; try done; try solve_addr.
      }
    - by iApply interp_weakening_from_sentry.
    - by iApply (interp_borrowed_sealed with "Hw").
  Qed.

  Lemma interp_readonly_word W C (ww : Word * Word) :
    interp W C ww ⊢ interp W C (readonly ww.1, readonly ww.2).
  Proof.
    iIntros "#Hw".
    destruct ww as [w w2]; cbn.
    iDestruct (interp_eq_unless_sealed with "Hw") as "[<-|(%o & %sb1 & %sb2 & -> & ->)]"
    ; last done.
    destruct w; try done.
    destruct sb; try done; cbn; cycle 1.
    destruct p;try done; cbn; cycle 1.
    destruct (isO (BPerm rx w dl dro)) eqn:HpO.
    { destruct rx,w; cbn in *; try done.
      rewrite !fixpoint_interp1_eq //=.
    }
    destruct (isO (BPerm rx Ow dl DRO)) eqn:HpO'.
    { destruct rx,w; cbn in *; try done.
      all: rewrite !fixpoint_interp1_eq //=.
    }
    iApply (interp_weakeningEO with "Hw"); eauto; try done; try solve_addr.
    apply DRO_flowsto.
  Qed.

  Lemma interp_load_word W C p (ww : Word * Word) :
    interp W C ww ⊢ interp W C (load_word p ww.1, load_word p ww.2).
  Proof.
    iIntros "Hinterp".
    destruct ww as [w1 w2]; cbn.
    rewrite /load_word.
    destruct (isDRO p),(isDL p); auto.
    - iApply (interp_readonly_word _ _ (_,_)).
      iApply (interp_deeplocal_word _ _ (_,_)).
      by iApply (interp_borrow_word _ _ (_,_)).
    - by iApply (interp_readonly_word _ _ (_,_)).
    - iApply (interp_deeplocal_word _ _ (_,_)).
      by iApply (interp_borrow_word _ _ (_,_)).
  Qed.

  Lemma interp_weakening_word_load (W : WORLD) (C : CmptName) (p p' : Perm) (v : Word * Word) :
    PermFlowsTo p p'
    -> fixpoint interp1 W C (load_word p' v.1, load_word p' v.2)
    -∗ fixpoint interp1 W C (load_word p v.1, load_word p v.2).
  Proof.
    iIntros (Hfl) "#Hinterp".
    iDestruct (interp_load_word _ _ p with "Hinterp") as "Hinterp'".
    by rewrite /= !load_word_load_word.
  Qed.

  (* Lemmas about interp  *)

  Lemma persistent_cond_interp : persistent_cond interp.
  Proof.
    intros W; apply _.
  Qed.

  Lemma zcond_interp C : ⊢ zcond interp C.
  Proof.
    iModIntro; iIntros (W1 W2 z1 z2) "Hz".
    iDestruct (interp_int_inv with "Hz") as "%Heq"; simplify_eq.
    iApply interp_int.
  Qed.

  Lemma wcond_interp C : ⊢ wcond interp C interp.
  Proof. by iModIntro; iIntros (W1 w) "?". Qed.

  Lemma rcond_interp C p : ⊢ rcond interp C p interp.
  Proof. iModIntro; iIntros (W1 w) "?"; by iApply interp_load_word. Qed.

  Lemma monoReq_interp (W : WORLD) (C : CmptName) (a : Addr) (p : Perm) (ρ : region_type) :
    (std W) !! a = Some ρ
    -> (ρ = Permanent -> isWL p = false)
    -> ⊢ monoReq W C a p interp.
  Proof.
    intros Hstd_a Hρ.
    rewrite /monoReq Hstd_a.
    destruct ρ; try done.
    - destruct (isWL p) eqn:Hwl.
      + iIntros (w W0 W1 Hrelated); iModIntro.
        iIntros "Hinterp".
        iApply interp_monotone; eauto.
      + destruct (isDL p) eqn:Hdl.
        * iIntros (w W0 W1 Hrelated); iModIntro.
          iIntros "Hinterp".
          iApply interp_monotone; eauto.
        * iIntros (w [HcanStore _] W0 W1 Hrelated); iModIntro.
          iIntros "Hinterp".
          iApply interp_monotone_nl; eauto.
          iPureIntro; cbn.
          by eapply canStore_global_nonisWL.
    - ospecialize (Hρ _); first done.
      iIntros (w [HcanStore _] W0 W1 Hrelated); iModIntro.
      iIntros "Hinterp".
      iApply interp_monotone_nl; eauto.
      iPureIntro; cbn.
      by eapply canStore_global_nonisWL.
  Qed.

  Lemma future_priv_mono_interp_z (C : CmptName) (z1 z2 : Z) :
    ⊢ future_priv_mono C interpC (WInt z1, WInt z2).
  Proof.
    iModIntro.
    iIntros (W W') "%Hrelated Hinterp".
    rewrite /=.
    iDestruct (interp_int_inv with "Hinterp") as "%Heq"; simplify_eq.
    iApply interp_int.
  Qed.

  Lemma future_pub_mono_interp_z (C : CmptName) (z1 z2 : Z) :
    ⊢ future_pub_mono C interpC (WInt z1, WInt z2).
  Proof.
    iModIntro.
    iIntros (W W') "%Hrelated Hinterp".
    rewrite /=.
    iDestruct (interp_int_inv with "Hinterp") as "%Heq"; simplify_eq.
    iApply interp_int.
  Qed.

  Lemma future_priv_mono_interp_global (C : CmptName) (p : Perm) (b e a : Addr) :
    ⊢ future_priv_mono C interpC (WCap p Global b e a, WCap p Global b e a).
  Proof.
    iModIntro.
    iIntros (W W') "%Hrelated Hinterp".
    rewrite /=.
    iApply interp_monotone_nl_cap; eauto.
  Qed.

  (* interp_dl *)
  Program Definition interp_dl : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO (Word * Word))
     , (interp W B (deeplocal (borrow v.1), deeplocal (borrow v.2)))%I).
  Solve All Obligations with solve_proper.

  Lemma future_pub_mono_interp_dl C w:
    ⊢ future_pub_mono C (safeC interp_dl) w.
  Proof.
    iIntros "!>" (W W' Hrelated) "H"; cbn.
    iApply interp_monotone; eauto.
  Qed.

  Lemma persistent_cond_interp_dl : persistent_cond interp_dl.
  Proof. intros W; apply _. Qed.

  Lemma interp_dl_int W C n : ⊢ interp_dl W C (WInt n, WInt n).
  Proof. iIntros; cbn; iApply interp_int. Qed.

  Lemma zcond_interp_dl C : ⊢ zcond interp_dl C.
  Proof.
    iModIntro; iIntros (W1 W2 z1 z2) "Hz"; cbn.
    iDestruct (interp_int_inv with "Hz") as "%Heq"; simplify_eq.
    iApply interp_int.
  Qed.

  Lemma wcond_interp_dl C : ⊢ wcond interp_dl C interp.
  Proof.
    iIntros "!> %W %w H"; destruct w as [w1 w2]; cbn.
    iApply (interp_deeplocal_word _ _ (_,_)).
    by iApply (interp_borrow_word _ _ (_,_)).
  Qed.

  Lemma rcond_interp_dl C p : isDL p = true -> ⊢ rcond interp_dl C p interp.
  Proof.
    iIntros (Hp) "!> %W %w H".
    rewrite /load_word /= Hp.
    destruct (isDRO p); last done.
    by iApply (interp_readonly_word _ _ (_,_)).
  Qed.

  Lemma mono_pub_interp_dl C : ⊢ mono_pub C (safeC interp_dl).
  Proof. iIntros (?) "!> %W %W' %Hrelated H"; cbn. iApply interp_monotone; auto. Qed.

  Program Definition interp_dro_eq (w : Word * Word) : V :=
    (λne (W : WORLD) (B : leibnizO CmptName) (v : leibnizO (Word * Word))
     , (⌜ v = w ⌝ ∗ interp W B (readonly w.1, readonly w.2))%I).
  Solve All Obligations with solve_proper.

  Lemma persistent_cond_interp_dro_eq (w : Word * Word) : persistent_cond (interp_dro_eq w).
  Proof. intros W; apply _. Qed.

  Lemma zcond_interp_dro_eq C w : ⊢ zcond (interp_dro_eq w) C.
  Proof.
    iModIntro; iIntros (W1 W2 z1 z2) "[<- H]"; cbn.
    iSplit; first done.
    iDestruct (interp_int_inv with "H") as "%Heq"; simplify_eq.
    iApply interp_int.
  Qed.

  Lemma rcond_interp_dro_eq C w p : isDRO p = true -> ⊢ rcond (interp_dro_eq w) C p interp.
  Proof.
    iIntros (Hp) "!> %W %w' [<- H]".
    rewrite /load_word /= Hp.
    destruct (isDL p); last done.
    replace (readonly (deeplocal (borrow w'.1))) with (deeplocal (borrow (readonly w'.1))).
    2: { destruct w'.1 as [| [ [] |] | |]; auto. }
    replace (readonly (deeplocal (borrow w'.2))) with (deeplocal (borrow (readonly w'.2))).
    2: { destruct w'.2 as [| [ [] |] | |]; auto. }
    iApply (interp_deeplocal_word _ _ (_,_)).
    by iApply (interp_borrow_word _ _ (_,_)).
  Qed.

End fundamental.
