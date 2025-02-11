From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Jalr.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ} {sealsg: sealStoreG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Lemma jalr_case (W : WORLD) (regs : leibnizO Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rdst : RegName) (P:D):
    ftlr_instr W regs p p' g b e a w (Jalr rdst) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.
    iApply (wp_Jalr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' pc_a' wdst Hrdst Hpca' ->| Hpca' ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    }

    rewrite (insert_commute _ cra PC) // insert_insert.
    iApply wp_pure_step_later; auto.

    iAssert (interp W (WCap (seal_perm_sentry p) g b e pc_a')) as "Hinterp_ret".
    { pose proof (isCorrectPC_nonSentry p _ _ _ _ HcorrectPC ) as HpnotSentry.
      iApply (interp_weakening with "IH Hinv_interp");eauto;try solve_addr.
      - rewrite /seal_perm_sentry; destruct p ; cbn in HpnotSentry; try congruence.
        repeat (apply andb_True;split; try reflexivity).
        destruct Hp as [Hexec _].
        destruct rx; cbn in Hexec ; try congruence;done.
      - reflexivity.
    }

    destruct (updatePcPerm wdst) eqn:Hwdst ; [ | destruct sb | ]; cycle 1.
    { destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; iIntros; discriminate.
      }


      destruct_word wdst; cbn in Hwdst; try discriminate.
      destruct c; inv Hwdst.
      { iNext ; iIntros "_".
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
        iApply ("IH" $! _ (<[cra:=WCap (seal_perm_sentry p) g b e pc_a']> regs) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]") ; eauto.
        - intros; cbn.
          rewrite lookup_insert_is_Some.
          destruct (decide (cra = x)); auto; right; split; auto.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = cra)); simplify_map_eq; cycle 1.
          * iApply ("Hreg" $! ri) ; auto.
          * iFrame "Hinterp_ret".
        - destruct (decide (rdst = PC)) as [HrdstPC|HrdstPC].
          + simplify_map_eq; auto.
          + simplify_map_eq.
            iDestruct ("Hreg" $! rdst _ HrdstPC Hrdst) as "Hrdst"; eauto.
      }
      { assert (rdst <> PC) as HPCnrdst.
        { intro; subst rdst; simplify_map_eq.
          destruct Hp as [Hexec _]
          ; eapply executeAllowed_nonSentry in Hexec
          ; eauto ; cbn in Hexec
          ; naive_solver.
        }
        simplify_map_eq.
        iDestruct ("Hreg" $! rdst _ HPCnrdst Hrdst) as "Hwdst".
        iEval (rewrite fixpoint_interp1_eq) in "Hwdst".
        simpl; rewrite /enter_cond.
        iDestruct "Hwdst" as "#Hinterp_dst".
        iAssert (future_world g0 W W) as "Hfuture".
        { iApply futureworld_refl. }

        iSpecialize ("Hinterp_dst" with "Hfuture").
        iDestruct "Hinterp_dst" as "[Hinterp_dst _]".
        iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
        { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
        iDestruct ("Hinterp_dst" with "[$Hmap $Hr $Hsts $Hown]") as "HA"; eauto.
        iNext.
        cbn; iSplit.
        - iIntros (ri); cbn; iPureIntro.
          rewrite lookup_insert_is_Some.
          destruct (decide (cra = ri)); auto; right; split; auto.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = cra)); simplify_map_eq; cycle 1.
          * iApply ("Hreg" $! ri) ; auto.
          * iFrame "Hinterp_ret".
      }
    }

    (* Non-capability cases *)
    all: iExtract "Hmap" PC as "HPC".
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iApply wp_value; iIntros; discriminate.
  Qed.

End fundamental.
