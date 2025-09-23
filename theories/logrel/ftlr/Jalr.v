From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import rules_base rules_Jalr.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma jalr_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rdst rsrc : RegName) (P:V)  (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word) (Nswitcher : namespace):
    ftlr_instr W C regs p p' g b e a w (Jalr rdst rsrc) ρ P cstk Ws Cs wstk Nswitcher.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hcont %Hframe Hsts Hown Hcstk".
    iIntros "Hr Hstate Ha HPC Hmap %Hwstk #Hinv_switcher".
    iInsert "Hmap" PC.
    iApply (wp_Jalr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' pc_a' wsrc Hrsrc Hpca' ->| Hpca' ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }

    iAssert (interp W C (WSentry p g b e pc_a')) as "Hinterp_ret".
    {
      iApply (interp_weakeningSentry with "IH Hinv_interp");eauto;try solve_addr.
      - destruct Hp as [Hexec _].
        by apply executeAllowed_nonO.
      - reflexivity.
    }

    iApply wp_pure_step_later; auto.

    destruct (decide (rdst = PC)) as [HPC_dst|HPC_dst]; simplify_eq.
    { iNext; iIntros "_".
      iApply (wp_bind (fill [SeqCtx])).
      iExtract "Hmap" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
      iNext; iIntros "HPC /=".
      iApply wp_pure_step_later; auto; iNext; iIntros "_".
      iApply wp_value; iIntros; discriminate.
    }

    destruct (updatePcPerm wsrc) eqn:Hwsrc ; [ | destruct sb | | ]; cycle 1.
    { destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; auto.
      }


      destruct_word wsrc; cbn in Hwsrc; try discriminate.
      { destruct c; inv Hwsrc.
        iNext ; iIntros "_".
        iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
        { destruct ρ;auto;contradiction. }
        rewrite !insert_insert insert_commute //.
        iApply ("IH" $! _ _ _ _ _ (<[rdst:=WSentry p g b e pc_a']> regs) with
                 "[%] [] [$Hmap] [%] [$Hr] [$Hsts] [$Hcont] [//] [$Hown] [$]") ; eauto.
        - intros; cbn.
          rewrite lookup_insert_is_Some.
          destruct (decide (rdst = x)); auto; right; split; auto.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = rdst)); simplify_map_eq; cycle 1.
          * iApply ("Hreg" $! ri) ; auto.
          * iFrame "Hinterp_ret".
        - Unshelve.
          2: exact (if (decide (rdst = csp)) then WSentry p g b e pc_a' else wstk).
          destruct (decide (rdst = csp)); simplify_map_eq; eauto.
        - destruct (decide (rsrc = PC)) as [HrsrcPC|HrsrcPC].
          + simplify_map_eq; auto.
          + simplify_map_eq.
            iDestruct ("Hreg" $! rsrc _ HrsrcPC Hrsrc) as "Hrsrc"; eauto.
      }
      assert (rsrc <> PC) as HPCnrsrc.
      { intro; subst rsrc; simplify_map_eq. }
      simplify_map_eq.
      iDestruct ("Hreg" $! rsrc _ HPCnrsrc Hrsrc) as "Hwsrc".
      iEval (rewrite fixpoint_interp1_eq) in "Hwsrc".
      simpl; rewrite /enter_cond.
      iDestruct "Hwsrc" as "#Hinterp_src".
      iAssert (future_world g0 W W) as "Hfuture".
      { iApply futureworld_refl. }
        iSpecialize ("Hinterp_src" with "Hfuture").
        iDestruct "Hinterp_src" as "[Hinterp_src _]".
        iDestruct (region_close with "[$Hstate $Hr Hw $Ha $HmonoV]") as "Hr"; eauto.
        { destruct ρ;auto;contradiction. }
        rewrite !insert_insert insert_commute //.
        iDestruct ("Hinterp_src" with "[$Hmap $Hr $Hsts $Hcstk $Hown $Hcont]") as "HA"; eauto.
        iNext.
        repeat (cbn; iSplit; auto).
        + iIntros (ri); cbn; iPureIntro.
          rewrite lookup_insert_is_Some.
          destruct (decide (rdst = ri)); auto; right; split; auto.
        + iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = rdst)); simplify_map_eq; cycle 1.
          * iApply ("Hreg" $! ri) ; auto.
          * iFrame "Hinterp_ret".
        + Unshelve.
          2: exact (if (decide (rdst = csp)) then WSentry p g b e pc_a' else wstk).
          destruct (decide (rdst = csp)); simplify_map_eq; eauto.
    }

    (* Non-capability cases *)
    all: iExtract "Hmap" PC as "HPC".
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iApply wp_value; auto.
  Qed.

End fundamental.
