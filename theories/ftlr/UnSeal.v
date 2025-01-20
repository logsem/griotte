From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_UnSeal.
From cap_machine.proofmode Require Import map_simpl.

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

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result. *)
  Lemma unsealing_preserves_interp W sb p0 g0 b0 e0 a0:
        permit_unseal p0 = true →
        withinBounds b0 e0 a0 = true →
        fixpoint interp1 W (WSealed a0 sb) -∗
        fixpoint interp1 W (WSealRange p0 g0 b0 e0 a0) -∗
        ▷ fixpoint interp1 W (WSealable sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsd #HVsr".
    rewrite
      (fixpoint_interp1_eq W (WSealRange _ _ _ _ _))
      (fixpoint_interp1_eq W (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[_ Hss]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[HsealP [ HWcond _  ]]".
    iDestruct "HVsd" as (P') "[% [HsealP' HP']]".
    iDestruct (seal_pred_agree with "HsealP HsealP'") as "Hequiv".
    Unshelve. 2: exact W.
    iSpecialize ("Hequiv" $! (WSealable sb)).
    iAssert (▷ P W (WSealable sb))%I as "HP". { iNext; by iRewrite "Hequiv". }
    by iApply "HWcond".
  Qed.

  Lemma unseal_case (W : WORLD) (regs : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:D):
    ftlr_instr W regs p g b e a w (UnSeal dst r1 r2) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_UnSeal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hunseal Hwb HincrPC | ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    }

    apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

    assert (r1 ≠ PC) as Hne1.
    { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
    rewrite lookup_insert_ne in Hr1; auto.
    assert (r2 ≠ PC) as Hne2.
    { destruct (decide (PC = r2)); last auto. simplify_map_eq; auto. }
    rewrite lookup_insert_ne in Hr2; auto.

    unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
    unshelve iDestruct ("Hreg" $! r2 _ _ Hr2) as "HVsd"; eauto.
    (* Generate interp instance before step, so we get rid of the later *)
    iDestruct (unsealing_preserves_interp with "HVsd HVsr") as "HVsb"; auto.

    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
    { destruct ρ;auto;[|ospecialize (Hnotmonostatic _)];contradiction. }

    (* If PC=dst and perm of unsealed cap = E -> error! *)
    destruct (decide (PC = dst ∧ p'' = E)) as [ [Herr1 Herr2] | HNoError].
    { (* Error case *)
      simplify_map_eq.
      iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]".
      { subst. by rewrite lookup_insert. }
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC_perm with "[HPC]"); eauto. split; auto.
      iIntros "!> _".
      iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value.
      iIntros (a1); inversion a1.
    }

    destruct (decide (PC = dst)) as [Heq | Hne]; cycle 1.
    { (* PC ≠ dst *)
      simplify_map_eq; map_simpl "Hmap".
      iApply ("IH" $! _ (<[dst:=WSealable sb]> regs)
               with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]")
      ; try (iClear "IH") ; eauto.
      { cbn. intros.
        by repeat (rewrite lookup_insert_is_Some'; right).
      }
      { iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri.
          rewrite lookup_insert in Hvs;
            inversion Hvs.
          auto. }
        { repeat (rewrite lookup_insert_ne in Hvs); auto.
          iApply "Hreg"; auto. }
      }
      {
        rewrite !fixpoint_interp1_eq /=.
        destruct Hp as [-> | [  -> | [-> ->] ] ]; rewrite /region_conditions //=.
      }
    }
    { (* PC = dst *)
      simplify_map_eq; map_simpl "Hmap".
      destruct (decide (p'' = RX ∨ p'' = RWX ∨ p'' = RWLX ∧ g'' = Local)) as [Hpft|Hpft].
      - iApply ("IH" $! _ regs
                 with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]")
        ; try (iClear "IH") ; eauto.
      {
        rewrite !fixpoint_interp1_eq /=.
        destruct Hpft as [-> | [  -> | [-> ->] ] ]; rewrite /region_conditions //=.
      }
      - (* not eq RX/RWX/RWLX-Local *)
        destruct (decide (p'' = RX)); simplify_eq.
        { destruct (Hpft); by left. }
        destruct (decide (p'' = RWX)); simplify_eq.
        { destruct (Hpft); by right; left. }
        destruct (decide (p'' = RWLX )); simplify_eq.
        destruct g'' ; simplify_eq; cycle 1.
        { destruct (Hpft); by right; right. }
        { iEval (rewrite fixpoint_interp1_eq //=) in "HVsb"; done. }

        iApply (wp_bind (fill [SeqCtx])).
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
        iApply (wp_notCorrectPC with "HPC")
        ; [eapply not_isCorrectPC_perm;  simpl in Hp; try discriminate; eauto|].
        iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto;iNext; iIntros "_".
        iApply wp_value.
        iIntros. discriminate. }
    Qed.

End fundamental.
