From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_Jmp.

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


  Lemma jmp_case (W : WORLD) (regs : leibnizO Reg)
    (p : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (r0 : RegName) (P:D):
    ftlr_instr W regs p g b e a w (Jmp r0) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto.
    destruct (decide (r0 = PC)).
    - subst r0.
      iApply (wp_jmp_successPC with "[HPC Ha]"); eauto; first iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iNext; iIntros "_".
      iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      (* close region *)
      iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g0)];contradiction. }
      (* apply IH *)
      iApply ("IH" $! _ _ _ g _ _ a with "[] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
      { iPureIntro. apply Hsome. }
      destruct p; iFrame.
      destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; congruence.
    - specialize Hsome with r0 as Hr0.
      destruct Hr0 as [wsrc Hsomesrc].
      iDestruct ((big_sepM_delete _ _ r0) with "Hmap") as "[Hsrc Hmap]"; eauto.
      rewrite (lookup_delete_ne regs PC r0); eauto.
      iApply (wp_jmp_success with "[$HPC $Ha $Hsrc]"); eauto.
      iNext. iIntros "[HPC [Ha Hsrc]] /=".
      iApply wp_pure_step_later; auto.
      (* reconstruct regions *)
      iDestruct ((big_sepM_delete _ _ r0) with "[Hsrc Hmap]") as "Hmap /=";
        [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
      rewrite -delete_insert_ne; auto.
      destruct (updatePcPerm wsrc) eqn:Heq ; [ | destruct sb | ]; cycle 1.
      { (* TODO simplify using "destruct (PermFlowsTo RX p0) eqn:Hpft; cycle 1." *)
        destruct p0.
        - iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        - iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        - iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        - iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        - iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id regs r0); auto.
          iDestruct ("Hreg" $! r0 _ n Hsomesrc) as "Hwsrc".
          destruct wsrc; simpl in Heq; try congruence.
          destruct sb, p0; try congruence.
          + inv Heq. rewrite (fixpoint_interp1_eq _ (WCap _ _ _ _ _)).
            simpl.
            iNext; iIntros "_".
            iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g1)];contradiction. }
            iApply ("IH" with "[] [] [$Hmap] [$Hr] [$Hsts] [$Hown]"); eauto.
          + inv Heq.
            iEval (rewrite fixpoint_interp1_eq) in "Hwsrc".
            simpl. rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hwsrc" as "#H".
            iAssert (future_world g0 W W) as "Hfuture".
            { iApply futureworld_refl. }
            iSpecialize ("H" with "Hfuture").
            iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g1)];contradiction. }
            iDestruct ("H" with "[$Hmap $Hr $Hsts $Hown]") as "HA"; auto.
        - iNext; iIntros "_".
          iApply (wp_bind (fill [SeqCtx])).
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; eauto|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; iIntros; discriminate.
        - iNext; iIntros "_".
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[|specialize (Hnotmonostatic g1)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id regs r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct sb,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 _ n Hsomesrc) as "Hwsrc".
          rewrite (fixpoint_interp1_eq _ (WCap _ _ _ _ _)).
          simpl.
          iClear "Hinv".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
        - iNext; iIntros "_".
          iDestruct (region_close with "[$Hstate $Hr Hw $Ha $Hmono]") as "Hr"; eauto.
          { destruct ρ;auto;[|specialize (Hnotmonostatic g1)];contradiction. }
          iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=".
          apply lookup_insert. rewrite delete_insert_delete. iFrame.
          rewrite (insert_id regs r0); auto.
          destruct wsrc; simpl in Heq; try congruence.
          destruct sb,p0; try congruence. inv Heq.
          iDestruct ("Hreg" $! r0 _ n Hsomesrc) as "Hwsrc".
          destruct g0; try congruence
          ; first by iEval (rewrite fixpoint_interp1_eq //=) in "Hwsrc".
          iClear "Hinv_interp".
          iApply ("IH" with "[] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); iFrame "#"; eauto.
      }

      (* Non-capability cases *)
      all: iNext; iIntros "_".
      all: iApply (wp_bind (fill [SeqCtx])).
      all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
      all: iNext; iIntros "HPC /=".
      all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
      all: iApply wp_value; iIntros; discriminate.
  Qed.

End fundamental.
