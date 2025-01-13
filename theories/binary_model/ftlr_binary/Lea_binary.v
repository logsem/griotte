From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary monotone_binary.
From cap_machine.binary_model Require Import rules_binary_base interp_weakening_binary.
From cap_machine.rules Require Import rules_Lea rules_base.
From cap_machine.binary_model.rules_binary Require Import rules_binary_Lea rules_binary_base.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ} {cfgg : cfgSG Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (prodO (leibnizO Word) (leibnizO Word)) -n> iPropO Σ).
  Notation R := (WORLD -n> (prodO (leibnizO Reg) (leibnizO Reg)) -n> iPropO Σ).
  Implicit Types v : (prodO (leibnizO Word) (leibnizO Word)).
  Implicit Types interp : (D).

  Lemma Lea_spec_determ r dst src regs regs' retv retv' :
    Lea_spec r dst src regs retv ->
    Lea_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
    - inv H7; try congruence. rewrite H0 in H6; congruence.
      rewrite H0 in H6. inv H6. rewrite H2 in H8. simplify_eq.
      destruct p0;try done.
    - inv H7; try congruence. rewrite H0 in H6; congruence.
      rewrite H0 in H6. inv H6. rewrite H2 in H8. simplify_eq.
      destruct p0;try done.
    - inv H0; try congruence. rewrite H1 in H2; congruence.
      rewrite H4 in H8. inv H8. rewrite H1 in H2. inv H2. rewrite H5 in H9. inv H9.
      destruct p;try done.
  Qed.

  Lemma lea_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr W r p g b e a w (Lea dst r0) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_lea _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(Hj & % & Ha' & Hsmap')";eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    specialize (Lea_spec_determ _ _ _ _ _ _ _ HSpec H0) as [Heq ->].

    destruct HSpec as [ * Hdst ? Hz Hoffset HUa HincrPC |].
    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX).

      assert (p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      destruct Heq as [<- | Hcontr];[|inversion Hcontr].

      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs' /=";auto.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g1)|specialize (Hnotuninitialized p1)];contradiction. }
      iApply ("IH" $! _ (regs',regs') with "[] [Hmap] [Hsmap'] [$Hr] [$Hsts] [$Hown] [$Hs']").
      { iSplit. cbn. intros. subst regs'. iPureIntro.
        split; repeat (apply lookup_insert_is_Some'; right);destruct Hsome with x0;eauto.
        iIntros (ri Hri). subst regs'.
        simpl. rewrite /RegLocate lookup_insert_ne//.
        destruct (decide (ri = dst)).
        { subst ri. unshelve iSpecialize ("Hreg" $! dst _); eauto.
          rewrite lookup_insert. assert (Hdst':=Hdst). rewrite Heqregs in Hdst'.
          rewrite lookup_insert_ne// in Hdst. rewrite lookup_insert_ne// in Hdst'.
          rewrite Hdst Hdst'. iApply interp_weakening; eauto; try solve_addr.
          - destruct p0; simpl; auto.
          - eapply PermFlowsToReflexive.
          - destruct g0; auto. }
        { rewrite !lookup_insert_ne//.
          iDestruct ("Hreg" $! _ Hri) as "HH".
          rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
      } }
      { subst regs'. rewrite insert_insert. iApply "Hmap". }
      { subst regs'. rewrite insert_insert. iApply "Hsmap'". }
      { iPureIntro. tauto. }
      eauto. }
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
  Qed.

End fundamental.
