From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary monotone_binary interp_weakening_binary.
From cap_machine Require Import addr_reg region.
From cap_machine.rules Require Import rules_base rules_Subseg.
From cap_machine.binary_model.rules_binary Require Import rules_binary_base rules_binary_Subseg.

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

  Lemma Subseg_spec_determ r dst r1 r2 regs regs' retv retv' :
    Subseg_spec r dst r1 r2 regs retv ->
    Subseg_spec r dst r1 r2 regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
    - inv H7; try congruence. rewrite H0 in H6; congruence.
    - inv H7; try congruence. rewrite H0 in H6; congruence.
    - inv H0; try congruence. rewrite H1 in H2; congruence.
  Qed.

  Lemma leb_addr_spec:
    forall a1 a2,
      reflect (le_addr a1 a2) (leb_addr a1 a2).
  Proof.
    intros. rewrite /leb_addr /le_addr.
    apply Z.leb_spec0.
  Qed.

  Lemma isWithin_implies a0 a1 b e:
    isWithin a0 a1 b e = true ->
    (b <= a0 /\ a1 <= e)%a.
  Proof.
    rewrite /isWithin. rewrite andb_true_iff /le_addr !Z.leb_le. solve_addr.
  Qed.

  Lemma within_in_range:
    forall a b b' e e',
      (b <= b')%a ->
      (e' <= e)%a ->
      in_range a b' e' ->
      in_range a b e.
  Proof.
    intros * ? ? [? ?]. split; solve_addr.
  Qed.

  Lemma subseg_interp_preserved W p l b b' e e' a :
      p <> E ->

      (b <= b')%a ->
      (e' <= e)%a ->
      IH -∗
      (fixpoint interp1) W (inr (p, l, b, e, a),inr (p, l, b, e, a)) -∗
      (fixpoint interp1) W (inr (p, l, b', e', a),inr (p, l, b', e', a)).
  Proof.
    intros Hne Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    - destruct (isU p); solve_addr.
    - destruct p; reflexivity.
    - destruct l; reflexivity.
  Qed.

  Lemma subseg_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName) (P:D):
    ftlr_instr W r p g b e a w (Subseg dst r1 r2) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_Subseg _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'' HSpec') "(Hj & Ha' & Hsmap)";eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }

    specialize (Subseg_spec_determ _ _ _ _ _ _ _ _ HSpec HSpec') as [Heq <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX)
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs /=";auto.

      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert in HPC |- *. simplify_map_eq.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
        iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); try iClear "IH"; eauto.
        rewrite -Heqregs. auto. iModIntro.
        generalize (isWithin_implies _ _ _ _ H4). intros [A B].
        destruct (Z_le_dec b'' e'').
        + rewrite /region_conditions (isWithin_region_addrs_decomposition b'' e'' b0 e0); auto.
          iDestruct (big_sepL_app with "Hinv") as "[Hinv1 Hinv2]".
          iDestruct (big_sepL_app with "Hinv2") as "[Hinv3 Hinv4]".
          iFrame "#".
        + rewrite /region_conditions.
          replace (region_addrs b'' e'') with (nil: list Addr).
          rewrite big_sepL_nil. auto.
          unfold region_addrs, region_size. rewrite Z_to_nat_nonpos //; lia. }
      { simplify_map_eq.
        iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
        iApply ("IH" $! _ (<[dst:=_]> _,<[dst:=_]> _) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); eauto.
        iSplit.
        - iPureIntro. intros; simpl.
          rewrite lookup_insert_is_Some.
          split. all: destruct (reg_eq_dec dst x0); auto; right; split; auto.
          all: rewrite lookup_insert_is_Some.
          all: destruct (reg_eq_dec PC x0); auto; right; split; auto; destruct Hsome with x0;eauto.
        - iIntros (ri Hri). rewrite /RegLocate.
          destruct (reg_eq_dec ri dst).
          + subst ri. rewrite lookup_insert.
            iDestruct ("Hreg" $! dst Hri) as "Hdst".
            generalize (isWithin_implies _ _ _ _ H4). intros [A B].
            rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
            rewrite H0. iApply subseg_interp_preserved; eauto.
          + repeat rewrite lookup_insert_ne; auto.
            iDestruct ("Hreg" $! _ Hri) as "Ha".
            rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
    } }
  Qed.

End fundamental.
