From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary monotone_binary interp_weakening_binary.
From cap_machine.rules Require Import rules_base rules_Restrict.
From cap_machine.binary_model Require Import rules_binary_base rules_binary_Restrict.

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

  Lemma Restrict_spec_determ r dst src regs regs' retv retv' :
    Restrict_spec r dst src regs retv ->
    Restrict_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
    - inv H6; try congruence. rewrite H0 in H5; congruence.
    - inv H6; try congruence. rewrite H0 in H5; congruence.
    - inv H0; try congruence. rewrite H1 in H2; congruence.
  Qed.

  Lemma locality_eq_dec:
    forall (l1 l2: Locality), {l1 = l2} + {l1 <> l2}.
  Proof.
    destruct l1, l2; auto.
  Qed.

  Lemma PermPairFlows_interp_preserved W p p' l l' b e a :
    p <> E ->
    PermPairFlowsTo (p', l') (p, l) = true →
    IH -∗
    (fixpoint interp1) W (inr (p, l, b, e, a),inr (p, l, b, e, a)) -∗
    (fixpoint interp1) W (inr (p', l', b, e, a),inr (p', l', b, e, a)).
  Proof.
    intros HpnotE Hp. iIntros "#IH HA".
    destruct (andb_true_eq _ _ ltac:(symmetry in Hp; exact Hp)) as [HH1 HH2].
    simpl in HH1, HH2. iApply (interp_weakening with "IH HA");eauto;try solve_addr.
    - destruct (isU p); solve_addr.
    - rewrite <- HH1. auto.
    - rewrite <- HH2. auto.
  Qed.

  Lemma match_perm_with_E_rewrite:
    forall (A: Type) p (a1 a2: A),
      match p with
      | E => a1
      | _ => a2
      end = if (perm_eq_dec p E) then a1 else a2.
  Proof.
    intros. destruct (perm_eq_dec p E); destruct p; auto; congruence.
  Qed.

  Lemma restrict_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst : RegName) (r0 : Z + RegName) (P:D):
    ftlr_instr W r p g b e a w (Restrict dst r0) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_Restrict _ [SeqCtx] with "[$Ha' $Hsmap $Hspec $Hj]") as (retv' regs'' HSpec') "(Hs & Ha' & Hsmap)";eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    specialize (Restrict_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Heq <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX)
      end. simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hs]") as "Hs /=";auto.

      assert (HPCr0: match r0 with inl _ => True | inr r0 => PC <> r0 end).
      { destruct r0; auto.
        intro; subst r0. simplify_map_eq. }

      destruct (reg_eq_dec PC dst).
      { subst dst. repeat rewrite insert_insert.
        repeat rewrite insert_insert in HPC.
        rewrite lookup_insert in HPC. inv HPC.
        rewrite lookup_insert in H0. inv H0.
        rewrite H5 in H3. iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
        { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
        destruct (PermFlowsTo RX p'') eqn:Hpft.
        { assert (Hpg: p'' = RX ∨ p'' = RWX ∨ p'' = RWLX ∧ g'' = Directed).
          { destruct p''; simpl in Hpft; eauto; try discriminate.
            destruct (andb_true_eq _ _ ltac:(naive_solver)).
            simpl in H3, H4. destruct p0; simpl in H3; try discriminate.
            destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; try discriminate.
            subst g0; destruct g''; simpl in H4; auto; discriminate. }
          rewrite H5. iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); try iClear "IH"; eauto.
          rewrite -Heqregs. auto.
          iModIntro. iApply (big_sepL_mono with "Hinv"); simpl; intros.
          iIntros "H". simpl.
          iDestruct "H" as "[H1 H2]".
          iSplitL "H1".
          { destruct (writeAllowed p'') eqn:Hwa.
            - assert (writeAllowed p0 = true) as ->;auto.
              destruct p0;auto;destruct p'';inversion Hwa;inversion H3.
            - destruct (writeAllowed p0).
              + iExists interp. iFrame. iSplit;[iPureIntro;apply _|].
                iSplit;[auto|]. iNext. iModIntro. iIntros (W1 W2 z1 z2) "Heq".
                rewrite !fixpoint_interp1_eq. iDestruct "Heq" as %->. done.
              + iDestruct "H1" as (P') "(?&?&?)".
                iExists _;iFrame. }
          iDestruct "H2" as %?.
          iPureIntro.
          destruct (andb_true_eq _ _ ltac:(naive_solver)); simpl in *.
          destruct (locality_eq_dec g'' g0).
          * subst g0. destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; destruct Hpg as [Hp' | [ Hp' | [Hp' Hg' ] ] ]; subst; simpl in *; simpl; try congruence; auto.
          * destruct g''; destruct g0; simpl in *; try congruence.
            all: destruct Hp as [Hp | [ Hp | [Hp Hl] ] ]; destruct Hpg as [Hp' | [ Hp' | [Hp' Hg' ] ] ]; subst; simpl in *; simpl; try congruence; auto. }
        { iApply (wp_bind (fill [SeqCtx])).
          iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
         rewrite H5.
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; destruct p''; simpl in Hpft; eauto; discriminate|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. } }

      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
      iApply ("IH" $! _ (<[dst:=_]> _,<[dst:=_]> _) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); eauto.
      iSplit.
      - iPureIntro. intros; simpl. split; repeat (rewrite lookup_insert_is_Some';right);eauto;destruct Hsome with x0;eauto.
      - iIntros (ri Hri). rewrite /RegLocate.
        destruct (decide (ri = dst)).
        + subst ri. rewrite lookup_insert.
          destruct (decodePermPair n) as (p1 & g1).
          iDestruct ("Hreg" $! dst Hri) as "Hdst".
          rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
          rewrite H0. iApply PermPairFlows_interp_preserved; eauto.
        + repeat rewrite lookup_insert_ne; auto.
          iDestruct ("Hreg" $! _ Hri) as "Ha".
          rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
    }
  Qed.

End fundamental.
