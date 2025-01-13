From cap_machine.binary_model Require Export logrel_binary.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Import ftlr_base_binary region_invariants_transitions_binary.
From cap_machine.rules Require Import rules_base rules_Jnz.
From cap_machine.binary_model.rules_binary Require Import rules_binary_base rules_binary_Jnz.

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

  Lemma Jnz_spec_determ r dst src regs regs' retv retv' :
    Jnz_spec r dst src regs retv ->
    Jnz_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto; try congruence.
  Qed.

  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let g := fresh "g" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as ((((p & g) & b) & e) & a).

  Lemma jnz_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (r1 r2 : RegName) (P:D):
    ftlr_instr W r p g b e a w (Jnz r1 r2) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_Jnz _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(#Hmovspec & Hj & Ha' & Hsmap) /=";eauto.
    { rewrite lookup_insert. eauto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'. destruct Hsome with rr;eauto. }
    iDestruct "Hmovspec" as %HSpec'.

    specialize (Jnz_spec_determ _ _ _ _ _ _ _ HSpec HSpec') as [Hregs <-].

    destruct HSpec.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX)
      end. simplify_map_eq. rewrite insert_insert.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs /=";auto.
      iApply wp_pure_step_later; auto. iNext.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' Hw $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];try contradiction. }
      destruct Hregs as [Hregs | Hcontr];[|inversion Hcontr].
      iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); try iClear "IH"; eauto.
      rewrite -Heqregs -Hregs insert_insert. auto. }
    { iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs /=";auto.
      simplify_map_eq. iApply wp_pure_step_later; auto.
      rewrite !insert_insert.
      destruct (updatePcPerm w') as [n0|c0] eqn:Hw.
      { iApply (wp_bind (fill [SeqCtx])).
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
        iApply (wp_notCorrectPC with "HPC"); [intro; match goal with H: isCorrectPC (inl _) |- _ => inv H end|].
        iNext. iNext. iIntros "HPC /=".
        iApply wp_pure_step_later; auto.
        iApply wp_value.
        iNext. iIntros. discriminate. }
      { destruct_cap c0. destruct (PermFlowsTo RX p0) eqn:Hpft.
        { destruct w'; simpl in Hw; try discriminate.
          destruct_cap c. assert (Heq: (if perm_eq_dec p0 p1 then True else p0 = RX /\ p1 = E) /\ g0 = g1 /\ b0 = b1 /\ e0 = e1 /\ a0 = a1) by (destruct (perm_eq_dec p0 p1); destruct p1; inv Hw; simpl in Hpft; try congruence; auto; repeat split; auto).
          clear Hw. destruct (perm_eq_dec p0 p1); [subst p1; destruct Heq as (_ & -> & -> & -> & ->)| destruct Heq as ((-> & ->) & -> & -> & -> & ->)].
          { iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p1)];contradiction. }
            rewrite /region_conditions.
            destruct Hregs as [Hregs | Hcontr];[|inversion Hcontr].
            iApply ("IH" $! _ r with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs]"); try iClear "IH"; eauto.
            { rewrite -Heqregs -Hregs insert_insert//. }
            - destruct p0; simpl in Hpft; auto; try discriminate.
              destruct (reg_eq_dec r1 PC).
              + subst r1. simplify_map_eq; auto.
              + simplify_map_eq.
                iDestruct ("Hreg" $! r1 n) as "Hr1".
                assert (r.2 !! r1 = Some (inr (RWLX, g1, b1, e1, a1))).
                { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
                rewrite /RegLocate H1 H3. rewrite (fixpoint_interp1_eq _ (inr _,inr _)).
                simpl; destruct g1; auto.
            - destruct (reg_eq_dec r1 PC).
              + subst r1. simplify_map_eq. auto.
              + simplify_map_eq.
                iDestruct ("Hreg" $! r1 n) as "Hr1".
                assert (r.2 !! r1 = Some (inr (p0, g1, b1, e1, a1))).
                { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
                rewrite /RegLocate H1 H3.
                iDestruct (readAllowed_implies_region_conditions with "Hr1") as "Hregion".
                { destruct p0; simpl in *; try discriminate; eauto. }
                iFrame "Hregion". }
          { assert (r1 <> PC) as HPCnr1.
            { intro; subst r1; simplify_map_eq. naive_solver. }
            simplify_map_eq. iDestruct ("Hreg" $! r1 HPCnr1) as "Hr1".
            assert (r.2 !! r1 = Some (inr (E, g1, b1, e1, a1))).
            { rewrite -(lookup_insert_ne _ PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//. }
            rewrite /RegLocate H1 H3. rewrite (fixpoint_interp1_eq _ (inr _,inr _)) /=.
            iDestruct (region_close with "[Hw $Hstate $Hr $Ha $Ha' $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized p0)];contradiction. }
            rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hr1" as "[_ #H]".
            iAssert (future_world g1 e1 W W) as "Hfuture".
            { destruct g1; iPureIntro.
              - destruct W. apply related_sts_priv_refl_world.
              - destruct W. apply related_sts_priv_refl_world.
              - destruct W. apply related_sts_a_refl_world. }
            iSpecialize ("H" $! _ _ with "Hfuture").
            destruct Hregs as [Hregs | Hcontr];[|inversion Hcontr].
            iNext. iDestruct ("H" with "[$Hmap Hsmap $Hr $Hsts $Hown $Hs]") as "[_ HX]"; auto. iSplit;auto. rewrite -Heqregs -Hregs insert_insert//. } }
        iApply (wp_bind (fill [SeqCtx])).
        iDestruct ((big_sepM_delete _ _ PC) with "Hmap") as "[HPC Hmap]"; [apply lookup_insert|].
        iApply (wp_notCorrectPC with "HPC").
        - intros HH. inv HH. naive_solver.
        - iNext. iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto.
          iApply wp_value.
          iNext. iIntros. discriminate. } }
  Qed.

End fundamental.
