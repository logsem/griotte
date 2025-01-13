From cap_machine Require Export logrel.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Import ftlr_base region_invariants_transitions.
From cap_machine.rules Require Import rules_base rules_Jnz.

Section fundamental.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  (* TODO: Move somewhere *)
  Ltac destruct_cap c :=
    let p := fresh "p" in
    let g := fresh "g" in
    let b := fresh "b" in
    let e := fresh "e" in
    let a := fresh "a" in
    destruct c as ((((p & g) & b) & e) & a).

  Lemma jnz_case (W : WORLD) (r : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (r1 r2 : RegName) (P:D):
    ftlr_instr W r p g b e a w (Jnz r1 r2) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Jnz with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { match goal with
      | H: incrementPC _ = Some _ |- _ => apply incrementPC_Some_inv in H as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs' & XX)
      end. simplify_map_eq. rewrite insert_insert.
      iApply wp_pure_step_later; auto. iNext.
      iDestruct (region_close with "[$Hstate $Hr $Ha Hw $Hmono]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized w1)];try contradiction. }
      iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto. }
    { simplify_map_eq. iApply wp_pure_step_later; auto.
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
          { iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized w1)];contradiction. }
            rewrite /region_conditions.
            iApply ("IH" $! _ r with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]"); try iClear "IH"; eauto.
            - destruct p0; simpl in Hpft; auto; try discriminate.
              destruct (reg_eq_dec r1 PC).
              + subst r1. simplify_map_eq; auto.
              + simplify_map_eq.
                iDestruct ("Hreg" $! r1 n) as "Hr1".
                rewrite /RegLocate H1. rewrite (fixpoint_interp1_eq _ (inr _)).
                simpl; destruct g1; auto.
            - destruct (reg_eq_dec r1 PC).
              + subst r1. simplify_map_eq. auto.
              + simplify_map_eq.
                iDestruct ("Hreg" $! r1 n) as "Hr1".
                rewrite /RegLocate H1.
                iDestruct (readAllowed_implies_region_conditions with "Hr1") as "Hregion".
                { destruct p0; simpl in *; try discriminate; eauto. }
                iFrame "Hregion". }
          { assert (r1 <> PC) as HPCnr1.
            { intro; subst r1; simplify_map_eq. naive_solver. }
            simplify_map_eq. iDestruct ("Hreg" $! r1 HPCnr1) as "Hr1".
            rewrite /RegLocate H1. rewrite (fixpoint_interp1_eq _ (inr _)) /=.
            iDestruct (region_close with "[Hw $Hstate $Hr $Ha $Hmono]") as "Hr"; eauto.
            { destruct ρ;auto;[|specialize (Hnotmonostatic g0)|specialize (Hnotuninitialized w1)];contradiction. }
            rewrite /enter_cond.
            rewrite /interp_expr /=.
            iDestruct "Hr1" as "#H".
            iAssert (future_world g1 e1 W W) as "Hfuture".
            { destruct g1; iPureIntro.
              - destruct W. apply related_sts_priv_refl_world.
              - destruct W. apply related_sts_priv_refl_world.
              - destruct W. apply related_sts_a_refl_world. }
            iSpecialize ("H" $! _ _ with "Hfuture").
            iNext. iDestruct ("H" with "[$Hmap $Hr $Hsts $Hown]") as "[_ HX]"; auto. } }
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
