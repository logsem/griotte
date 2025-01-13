From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.binary_model Require Export logrel_binary.
From cap_machine.binary_model Require Import ftlr_base_binary.
From cap_machine.rules Require Import rules_IsPtr.
From cap_machine.binary_model.rules_binary Require Import rules_binary_IsPtr.

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

  Lemma IsPtr_spec_determ r dst src regs regs' retv retv' :
    IsPtr_spec r dst src regs retv ->
    IsPtr_spec r dst src regs' retv' ->
    (regs = regs' ∨ retv = FailedV) ∧ retv = retv'.
  Proof.
    intros Hspec1 Hspec2.
    inversion Hspec1; inversion Hspec2; subst; simplify_eq; split; auto.
  Qed.

  Lemma isptr_case (W : WORLD) (r : prodO (leibnizO Reg) (leibnizO Reg)) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r0 : RegName) (P:D) :
    ftlr_instr W r p g b e a w (IsPtr dst r0) ρ P.
  Proof.
    intros Heqregs Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#Hspec #IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha Ha' HPC Hmap HsPC Hsmap Hj".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iDestruct ((big_sepM_delete _ _ PC) with "[HsPC Hsmap]") as "Hsmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_IsPtr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".

    iMod (step_IsPtr _ [SeqCtx] with "[$Ha' $Hsmap $Hj $Hspec]") as (retv' regs'') "(Hj & % & Ha' & Hsmap)";eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; destruct Hsome with rr; eauto. }

    specialize (IsPtr_spec_determ _ _ _ _ _ _ _ HSpec H0) as [Heq <-].

    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { destruct Heq as [<- | Hcontr];[|inversion Hcontr].
      incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      iMod (do_step_pure _ [] with "[$Hspec $Hj]") as "Hs' /=";auto.
      assert (dst <> PC) as HdstPC. { intros ->. simplify_map_eq. }
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Ha' $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized p)];contradiction. }
      iApply ("IH" $! _ (<[dst:= _]> _,<[dst:=_]> _) with "[] [Hmap] [Hsmap] [$Hr] [$Hsts] [$Hown] [$Hs']");
        try iClear "IH"; eauto.
      iSplit.
      { iPureIntro. cbn; intro. split; repeat (rewrite lookup_insert_is_Some'; right); destruct Hsome with x5; eauto. }
      { iIntros (ri Hri). rewrite /RegLocate insert_commute // lookup_insert_ne //.
        destruct (decide (ri = dst)); simplify_map_eq.
        * repeat rewrite fixpoint_interp1_eq; auto.
        * iDestruct ("Hreg" $! _ Hri) as "Ha".
          rewrite -(lookup_insert_ne r.2 PC _ (inl 0%Z))// -Heqregs lookup_insert_ne//.
    } }
  Qed.

End fundamental.
