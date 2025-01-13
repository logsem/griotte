From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Import rules_IsPtr.

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

  Lemma isptr_case (W : WORLD) (r : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r0 : RegName) (P:D) :
    ftlr_instr W r p g b e a w (IsPtr dst r0) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_IsPtr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      assert (dst <> PC) as HdstPC. { intros ->. simplify_map_eq. }
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized w1)];contradiction. }
      iApply ("IH" $! _ (<[dst:= _]> _) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]");
        try iClear "IH"; eauto.
      { cbn; intro. repeat (rewrite lookup_insert_is_Some'; right); eauto. }
      { iIntros (ri Hri). rewrite /RegLocate insert_commute // lookup_insert_ne //.
        destruct (decide (ri = dst)); simplify_map_eq.
        * repeat rewrite fixpoint_interp1_eq; auto.
        * by iApply "Hreg". } }
  Qed.

End fundamental.
