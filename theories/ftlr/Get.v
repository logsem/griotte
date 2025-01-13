From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine Require Import ftlr_base.
From cap_machine.rules Require Export rules_Get.

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

  Lemma get_case (W : WORLD) (r : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r0 : RegName) (ins: instr) (P:D) :
    is_Get ins dst r0 →
    ftlr_instr W r p g b e a w ins ρ P.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hpers Hpwl Hregion Hnotrevoked Hnotmonostatic Hnotuninitialized Hi.
    iIntros "#IH #Hinv #Hreg #Hinva #Hrcond #Hwcond Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite delete_insert_delete.
    rewrite <- Hi in Hinstr. clear Hi.
    iDestruct ((big_sepM_delete _ _ PC) with "[HPC Hmap]") as "Hmap /=";
      [apply lookup_insert|rewrite delete_insert_delete;iFrame|]. simpl.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq. intros rr _.
      apply elem_of_gmap_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    { iApply wp_pure_step_later; auto. iNext.
      iApply wp_value; auto. iIntros; discriminate. }
    { incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext.
      destruct c as ((((p1 & g1) & b1) & e1) & a1).
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotmonostatic g)|specialize (Hnotuninitialized w0)];contradiction. }
      iApply ("IH" $! _ (<[dst := _]> (<[PC := _]> r)) with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]");
        try iClear "IH"; eauto.
      { intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right). }
      iIntros (ri Hri). rewrite /(RegLocate _ ri) insert_commute // lookup_insert_ne //; [].
      destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { by iApply "Hreg". } }
  Qed.

End fundamental.
