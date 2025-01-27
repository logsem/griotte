From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Export rules_Get rules_base.
From cap_machine.proofmode Require Import map_simpl register_tactics.

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

  Lemma get_case (W : WORLD) (regs : leibnizO Reg) (p p' : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (ρ : region_type) (dst r : RegName) (ins: instr) (P:D) :
    is_Get ins dst r →
    ftlr_instr W regs p p' g b e a w ins ρ P.
  Proof.
    intros Hinstr Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    rewrite <- Hi in Hinstr; clear Hi.
    iInsert "Hmap" PC.
    iApply (wp_Get with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    - incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|specialize (Hnotfrozen g)];contradiction. }

      iApply ("IH" $! _ (<[dst := _]> (<[PC := _]> regs))
               with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]")
        ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
      { repeat rewrite fixpoint_interp1_eq; auto. }
      { iApply "Hreg"; eauto. }
      + iApply (interp_next_PC with "IH Hinv_interp"); eauto.
  Qed.

End fundamental.
