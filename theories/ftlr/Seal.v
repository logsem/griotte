From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Seal.
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

  (* Proving the meaning of sealing in the LR sane *)
  Lemma sealing_preserves_interp W sb p0 g0 b0 e0 a0:
        permit_seal p0 = true →
        withinBounds b0 e0 a0 = true →
        fixpoint interp1 W (WSealable sb) -∗
        fixpoint interp1 W (WSealRange p0 g0 b0 e0 a0) -∗
        fixpoint interp1 W (WSealed a0 sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsb #HVsr".
    rewrite (fixpoint_interp1_eq W (WSealRange _ _ _ _ _)) (fixpoint_interp1_eq W (WSealed _ _)) /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "[% [HsealP HWcond]]".
    iExists (P W).
    repeat iSplitR; auto.
    by iApply "HWcond".
  Qed.

  Lemma seal_case (W : WORLD) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:D):
    ftlr_instr W regs p p' g b e a w (Seal dst r1 r2) ρ P.
  Proof.
    intros Hp Hsome i Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iDestruct (execCond_implies_region_conditions with "Hinv_interp") as "#Hinv"; eauto.
    iInsert "Hmap" PC.
    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Hseal Hwb HincrPC | ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate.
    }

    - apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      assert (p'' = p ∧ g'' = g ∧ a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }
      assert (r1 ≠ PC) as Hne.
      { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
      rewrite lookup_insert_ne in Hr1; auto.
      iAssert (fixpoint interp1 W (WSealable sb)) as "#HVsb". {
        destruct (decide (r2 = PC)) as [Heq|Heq]; simplify_map_eq.
        - rewrite (fixpoint_interp1_eq _ (WCap p g b e a)) /=.
          destruct Hp as [Hp | [Hp | [Hp Hg] ] ]; subst p; try subst g;
            try (iFrame "Hexec"); try (iFrame "Hinv").
          all: iApply (big_sepL_mono with "Hinv").
          all: intros; iIntros "H"; simpl.
          all: iDestruct "H" as (p Hflp) "[H %Hstate]".
          1: iDestruct "H" as (P' HpersP') "Hcond".
          all: iExists p; iFrame "%∗".
        - unshelve iSpecialize ("Hreg" $! r2 _ _ Hr2); eauto.
      }

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.
      iDestruct (region_close with "[$Hstate $Hr $Ha $Hmono Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }

      iApply ("IH" $! _ (<[dst := _]> (<[PC := _]> regs))
               with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]");
        try iClear "IH"; eauto.
      + intro. cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
      { unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
        iApply (sealing_preserves_interp with "[HVsb HVsr]"); eauto.
      }
      { by iApply "Hreg". }
      + destruct Hp as [-> | [  -> | [-> ->] ] ]
          ; rewrite !fixpoint_interp1_eq /region_conditions //=.
  Qed.

End fundamental.
