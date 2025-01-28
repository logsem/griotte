From cap_machine Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine.ftlr Require Import ftlr_base interp_weakening.
From cap_machine.rules Require Import rules_base rules_Lea.
From cap_machine.proofmode Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ} {sealsg: sealStoreG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

   Lemma lea_case (W : WORLD) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
     (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D):
    ftlr_instr W regs p p' g b e a w (Lea dst src) ρ P.
    Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp HO Hpers Hpwl Hregion Hnotrevoked Hnotfrozen Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono #HmonoV Hw Hsts Hown".
    iIntros "Hr Hstate Ha HPC Hmap".
    iInsert "Hmap" PC.
    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst ? Hz Hoffset HincrPC | * Hdst Hz Hoffset HincrPC | ]
    ; cycle 2.
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. iIntros; discriminate. }

    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }
      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]").
      - cbn; intros; subst regs'. by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri. simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening with "IH"); eauto; try solve_addr.
          - eapply PermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (p''&g''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct (region_close with "[$Hstate $Hr $Ha $HmonoV Hw]") as "Hr"; eauto.
      { destruct ρ;auto;[|ospecialize (Hnotfrozen _)];contradiction. }

      iApply ("IH" $! _ regs' with "[%] [] [Hmap] [$Hr] [$Hsts] [$Hown]").
      - cbn; intros; subst regs'. by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri. simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply interp_weakening_ot; eauto; try solve_addr.
          - apply SealPermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    Qed.

End fundamental.
