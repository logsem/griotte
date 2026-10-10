From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Lea.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma lea_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Lea dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_lea with "[$Ha $Hmap]"); eauto.
    { by rewrite lookup_insert_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst Hz Hoffset HincrPC
                      | * Hdst Hz Hoffset HincrPC
                      | * Hdst Hz Hoffset HincrPC
                      | * Hdst Hz Hoffset HincrPC
                      | ].
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & π'' & HPC & Z & Hregs').

      assert (t'' = true ∧ p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e ∧ π'' = None)
        as (-> & -> & -> & -> & -> & ->).
      { rewrite /linsert_reg /llookup_reg in HPC Hdst.
        destruct (decide (PC = dst)); simplify_map_eq; by repeat split. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        subst regs'. rewrite /linsert_reg lookup_insert_ne // in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hdst.
          iSpecialize ("Hreg" $! dst _ Hri Hdst).
          iApply (interp_weakening with "IH Hreg"); eauto; try solve_addr;
            try apply subseg_heap_base_same.
          - eapply PermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert_eq;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & π'' & HPC & Z & Hregs').

      assert (t'' = true ∧ p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e ∧ π'' = None)
        as (-> & -> & -> & -> & -> & ->).
      { rewrite /linsert_reg /llookup_reg in HPC Hdst.
        destruct (decide (PC = dst)); simplify_map_eq; by repeat split. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        subst regs'. rewrite /linsert_reg lookup_insert_ne // in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hdst.
          iSpecialize ("Hreg" $! dst _ Hri Hdst).
          iApply (interp_weakening_ot with "Hreg"); eauto; try solve_addr.
          - apply SealPermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert_eq;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WCap false p0 g0 b0 e0 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); by iApply interp_untagged. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WSealRange false p0 g0 b0 e0 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); by iApply interp_untagged. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
