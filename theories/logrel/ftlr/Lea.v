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
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma lea_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
    (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Lea dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hpc_live Hheap_wf Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#Halloc #IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
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
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (t'' = true ∧ p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (regs' !! csp)) as [??].
      { rewrite Hregs'. destruct (decide (dst = csp));simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ _ _ regs' with "Halloc [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri. simplify_map_eq.
          destruct (decide (dst = cnull)); [iApply interp_int|]; simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply (interp_weakening with "IH"); eauto; try solve_addr.
          - eapply PermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert_eq;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs').

      assert (t'' = true ∧ p'' = p ∧ g'' = g ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; auto. }

      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (regs' !! csp)) as [??].
      { rewrite Hregs'. destruct (decide (dst = csp));simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ _ _ regs' with "Halloc [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        { subst ri. simplify_map_eq.
          destruct (decide (dst = cnull)); [iApply interp_int|]; simplify_map_eq.
          unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
          iApply interp_weakening_ot; eauto; try solve_addr.
          - apply SealPermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - subst regs';rewrite insert_insert_eq;iApply "Hmap".
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    {
      match type of HincrPC with
      | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
          set (wout := wnew) in HincrPC
      end.
      assert (Htagout : get_tag wout = false).
      { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
      incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
        { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
        rewrite Hwout /= in Htagout. subst t0.
        map_simpl "Hmap".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
        rewrite lookup_insert_eq in HPC0.
        injection HPC0 as <- <- <- <- <- <-.
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
          with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull));
              [iApply interp_int | by iApply interp_untagged]. }
          rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    {
      match type of HincrPC with
      | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
          set (wout := wnew) in HincrPC
      end.
      assert (Htagout : get_tag wout = false).
      { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
      incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
        { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
        rewrite Hwout /= in Htagout. subst t0.
        map_simpl "Hmap".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
        rewrite lookup_insert_eq in HPC0.
        injection HPC0 as <- <- <- <- <- <-.
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
          with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull));
              [iApply interp_int | by iApply interp_untagged]. }
          rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
