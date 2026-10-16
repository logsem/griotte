From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import memory_region map_simpl.
From griotte Require Import rules_base rules_Restrict.
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

  Lemma PermPairFlows_interp_preserved W C t p p' g g' b e a π :
    PermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b e a @@? π).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening with "IH HA");eauto;try solve_addr.
  Qed.

  Lemma SealPermPairFlows_interp_preserved W C t p p' g g' b e a π :
    SealPermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WSealRange t p g b e a @@? π) -∗
    interp W C (WSealRange t p' g' b e a @@? π).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening_ot with "HA");eauto;try solve_addr.
  Qed.

  Lemma restrict_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Restrict dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Restrict with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ * Hdst Hz Hpair HPfl HLfl HincrPC Hregs'
                      | * Hdst Hz Hpair HPfl HLfl HincrPC Hregs'
                      | * Hdst Hz Hpair Hflows HincrPC Hregs'
                      | * Hdst Hz Hpair Hflows HincrPC Hregs'
                      | ].
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          rewrite llookup_reg_not_cnull // in Hdst.
          iDestruct ("Hreg" $! dst _ Hdst) as "Hdst".
          iApply PermPairFlows_interp_preserved; eauto.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          rewrite llookup_reg_not_cnull // in Hdst.
          iDestruct ("Hreg" $! dst _ Hdst) as "Hdst".
          iApply SealPermPairFlows_interp_preserved; eauto.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          by iApply interp_untagged.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          by iApply interp_untagged.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { iApply wp_pure_step_later; auto.
      iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
