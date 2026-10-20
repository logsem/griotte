From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Auipcc.
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

  (** The result of [auipcc] is the PC with another address (or its untagged
      version), so it is safe because the PC is. *)
  Lemma auipcc_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (ρ : region_type) (dst : RegName) (imm : Z) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Auipcc dst imm) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Auipcc with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [HincrPC Hregs' | HincrPC]; cycle 1.
    { subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto. }

    apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
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
        rewrite /auipcc_word.
        destruct (a + imm)%a as [a'|]; last by iApply interp_untagged.
        iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr;
          try apply subseg_heap_base_same.
        - eapply PermFlowsToReflexive.
        - apply LocalityFlowsToReflexive.
      }
      { iApply "Hreg"; auto. by simplify_map_eq. }
    - iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
