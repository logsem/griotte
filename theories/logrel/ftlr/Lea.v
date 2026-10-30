From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Lea.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma lea_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (ρ : region_part) (dst src : RegName) (arg : Z + RegName) (P:D) :
    ftlr_instr W C regs p p' g b e a w (Lea dst src arg) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros (hb) "@".

    iDestruct (pc_open_acc_fetch with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_lea (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ * Hsrc Hz Hoffset HincrPC Hregs'
                      | * Hsrc Hz Hoffset HincrPC Hregs'
                      | * Hsrc Hz Hoffset HincrPC Hregs'
                      | * Hsrc Hz Hoffset HincrPC Hregs'
                      | * Hsrc Hz HincrPC Hregs'
                      | * Hsrc Hsl HincrPC Hregs'
                      | ].
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        assert (src ≠ cnull) as Hsrc_cnull
          by (eapply llookup_reg_not_zero_not_cnull; [exact Hsrc | done]).
        rewrite llookup_reg_not_cnull // in Hsrc.
        iSpecialize ("Hreg" $! src _ Hsrc).
        iApply (interp_weakening with "IH Hthread Hreg"); eauto; try solve_addr;
          try apply subseg_heap_base_same.
        + eapply PermFlowsToReflexive.
        + apply LocalityFlowsToReflexive.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        assert (src ≠ cnull) as Hsrc_cnull
          by (eapply llookup_reg_not_zero_not_cnull; [exact Hsrc | done]).
        rewrite llookup_reg_not_cnull // in Hsrc.
        iSpecialize ("Hreg" $! src _ Hsrc).
        iApply (interp_weakening_ot with "Hreg"); eauto; try solve_addr.
        + apply SealPermFlowsToReflexive.
        + apply LocalityFlowsToReflexive.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        by iApply interp_untagged.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        by iApply interp_untagged.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        by iApply interp_untagged.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iNext.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iApply (ftlr_post_next with "HPC Hmap Hhwm [] [] Hworld_interp").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        iApply interp_clear_tag.
      - iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hhwm Hreg Hworld_interp"); eauto. }
  Qed.

End fundamental.
