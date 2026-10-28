From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_JCond.
From griotte Require Import rules_base.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma jcond_case (W : WORLD) (C : CmptName)  (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i : instr) (ρ : region_type) (off arg1 arg2 : Z + RegName) (P:D) :
    is_JCond i off arg1 arg2 →
    ftlr_instr W C regs p p' g b e a w i ρ P.
  Proof.
    intros HJCond Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_JCond (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ lpc' n1 n2 Hn1 Hn2 Htest Hincr | lpc' n1 n2 imm Hn1 Hn2 Htest Himm HincrPC | ]; cycle 2.
    { iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto. }

    {
      incrementPC_inv; simplify_map_eq.
      iNext.

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp"); eauto.
      iApply "IH". iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    incrementPC_inv as (t0&p0&g0&b0&e0&a0&a0'&π0&?&Ha0'&?); simplify_map_eq.
    iNext.

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp") ; eauto.
    iApply "IH". iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr; try reflexivity; try apply subseg_heap_base_same.
  Qed.

End fundamental.
