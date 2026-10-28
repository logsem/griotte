From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Mov.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.
Import uPred.

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

   Lemma mov_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr)
     (w : LWord) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) :
    ftlr_instr W C regs p p' g b e a w (Mov dst src) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Mov (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [w0 Hw0 Hinc -> | w0 Hw0 Hinc]; cycle 1.
    - subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto.
    - incrementPC_inv as (t0 & p0 & g0 & b0 & e0 & a0 & a0' & π0 & ? & ? & ?); simplify_map_eq.
      iNext.

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp").
      + by apply full_map_linsert.
      + iApply (interp_linsert with "Hreg"). iIntros (_).
        by iApply (interp_lword_of_argument with "Hreg").
      + iApply "IH". iApply (interp_next_PC with "[Hinv_interp]"); eauto.
  Qed.

End fundamental.
