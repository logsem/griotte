From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_ClearTag rules_base.
From griotte Require Import BinOp.
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

  Lemma cleartag_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
        (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
        (ρ : region_type) (dst src : RegName) (P:D)
        (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (ClearTag dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".
    iDestruct (WorldRes_acc with "WorldRes") as "[(Ha & Hinterp) WorldRes]".
    iApply (wp_ClearTag with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }
    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [w0 Hsrc Hinc -> | ]; cycle 1.
    - subst regs'.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
    - incrementPC_inv as (t0 & p0 & g0 & b0 & e0 & a0 & a0' & π0 & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply ("IH" $! _ _ _ _ _ (<[dst:=lclear_tag w0]ₗ> regs) _ _ _ _ a0' None
        with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
      + by apply full_map_linsert.
      + iApply (interp_linsert with "Hreg"). iIntros (_). iApply interp_clear_tag.
      + iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
