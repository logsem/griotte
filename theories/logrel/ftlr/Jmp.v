From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Jmp.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma jmp_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (rimm : Z + RegName) (P:D) :
    ftlr_instr W C regs p p' g b e a w (Jmp rimm) ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".

    iDestruct (pc_open_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Jmp (CL := link_core) with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ lpc' imm Himm Hincr| ]; cycle 1.
    { iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); eauto. }

    incrementPC_inv as (t0&p0&g0&b0&e0&a0&a0'&π0&?&Ha0'&?); simplify_map_eq.
    iNext.

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

    iApply (ftlr_post_next with "HPC Hmap [] [] Hworld_interp") ; eauto.
    iApply "IH". iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr; try reflexivity; try apply subseg_heap_base_same.
  Qed.

End fundamental.
