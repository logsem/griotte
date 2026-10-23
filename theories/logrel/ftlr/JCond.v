From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Export rules_JCond.
From griotte Require Import rules_base.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma jcond_case (W : WORLD) (C : CmptName)  (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i : instr) (ρ : region_type) (off arg1 arg2 : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    is_JCond i off arg1 arg2 →
    ftlr_instr trusted_fault W C regs p p' g b e a w i ρ P cstk Ws Cs.
  Proof.
    intros HJCond Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_JCond with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ lpc' n1 n2 Hn1 Hn2 Htest Hincr | lpc' n1 n2 imm Hn1 Hn2 Htest Himm HincrPC | ]; cycle 2.
    { iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto. }

    {
      incrementPC_inv; simplify_map_eq.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]"); eauto.
      iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    incrementPC_inv as (t0&p0&g0&b0&e0&a0&a0'&π0&?&Ha0'&?); simplify_map_eq.
    iApply wp_pure_step_later; auto. iNext; iIntros "_".

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]") ; eauto.
    iApply (interp_weakening with "IH Hinv_interp"); eauto; try solve_addr; try reflexivity; try apply subseg_heap_base_same.
  Qed.

End fundamental.
