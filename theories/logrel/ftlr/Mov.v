From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_Mov.
From griotte Require Import map_simpl register_tactics.
Import uPred.

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

   Lemma mov_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr)
     (w : LWord) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Mov dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Mov with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [w0 Hw0 Hinc -> | w0 Hw0 Hinc]; cycle 1.
    - iTrap; auto.
    - incrementPC_inv as (t0 & p0 & g0 & b0 & e0 & a0 & a0' & π0 & ? & ? & ?); simplify_map_eq.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ (<[dst:=w0]ₗ> regs) with "[%] [] [HPC] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
      + intros x; rewrite /linsert_reg lookup_insert_is_Some'; right; apply Hsome.
      + iIntros (ri wi Hregs_ri).
        rewrite /linsert_reg in Hregs_ri.
        destruct (decide (ri = dst)); simplify_map_eq.
        * (* ri = dst *)
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          destruct src; simplify_map_eq; [by iApply interp_untagged|].
          apply bind_Some in Hw0 as (wr & Hr & Hwr).
          destruct (decide (r = cnull)); simplify_eq; [by iApply interp_untagged|].
          iApply ("Hreg" $! r) ; auto.
        * iApply ("Hreg" $! ri) ; auto.
      + iApply (interp_next_PC with "[Hinv_interp]"); eauto.
  Qed.

End fundamental.
