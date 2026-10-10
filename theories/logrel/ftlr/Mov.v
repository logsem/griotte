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
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Mov with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec; cycle 1.
    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    - incrementPC_inv as (t0 & p0 & g0 & b0 & e0 & a0 & a0' & π0 & ? & ? & ?); simplify_map_eq.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      destruct (decide (dst = PC)) as [HdstPC|HdstPC]; simplify_map_eq.
      { map_simpl "Hmap".
        destruct src; simpl in *; try discriminate.

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        destruct (decide (r = PC)).
        { simplify_map_eq.
          iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
        }
        simplify_map_eq.
        assert (r ≠ cnull); simplify_map_eq.
        { intros ->; simplify_map_eq.
          destruct (regs !! cnull) eqn:Heq; rewrite Heq in H; cbn in *; try done. }
        apply bind_Some in H as (wr & Hr & Hwr).
        case_decide; first done. simplify_eq.
        iDestruct ("Hreg" $! r _ n Hr) as "Hr0".
        destruct t0; cycle 1.
        { iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC_tag with "HPC"); first done.
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value; auto.
        }
        destruct (executeAllowed p0) eqn:Hpft; cycle 1.
        { iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto; iNext; iIntros "_".
          iApply wp_value;auto.
        }

        iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        iApply (interp_weakening with "IH Hr0"); eauto; try reflexivity; try solve_addr; try apply subseg_heap_base_same.
      }
      { map_simpl "Hmap".

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        iApply ("IH" $! _ _ _ _ _ (<[dst:=if decide (dst = cnull) then lnull else w0]> _) with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        - intros x; rewrite lookup_insert_is_Some'; right; apply Hsome.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)); simplify_map_eq.
          + (* ri = dst *)
            destruct (decide (dst = cnull)); [by iApply interp_untagged|].
            destruct src; simplify_map_eq; [by iApply interp_untagged|].
            destruct (decide (PC = r)); simplify_map_eq; [done|].
            apply bind_Some in H as (wr & Hr & Hwr).
            destruct (decide (r = cnull)); simplify_eq; [by iApply interp_untagged|].
            iApply ("Hreg" $! r) ; auto.
          + iApply ("Hreg" $! ri) ; auto.
        - iApply (interp_next_PC with "[Hinv_interp]"); eauto.
      }
  Qed.

End fundamental.
