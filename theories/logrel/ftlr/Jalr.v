From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_Jalr.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma jalr_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (rdst rsrc : RegName) (P:V)  (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName):
    ftlr_instr W C regs p p' g b e a w (Jalr rdst rsrc) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Jalr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' pc_a' wsrc Hrsrc Hpca' ->| Hpca' ]; cycle 1.
    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }

    iAssert (interp W C (WSentry true p g b e pc_a')) as "Hinterp_ret".
    {
      destruct Hp as [Hexec _].
      iDestruct (interp_cap_disjoint with "Hinv_interp") as %[_ Hheap]; first exact Hexec.
      assert (not_heap_range b e) as Hsentry.
      { split; last exact Hheap.
        apply not_true_is_false. intros Hbase_heap.
        apply withinBounds_true_iff in Hbase_heap.
        rewrite /disjoint_from_heap elem_of_disjoint in Hheap.
        eapply (Hheap b); apply elem_of_finz_seq_between; solve_addr. }
      iApply (interp_weakeningSentry with "IH Hinv_interp");eauto;try solve_addr.
      - by apply executeAllowed_nonO.
      - reflexivity.
    }

    iApply wp_pure_step_later; auto.
    rewrite (linsert_reg_not_cnull PC) // insert_insert_eq.

    destruct (decide (rdst = PC)) as [HPC_dst|HPC_dst]; simplify_eq.
    { iNext; iIntros "_".
      iApply (wp_bind (fill [SeqCtx])).
      rewrite (linsert_reg_not_cnull PC) // insert_insert_eq.
      iExtract "Hmap" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
      iNext; iIntros "HPC /=".
      iApply wp_pure_step_later; auto; iNext; iIntros "_".
      iApply wp_value; iIntros; discriminate.
    }

    set (wret := if decide (rdst = cnull) then lnull else WSentry true p g b e pc_a' @@? None).
    rewrite /linsert_reg (insert_insert_ne _ rdst PC) //.
    iAssert (interp W C wret) as "#Hinterp_ret'".
    { rewrite /wret.
      destruct (decide (rdst = cnull)); [by iApply interp_untagged | iExact "Hinterp_ret"]. }
    iClear "Hinterp_ret".

    (* The new PC is the source word with the PC permission, and keeps its
       identifier. *)
    destruct wsrc as [wsrc πs].
    rewrite /lupdatePcPerm /lift_word /=.
    iAssert (interp W C (wsrc @@? πs)) as "#Hwsrc".
    { destruct (decide (rsrc = PC)) as [->|HrsrcPC].
      - rewrite llookup_reg_not_cnull // lookup_insert_eq in Hrsrc.
        injection Hrsrc as <- <-. iExact "Hinv_interp".
      - destruct (decide (rsrc = cnull)) as [->|Hnull].
        + rewrite /llookup_reg in Hrsrc. apply bind_Some in Hrsrc as (? & _ & Hw).
          injection Hw as <- <-. by iApply interp_untagged.
        + rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hrsrc.
          iApply "Hreg"; eauto. }

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    destruct (updatePcPerm wsrc) as
      [z | [t0 p0 g0 b0 e0 a0 | t0 sp0 g0 b0 e0 a0] | t0 p0 g0 b0 e0 a0 | ot sb]
      eqn:Hwsrc; cycle 1.
    { destruct t0; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; auto.
      }
      destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; auto.
      }

      destruct_word wsrc; try destruct t; cbn in Hwsrc; try discriminate.
      { destruct c; inv Hwsrc.
        iNext ; iIntros "_".
        iApply ("IH" $! _ _ _ _ _ (<[rdst:=wret]> regs) with
                 "[%] [] [$Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$]") ; eauto.
        - intros; cbn. rewrite lookup_insert_is_Some.
          destruct (decide (rdst = x)); auto; right; split; auto.
        - iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = rdst)); simplify_map_eq; cycle 1.
          * iApply ("Hreg" $! ri) ; auto.
          * iExact "Hinterp_ret'".
      }
      inv Hwsrc.
      iEval (rewrite fixpoint_interp1_eq) in "Hwsrc".
      simpl; rewrite /enter_cond.
      iDestruct "Hwsrc" as "[%Hnonheap #Hinterp_src]".
      iAssert (future_world g0 W W) as "Hfuture".
      { iApply futureworld_refl. }
      iSpecialize ("Hinterp_src" with "Hfuture").
      pose proof (LocalityFlowsToReflexive g0) as Hg0.
      iSpecialize ("Hinterp_src" $! g0 Hg0).
      iNext. iIntros "_".
      iApply ("Hinterp_src" $! cstk Ws Cs (<[rdst:=wret]> regs)
               with "[$Hmap $Hworld_interp $Htframe $Hown $Hcont]").
      iSplit; last done.
      iSplit.
      + iIntros (ri); cbn; iPureIntro.
        rewrite lookup_insert_is_Some.
        destruct (decide (rdst = ri)); auto; right; split; auto.
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = rdst)); simplify_map_eq; cycle 1.
        * iApply ("Hreg" $! ri) ; auto.
        * iExact "Hinterp_ret'".
    }

    (* Non-capability cases *)
    all: iExtract "Hmap" PC as "HPC".
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: iApply wp_pure_step_later; auto; iNext; iIntros "_".
    all: iApply wp_value; auto.
  Qed.

End fundamental.
