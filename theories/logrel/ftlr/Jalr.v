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
    (trap_no_resume : LWord → Prop)
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
    ftlr_instr trap_no_resume W C regs p p' g b e a w (Jalr rdst rsrc) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Jalr with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap)".
    destruct HSpec as [ regs' pc_a' wsrc mie Hrsrc Htgt Hpca' Hregs' | wsrc Hrsrc Htgt | Hpca' ]; cycle 1.
    1,2: assert (ρ = Temporary ∨ ρ = Permanent) as Hρ by (destruct ρ; auto; contradiction);
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes";
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto;
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.

    (* The link: a return sentry when [rdst = cra], the unsealed PC otherwise. *)
    iAssert (interp W C (jalr_link rdst mie true p g b e pc_a')) as "Hinterp_ret".
    { rewrite /jalr_link. destruct (decide (rdst = cra)) as [Hcra | Hcra].
      2: { iApply (interp_weakening with "IH Hinv_interp");
           [solve_addr | solve_addr | apply subseg_heap_base_same
           | apply PermFlowsToReflexive | apply LocalityFlowsToReflexive]. }
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

    (* A [cnull] destination leaves the registers unchanged. *)
    assert (∀ x, is_Some (regs' !! x)) as Hsome'.
    { intros x. rewrite Hregs'. case_decide; first apply Hsome.
      rewrite /linsert_reg decide_False // lookup_insert_is_Some.
      destruct (decide (rdst = x)); auto; right; split; auto. }
    iAssert (∀ ri wi, ⌜regs' !! ri = Some wi⌝ → interp W C wi)%I as "#Hreg'".
    { iIntros (ri wi Hri). rewrite Hregs' in Hri. case_decide; first by iApply "Hreg".
      rewrite /linsert_reg decide_False // in Hri.
      destruct (decide (ri = rdst)); simplify_map_eq; [iExact "Hinterp_ret" | by iApply "Hreg"]. }
    iClear "Hinterp_ret". clear Hregs'.

    (* The new PC is the source word with the PC permission, and keeps its
       identifier. *)
    destruct wsrc as [wsrc πs].
    rewrite /lupdatePcPerm /lift_word /=.
    iAssert (interp W C (wsrc @@? πs)) as "#Hwsrc".
    { destruct (decide (rsrc = cnull)) as [->|Hnull].
      + rewrite /llookup_reg in Hrsrc. apply bind_Some in Hrsrc as (? & _ & Hw).
        injection Hw as <- <-. by iApply interp_untagged.
      + rewrite llookup_reg_not_cnull // in Hrsrc.
        iApply "Hreg"; eauto. }

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    destruct (updatePcPerm wsrc) as
      [z | [t0 p0 g0 b0 e0 a0 | t0 sp0 g0 b0 e0 a0] | k0 t0 p0 g0 b0 e0 a0 | ot sb]
      eqn:Hwsrc; cycle 1.
    { destruct t0; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply (ftlr_trap with "Htrap Hreg' Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
      }
      destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        iApply (ftlr_trap with "Htrap Hreg' Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
      }

      destruct_word wsrc; try destruct t; cbn in Hwsrc; try discriminate.
      { destruct c; inv Hwsrc.
        iNext ; iIntros "_".
        iApply ("IH" $! _ _ _ _ _ regs' with
                 "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$]") ; eauto.
      }
      inv Hwsrc.
      iEval (rewrite interp_unfold) in "Hwsrc".
      simpl; rewrite /enter_cond.
      iDestruct "Hwsrc" as "[%Hnonheap #Hinterp_src]".
      iAssert (future_world g0 W W) as "Hfuture".
      { iApply futureworld_refl. }
      iSpecialize ("Hinterp_src" with "Hfuture").
      pose proof (LocalityFlowsToReflexive g0) as Hg0.
      iSpecialize ("Hinterp_src" $! g0 Hg0).
      iNext. iIntros "_".
      iApply ("Hinterp_src" $! cstk Ws Cs regs'
               with "[$HPC $Hmap $Hworld_interp $Htframe $Hown $Hcont $Htop]").
      iSplit; last done.
      iSplit.
      + iIntros (ri); cbn; iPureIntro. apply Hsome'.
      + iIntros (ri wi Hregs_ri). iApply interp_filter_heap. by iApply "Hreg'".
    }

    (* Non-capability cases *)
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: iApply (ftlr_trap with "Htrap Hreg' Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto.
  Qed.

End fundamental.
