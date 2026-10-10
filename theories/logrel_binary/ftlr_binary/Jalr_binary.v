From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_base rules_Jalr rules_Jalr_binary.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Lemma jalr_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (rdst rsrc : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Jalr rdst rsrc) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Jalr with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Jalr with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ regs' pc_a' wsrc Hrsrc Hpca' ->| Hpca' ]; cycle 1.
    { ftlr_impl_fail. }

    (* The specification run jumps to a related word *)
    iDestruct (interp_reg_lookup_Some _ _ _ _ (WCap p g b e a) rsrc with "Hreg") as %[wsrc2 Hrsrc2].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#Hwsrc"; [exact Hrsrc|exact Hrsrc2|].
    eapply Jalr_spec_determ in HSpec2 as [Hv2 Hregs2];
      last (eapply Jalr_spec_success; eauto).
    specialize (Hregs2 eq_refl); subst retv2 regs2'.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.

    iAssert (interp W C (WSentry p g b e pc_a', WSentry p g b e pc_a')) as "Hinterp_ret".
    {
      iApply (interp_weakeningSentry with "IH Hinv_interp");eauto;try solve_addr.
      - destruct Hp as [Hexec _].
        by apply executeAllowed_nonO.
      - reflexivity.
    }

    iApply wp_pure_step_later; auto.

    destruct (decide (rdst = PC)) as [HPC_dst|HPC_dst]; simplify_eq.
    { iNext; iIntros "_".
      iApply (wp_bind (fill [SeqCtx])).
      rewrite /insert_reg; simplify_map_eq.
      iExtract "Hmap" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
      iNext; iIntros "HPC /=".
      ftlr_impl_fail.
    }

    rewrite !insert_reg_insert !insert_reg_PC !insert_reg_insert_commute //.
    iDestruct (interp_eq_unless_sealed with "Hwsrc") as %[<-|(o & sb1 & sb2 & -> & ->)]; cycle 1.
    { (* Sealed words are not valid program counters *)
      iNext; iIntros "_".
      iApply (wp_bind (fill [SeqCtx])).
      iExtract "Hmap" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
      iNext; iIntros "HPC /=".
      ftlr_impl_fail.
    }

    iAssert (interp_reg interp W C (<[rdst:=WSentry p g b e pc_a']ᵣ> regs1,
                                    <[rdst:=WSentry p g b e pc_a']ᵣ> regs2)) as "#Hreg'".
    { iApply (interp_reg_insert with "Hreg"); by iIntros. }

    destruct (updatePcPerm wsrc) eqn:Hwsrc ; [ | destruct sb | | ]; cycle 1.
    { destruct (executeAllowed p0) eqn:Hpft; cycle 1.
      { iNext; iIntros "_".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; naive_solver|].
        iNext; iIntros "HPC /=".
        ftlr_impl_fail.
      }

      iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      destruct_word wsrc; cbn in Hwsrc; try discriminate.
      { (* Jump to a capability *)
        destruct c; inv Hwsrc.
        iNext ; iIntros "_".
        iApply ("IH" $! _ _ _ _ _ (<[rdst:=WSentry p g b e pc_a']ᵣ> regs1) (<[rdst:=WSentry p g b e pc_a']ᵣ> regs2)
                 with "Hspec Hreg' Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec") ; eauto.
      }
      (* Jump to a sentry *)
      iEval (rewrite interp_diag_eq //) in "Hwsrc".
      rewrite /interp1_diag /=; rewrite /enter_cond.
      iDestruct "Hwsrc" as "#Hinterp_src".
      inv Hwsrc.
      iSpecialize ("Hinterp_src" $! W with "[]"); first iApply futureworld_refl.
      iSpecialize ("Hinterp_src" $! _ (LocalityFlowsToReflexive _)).
      iDestruct ("Hinterp_src" with "[$Hspec $Hreg' $Hmap $Hsmap $Hj $Hworld_interp $Htframe $Htframe_spec $Hown $Hcont]") as "HA"; eauto.
    }

    (* Non-capability cases *)
    all: iExtract "Hmap" PC as "HPC".
    all: iNext; iIntros "_".
    all: iApply (wp_bind (fill [SeqCtx])).
    all: iApply (wp_notCorrectPC with "HPC"); [intro Hcontra ; inv Hcontra|].
    all: iNext; iIntros "HPC /=".
    all: ftlr_impl_fail.
  Qed.

End fundamental.
