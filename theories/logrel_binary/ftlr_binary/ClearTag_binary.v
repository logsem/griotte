From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_ClearTag rules_ClearTag_binary.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType (Word * Word) Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  Lemma cleartag_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst src : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (ClearTag dst src) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_ClearTag with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_ClearTag with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [w1 Hw1 Hincr | w1 Hw1 Hincr ->]; cycle 1.
    { ftlr_impl_fail. }

    (* The specification run reads the same word *)
    iDestruct (interp_reg_lookup_Some _ _ _ _ (WCap true p g b e a) src with "Hreg") as %[w2 Hw2].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "Hw"; [exact Hw1|exact Hw2|].
    iDestruct (interp_eq with "Hw") as %<-.
    apply incrementPC_Some_inv in Hincr as (t2&p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
    eapply ClearTag_spec_determ in HSpec2 as [Hv2 Hregs2];
      last (eapply ClearTag_spec_success; eauto; transfer_incrementPC HPC Ha2).
    specialize (Hregs2 eq_refl); subst retv2 regs2'.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".

    destruct (decide (dst = PC)) as [->|HdstPC].
    { (* The new PC is untagged *)
      assert (t2 = false) as ->.
      { rewrite /insert_reg lookup_insert_eq in HPC.
        apply (inj Some) in HPC.
        pose proof (get_tag_clear_tag w1) as Htag.
        by rewrite HPC in Htag. }
      iApply (wp_bind (fill [SeqCtx])).
      iExtract "Hmap" PC as "HPC".
      iApply (wp_notCorrectPC_tag with "HPC"); first done.
      iNext; iIntros "HPC /=".
      ftlr_impl_fail.
    }

    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }
    rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
    iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
    - iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
      iIntros (_ _).
      iApply interp_clear_tag.
    - iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
