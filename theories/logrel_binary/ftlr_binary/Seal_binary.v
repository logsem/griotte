From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_Seal rules_Seal_binary.
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

  (* Proving the meaning of sealing in the LR sane *)
  Lemma sealing_preserves_interp W C sb p0 g0 b0 e0 a0:
        permit_seal p0 = true →
        withinBounds b0 e0 a0 = true →
        interp W C (WSealable sb, WSealable sb) -∗
        interp W C (borrow (WSealable sb), borrow (WSealable sb)) -∗
        interp W C (WSealRange p0 g0 b0 e0 a0, WSealRange p0 g0 b0 e0 a0) -∗
        interp W C (WSealed a0 sb, WSealed a0 sb).
  Proof.
    iIntros (Hpseal Hwb) "#HVsb #HVsb_borrowed #HVsr".
    rewrite interp_sealed_inv (interp_diag_eq _ _ (WSealRange _ _ _ _ _)) //.
    rewrite /interp1_diag /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "(% & #Hmono & HsealP & HWcond)".
    iSplit; first done.
    iExists P.
    repeat iSplitR; auto; by iApply "HWcond".
  Qed.

  Lemma seal_case (W : WORLD)(C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (Seal dst r1 r2) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_Seal with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ p0 g0 b0 e0 a0 sb Hr1 Hr2 Hseal Hwb HincrPC | ]; cycle 1.
    { ftlr_impl_fail. }

    (* The specification run performs the same update *)
    iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hr1'; [exact Hr1|done|].
    iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hr2'; [exact Hr2|done|].
    apply incrementPC_Some_inv in HincrPC as (p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
    eapply Seal_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply Seal_spec_success; eauto; transfer_incrementPC HPC Ha2).
    specialize (Hregs2 eq_refl); subst retv2 regs2'.

    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#HVsr"; [exact Hr1|exact Hr1'|].
    iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#HVsb"; [exact Hr2|exact Hr2'|].
    iDestruct (interp_borrow_word _ _ (_,_) with "HVsb") as "#HVsb_borrowed".

    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    assert (dst ≠ PC) as HdstPC.
    { intros ->; rewrite /insert_reg in HPC; simplify_map_eq. }
    rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
    iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
    - iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
      iIntros (_ Hdstnull).
      iApply (sealing_preserves_interp with "HVsb HVsb_borrowed HVsr"); eauto.
    - iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
