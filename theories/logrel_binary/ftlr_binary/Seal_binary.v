From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary monotone_binary interp_weakening_binary.
From griotte Require Import rules_Seal rules_Seal_binary.
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

  (* Proving the meaning of sealing in the LR sane *)
  Lemma sealing_preserves_interp W C sb p g b e a :
    permit_seal p = true ->
    withinBounds b e a = true ->
    interp W C (WSealable sb, WSealable sb) -∗
    interp W C (WSealRange p g b e a, WSealRange p g b e a) -∗
    world_interp W C
    ==∗
    ∃ W', ⌜ related_sts_pub_world W W' ⌝ ∗
          world_interp W' C ∗
          interp W' C (WSealed a sb, WSealed a sb).
  Proof.
    iIntros (Hseal Hwb) "#HVsb #HVsr Hworld_interp".
    rewrite (interp_diag_eq _ _ (WSealRange _ _ _ _ _)) //.
    rewrite /interp1_diag /= Hseal.
    iDestruct "HVsr" as "[Hss _]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_elem_of_acc with "Hss") as "[HSa0 _]"; eauto.
    { rewrite list_elem_of_lookup; eauto. }
    iDestruct "HSa0" as "(%Po & %HPo_pers & Hsealpred & %Ha0_in_Wseals & #Hwcond_Po)".
    rewrite elem_of_dom in Ha0_in_Wseals; destruct Ha0_in_Wseals as [ws Hws].
    set (new_seals_words :=
           ({[(WSealable sb, WSealable sb); borrow_pair (WSealable sb, WSealable sb)]}
             : gset (Word * Word))).
    set ( W' := <o[ a := ( new_seals_words ∪ ws) ]o> W ).
    assert (related_sts_pub_world W W') as Hrelated.
    { by apply related_sts_pub_world_update_ot. }
    iAssert ([∗ set] w0 ∈ normalise_sealed_words new_seals_words, ▷ (safeC Po) (W', C, w0))%I
      as "Hws".
    { subst new_seals_words.
      rewrite normalise_sealed_words_borrow big_sepS_singleton.
      iNext; iApply "Hwcond_Po".
      iApply (interp_monotone with "[%] [$HVsb]"); eauto.
    }
    iMod (world_interp_sealing_update with "Hsealpred Hws Hworld_interp")
      as "(Hworld_interp & #Hstd_seals)"; eauto.
    subst W'.
    iModIntro.
    iExists _; iFrame "∗%".
    rewrite interp_sealed_inv /interp_sb.
    iSplit; first done.
    iSplit; first done.
    iApply sts_seals_std_weaken; last iFrame "#".
    set_solver+.
  Qed.

  Lemma interp_reg_monotone W W' C regs1 regs2 :
    related_sts_pub_world W W' ->
    interp_reg interp W C (regs1, regs2) -∗
    interp_reg interp W' C (regs1, regs2).
  Proof.
    iIntros (Hrelated) "#(%Hfull1 & %Hfull2 & Hreg)".
    iSplit; first done.
    iSplit; first done.
    iIntros (r v1 v2 Hr Hv1 Hv2).
    iApply (interp_monotone with "[%] [-]"); eauto.
    by iApply "Hreg".
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

    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    assert (dst ≠ PC) as HdstPC.
    { intros ->; rewrite /insert_reg in HPC; simplify_map_eq. }
    rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
    iMod (sealing_preserves_interp with "HVsb HVsr Hworld_interp")
      as "(%W' & %Hrelated & Hworld_interp & #HVsb')"; eauto.
    eapply frame_match_mono in Hframe; eauto.
    iApply ("IH" $! W' _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
             with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
    - iApply (interp_reg_insert with "[]").
      { iApply interp_reg_insert_PC.
        iApply (interp_reg_monotone with "Hreg"); eauto. }
      by iIntros (_ Hdstnull).
    - iModIntro; iApply (interp_monotone with "[%] [-]"); eauto.
      iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
