From stdpp Require Import base.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Export logrel_binary.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import rules_UnSeal rules_UnSeal_binary.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType (Word * Word) Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO (Word * Word)) -n> iPropO Σ).
  Implicit Types interp : (V).

  (* Proving the meaning of unsealing in the LR sane. Note the use of the later in the result.
     Related sealed words are equal, so the unsealed payloads are equal too. *)
  Lemma unsealing_preserves_interp W C sb p0 g0 b0 e0 a0 o s:
        permit_unseal p0 = true →
        withinBounds b0 e0 o = true →
        interp W C (WSealed o sb, WSealed o sb) -∗
        interp W C (WSealRange true p0 g0 b0 e0 a0, WSealRange true p0 g0 b0 e0 a0) -∗
        world_interp_open W C s
        -∗
        ▷ (interp W C (WSealable (machine_word.unseal g0 sb), WSealable (machine_word.unseal g0 sb)) ∗
           world_interp_open W C s).
  Proof.
    iIntros (Hpseal Hwb) "#HVsd #HVsr Hworld_interp".
    destruct (get_tag_sealable sb) eqn:Htag.
    2: { iNext. iFrame. iApply interp_untagged. by rewrite /= get_tag_unseal Htag. }
    rewrite interp_sealed_inv // (interp_diag_eq _ _ (WSealRange _ _ _ _ _ _)) //.
    rewrite /interp1_diag /= Hpseal /interp_sb.
    iDestruct "HVsr" as "[_ Hss]".
    apply seq_between_dist_Some in Hwb.
    iDestruct (big_sepL_delete with "Hss") as "[HSa0 _]"; eauto.
    iDestruct "HSa0" as (P) "(%Hpers & HsealP & %Hdom & Hrcond)".
    assert (∀ WCv : WORLD * CmptName * (Word * Word), Persistent (safeC P WCv)) as Hpers'.
    { intros [ [W0 C0] w0 ]; rewrite //=; eapply (Hpers (W0, C0, w0)). }
    iDestruct "HVsd" as "[_ [%Hloc HVsd]]".
    iAssert (sts_seals_std C o {[(WSealable sb, WSealable sb)]}) as "#HVsd'".
    { iApply sts_seals_std_weaken; last iFrame "HVsd"; set_solver+. }
    iDestruct (world_interp_open_seal_pred_singleton with "HsealP HVsd' Hworld_interp")
      as "(Hworld_interp & #HP)".
    iNext.
    iFrame.
    destruct g0.
    - rewrite unseal_global. by iApply "Hrcond".
    - rewrite unseal_local.
      iApply (interp_borrow_word W C (WSealable sb, WSealable sb)). by iApply "Hrcond".
  Qed.

  Lemma unseal_case (W : WORLD) (C : CmptName) (regs1 regs2 : Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:V)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs1 regs2 p p' g b e a w (UnSeal dst r1 r2) ρ P stk Ws Cs.
  Proof.
    intros Hp HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi; rewrite /ftlr_post.
    iIntros "#IH #Hspec #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe
      Hworld_interp Hown Htframe Htframe_spec Hstate Hj Hmap Hsmap".
    iDestruct (interp_reg_full_map_1 with "Hreg") as %Hsome1.
    iDestruct (interp_reg_full_map_2 with "Hreg") as %Hsome2.
    iDestruct (WorldRes_acc with "WorldRes") as "[ (Ha & >Hsa & Hinterp) WorldRes ]".

    iMod (step_UnSeal with "[$Hspec $Hj $Hsa $Hsmap]")
      as (retv2 regs2') "(Hj & %HSpec2 & Hsa & Hsmap)"; eauto.
    { by simplify_map_eq. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iApply (wp_UnSeal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ p0 g0 b0 e0 a0 o sb Hr1 Hr2 Htag Hunseal Hwb HincrPC
                      | t0 p0 g0 b0 e0 a0 o sb Hr1 Hr2 Hvalid HincrPC
                      | ]; cycle 2.
    { ftlr_impl_fail. }

    (* The sealing capability and the sealed word are the same in both runs *)
    all: iDestruct (interp_reg_lookup_same with "Hinv_interp Hreg") as %Hr1'; [exact Hr1|done|].
    all: iDestruct (interp_reg_lookup_Some _ _ _ _ (WCap true p g b e a) r2 with "Hreg") as %[w2 Hr2'].
    all: iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#HVsr"; [exact Hr1|exact Hr1'|].
    all: iDestruct (interp_reg_lookup with "Hinv_interp Hreg") as "#HVsd"; [exact Hr2|exact Hr2'|].
    all: iDestruct (interp_eq with "HVsd") as %<-.
    all: apply incrementPC_Some_inv in HincrPC as (t2&p2&g2&b2&e2&a2&a3&HPC&Ha2&->).
    1: eapply UnSeal_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply UnSeal_spec_success; eauto; transfer_incrementPC HPC Ha2).
    2: eapply UnSeal_spec_determ in HSpec2 as [Hv2 Hregs2];
       last (eapply UnSeal_spec_invalidated; eauto; transfer_incrementPC HPC Ha2).
    all: specialize (Hregs2 eq_refl); subst retv2 regs2'.

    2: { (* The unsealed word is untagged *)
      iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
      iApply wp_pure_step_later; auto; iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      { assert (t2 = false) as ->.
        { rewrite /insert_reg lookup_insert_eq in HPC.
          destruct sb; cbn in HPC; simplify_eq; done. }
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
        iApply interp_untagged; cbn; apply get_tag_clear_tag_sealable.
      - iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    (* Unsealing yields a safe payload *)
    iDestruct (unsealing_preserves_interp with "HVsd HVsr Hworld_interp")
      as "[#HVsb Hworld_interp]"; auto.
    iMod (step_seq_nexti with "Hspec Hj") as "Hj"; first solve_ndisj.
    iApply wp_pure_step_later; auto; iNext; iIntros "_".
    iDestruct ("WorldRes" with "[$Ha $Hsa $Hinterp]") as "WorldRes".
    iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
    { destruct ρ;auto;contradiction. }

    destruct (decide (dst = PC)) as [->|HdstPC].
    - (* The PC is overwritten by the unsealed capability *)
      assert (WSealable (machine_word.unseal g0 sb) = WCap t2 p2 g2 b2 e2 a2) as Hunsb.
      { rewrite /insert_reg lookup_insert_eq in HPC.
        by apply (inj Some) in HPC. }
      assert (t2 = true) as ->.
      { have Hout := get_tag_unseal g0 sb.
        apply (f_equal get_tag) in Hunsb; cbn in Hunsb; congruence. }
      rewrite Hunsb.
      iApply ("IH" $! _ _ _ _ _ (<[PC:=_]ᵣ> _) (<[PC:=_]ᵣ> _)
               with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      + iApply (interp_reg_insert _ _ _ _ PC (WCap true p2 g2 b2 e2 a2) (WCap true p2 g2 b2 e2 a2) with "[]")
        ; first by iApply interp_reg_insert_PC.
        by iIntros (?).
      + iModIntro; iApply (interp_weakening with "IH HVsb"); eauto; try solve_addr; try reflexivity.
    - rewrite insert_reg_lookup_PC // in HPC; simplify_map_eq.
      iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) (<[dst:=_]ᵣ> _)
               with "Hspec [] Hmap Hsmap Hj Hworld_interp Hcont [//] Hown Htframe Htframe_spec"); eauto.
      + iApply (interp_reg_insert with "[]"); first by iApply interp_reg_insert_PC.
        by iIntros.
      + iModIntro; iApply (interp_next_PC with "Hinv_interp"); eauto.
  Qed.

End fundamental.
