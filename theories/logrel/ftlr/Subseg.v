From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import memory_region map_simpl.
From griotte Require Import rules_base rules_Subseg.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma subseg_interp_preserved W C t p g b b' e e' a :
      (b <= b')%a ->
      (e' <= e)%a ->
      ftlr_IH -∗
      interp W C (WCap t p g b e a) -∗
      interp W C (WCap t p g b' e' a).
  Proof.
    intros Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto.
    - destruct p; reflexivity.
    - destruct g; reflexivity.
  Qed.

   Lemma subseg_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : Word)
     (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Subseg dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#Halloc #IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Subseg with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    assert (∀ wdst, is_Some (<[dst := wdst]> regs !! csp)) as Hspdst.
    { intros. destruct (decide (dst = csp));simplify_map_eq=>//. }
    destruct HSpec as [t p0 g0 b0 e0 a0 n1 n2 a1 a2 Hdst Hz1 Hz2 Hao1 Hao2 HincrPC
                      | * Hdst Hz1 Hz2 Hunrep HincrPC
                      | t p0 g0 b0 e0 a0 n1 n2 a1 a2 Hdst Hz1 Hz2 Hoo1 Hoo2 HincrPC
                      | * Hdst Hz1 Hz2 Hunrep HincrPC | ].
    { destruct (isWithin a1 a2 b0 e0) eqn:Hwi.
      { rewrite andb_true_r in HincrPC.
        apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

        assert (t'' = true ∧ a'' = a ∧ p'' = p∧ g'' = g) as (-> & -> & -> & ->).
        { destruct (decide (PC = dst)); simplify_map_eq; auto. }

        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        simplify_map_eq; map_simpl "Hmap".

        (* edestruct Hspdst as [??]. *)
        iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) with "Halloc [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          { subst ri.
            simplify_map_eq.
            destruct (decide (dst = cnull)); simplify_map_eq; first iApply interp_int.
            unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
            rewrite /isWithin in Hwi.
            iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
            - apply PermFlowsToReflexive.
            - apply LocalityFlowsToReflexive.
          }
          { iApply "Hreg"; auto.
            by rewrite lookup_insert_ne in Hvs; auto; simplify_map_eq.
          }
        }
        {
          iModIntro.
          apply isWithin_implies in Hwi.
          destruct Hwi as [Hwi_b Hwi_e].
          destruct (decide (dst = PC))
          ; simplify_map_eq
          ; [iApply subseg_interp_preserved; eauto|]
          ; iApply (interp_next_PC with "Hinv_interp"); eauto.
        }

      }
      { rewrite andb_false_r in HincrPC.
        match type of HincrPC with
        | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
            set (wout := wnew) in HincrPC
        end.
        assert (Htagout : get_tag wout = false).
        { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
        incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        destruct (decide (dst = PC)) as [->|HdstPC].
        + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
          { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
          rewrite Hwout /= in Htagout. subst t0.
          map_simpl "Hmap".
          iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC_tag with "HPC"); first done.
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext; iIntros "_".
          iApply wp_value; auto.
        + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
          rewrite lookup_insert_eq in HPC0.
          injection HPC0 as <- <- <- <- <- <-.
          iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
          iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
          { destruct ρ; auto; contradiction. }
          iApply ("IH" $! _ _ _ _ _
            (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
            with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
          * iIntros (ri wi Hri Hregs_ri).
            destruct (decide (ri = dst)) as [->|Hne].
            { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
              injection Hregs_ri as <-.
              destruct (decide (dst = cnull));
                [iApply interp_int | by iApply interp_untagged]. }
            rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
            iApply "Hreg"; eauto.
          * iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    }

    {
      match type of HincrPC with
      | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
          set (wout := wnew) in HincrPC
      end.
      assert (Htagout : get_tag wout = false).
      { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
      incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
        { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
        rewrite Hwout /= in Htagout. subst t0.
        map_simpl "Hmap".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
        rewrite lookup_insert_eq in HPC0.
        injection HPC0 as <- <- <- <- <- <-.
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
          with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull));
              [iApply interp_int | by iApply interp_untagged]. }
          rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { destruct (isWithin a1 a2 b0 e0) eqn:Hwi.
      { rewrite andb_true_r in HincrPC.
        apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .

        assert (t'' = true ∧ a'' = a ∧ p'' = p∧ g'' = g) as (-> & -> & -> & ->).
        { destruct (decide (PC = dst)); simplify_map_eq; auto. }

        iApply wp_pure_step_later; auto.
        iNext ; iIntros "_".

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        simplify_map_eq; map_simpl "Hmap".

        iApply ("IH" $! _ _ _ _ _ (<[dst:=_]ᵣ> _) with "Halloc [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        { cbn. intros. by repeat (rewrite lookup_insert_is_Some'; right). }
        { iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          { subst ri.
            simplify_map_eq.
            destruct (decide (dst = cnull)); simplify_map_eq; first iApply interp_int.

            unshelve iSpecialize ("Hreg" $! dst _ _ Hdst); eauto.
            rewrite /isWithin in Hwi.
            iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
            - apply SealPermFlowsToReflexive.
            - apply LocalityFlowsToReflexive.
          }
          { iApply "Hreg"; auto.
            by rewrite lookup_insert_ne in Hvs; auto; simplify_map_eq.
          }
        }
        {
          iModIntro.
          apply isWithin_implies in Hwi.
          destruct Hwi as [Hwi_b Hwi_e].
          destruct (decide (dst = PC)) ; simplify_map_eq.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
        }

      }
      { rewrite andb_false_r in HincrPC.
        match type of HincrPC with
        | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
            set (wout := wnew) in HincrPC
        end.
        assert (Htagout : get_tag wout = false).
        { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
        incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        destruct (decide (dst = PC)) as [->|HdstPC].
        + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
          { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
          rewrite Hwout /= in Htagout. subst t0.
          map_simpl "Hmap".
          iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC_tag with "HPC"); first done.
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext; iIntros "_".
          iApply wp_value; auto.
        + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
          rewrite lookup_insert_eq in HPC0.
          injection HPC0 as <- <- <- <- <- <-.
          iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
          iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
          { destruct ρ; auto; contradiction. }
          iApply ("IH" $! _ _ _ _ _
            (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
            with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
          * iIntros (ri wi Hri Hregs_ri).
            destruct (decide (ri = dst)) as [->|Hne].
            { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
              injection Hregs_ri as <-.
              destruct (decide (dst = cnull));
                [iApply interp_int | by iApply interp_untagged]. }
            rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
            iApply "Hreg"; eauto.
          * iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    }

    {
      match type of HincrPC with
      | incrementPC (<[dst := ?wnew]ᵣ> _) = _ =>
          set (wout := wnew) in HincrPC
      end.
      assert (Htagout : get_tag wout = false).
      { by rewrite /wout /= ?get_tag_clear_tag_sealable. }
      incrementPC_inv as (t0 & p0' & g0' & b0' & e0' & a0' & a_next & HPC0 & Ha0 & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + assert (Hwout : wout = WCap t0 p0' g0' b0' e0' a0').
        { rewrite /insert_reg /= lookup_insert /= in HPC0. by simplify_eq. }
        rewrite Hwout /= in Htagout. subst t0.
        map_simpl "Hmap".
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /insert_reg lookup_insert_ne in HPC0; last congruence.
        rewrite lookup_insert_eq in HPC0.
        injection HPC0 as <- <- <- <- <- <-.
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=wout]ᵣ> (<[PC:=WCap true p g b e a]> regs)) p g b e a_next
          with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr. rewrite /insert_reg !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite /insert_reg lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull));
              [iApply interp_int | by iApply interp_untagged]. }
          rewrite /insert_reg !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
