From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import memory_region map_simpl.
From griotte Require Import rules_base rules_Restrict.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Lemma PermPairFlows_interp_preserved W C t p p' g g' b e a :
    PermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WCap t p g b e a) -∗
    interp W C (WCap t p' g' b e a).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening with "IH HA");eauto;try solve_addr.
  Qed.

  Lemma SealPermPairFlows_interp_preserved W C t p p' g g' b e a :
    SealPermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    ftlr_IH -∗
    interp W C (WSealRange t p g b e a) -∗
    interp W C (WSealRange t p' g' b e a).
  Proof.
    intros Hp Hg. iIntros "#IH HA".
    iApply (interp_weakening_ot with "HA");eauto;try solve_addr.
  Qed.

  Lemma restrict_case (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst : RegName) (src : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Restrict dst src) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Restrict with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hdst Hz Hpair HPfl HLfl HincrPC
                      | * Hdst Hz Hpair HPfl HLfl HincrPC
                      | * Hdst Hz Hpair Hflows HincrPC
                      | * Hdst Hz Hpair Hflows HincrPC
                      | ].
    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      assert (HPCsrc: match src with inl _ => True | inr src => PC <> src end).
      { destruct src; auto.
        intro; subst r. simplify_map_eq. }

      destruct (decide (PC=dst)) as [HdstPC|HdstPC].
      { subst dst.
        repeat rewrite insert_insert_eq in HPC.
        rewrite lookup_insert_eq in HPC. inv HPC.

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        destruct (executeAllowed p'') eqn:Hpft.
        {
          simplify_map_eq ; map_simpl "Hmap".
          iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          iModIntro.
          iApply (PermPairFlows_interp_preserved); eauto.
          iApply (interp_next_PC with "Hinv_interp"); eauto.
        }
        { iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC with "HPC"); [eapply not_isCorrectPC_perm; simpl in Hpft; eauto; discriminate|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto. iNext ; iIntros "_".
          iApply wp_value;auto. }
      }
      {
        simplify_map_eq.

        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }

        assert (is_Some (<[dst:=WCap t p'0 g' b0 e0 a0]> (<[PC:=WCap true p'' g'' b'' e'' a'']> regs) !! csp)) as [??].
        { destruct (decide (dst = csp)); simplify_map_eq=>//. }
        iApply ("IH" $! _ _ _ _ _ (<[dst:=_]> _) with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        - intros; simpl. repeat (rewrite lookup_insert_is_Some'; right); eauto.
        - iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          + subst ri. simplify_map_eq.
            destruct (decodePermPair n) as (p1 & g1); simplify_eq.
            destruct (decide (dst = cnull)); simplify_map_eq; [iApply interp_int|].
            iDestruct ("Hreg" $! dst _ Hri Hdst) as "Hdst".
            iApply PermPairFlows_interp_preserved; eauto.
          + simplify_map_eq. iApply "Hreg"; auto.
        - iApply (interp_next_PC with "Hinv_interp"); eauto.
      }

    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      iApply wp_pure_step_later; auto. iNext; iIntros "_".

      assert (HPCsrc: match src with inl _ => True | inr src => PC <> src end).
      { destruct src; auto.
        intro; subst r. simplify_map_eq. }

      destruct (decide (PC=dst)) as [HdstPC|HdstPC].
      { subst dst. repeat rewrite insert_insert_eq.
        repeat rewrite insert_insert_eq in HPC.
        rewrite lookup_insert_eq in HPC. inv HPC.
      }

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      simplify_map_eq; map_simpl "Hmap".
      rewrite insert_reg_insert_commute; auto.
      simplify_map_eq; map_simpl "Hmap".
      assert (is_Some (<[dst:=WSealRange t p'0 g' b0 e0 a0]ᵣ> regs !! csp)) as [??].
      { destruct (decide (dst = csp)); simplify_map_eq=>//. }
      iApply ("IH" $! _ _ _ _ _ (<[dst:=WSealRange t p'0 g' b0 e0 a0]ᵣ> regs) with
               "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
      + intros. by rewrite lookup_insert_is_Some' ; right.
      + iIntros (ri v Hri Hvs).
        destruct (decide (ri = dst)).
        * subst ri. simplify_map_eq.
          destruct (decodeSealPermPair n) as (p1 & g1); simplify_eq.
          destruct (decide (dst = cnull)); simplify_map_eq; [iApply interp_int|].
          iDestruct ("Hreg" $! dst _ Hri Hdst) as "Hdst".
          iApply SealPermPairFlows_interp_preserved; eauto.
        * simplify_map_eq. iApply "Hreg"; auto.
      + iApply (interp_next_PC with "Hinv_interp"); eauto.

    - match type of HincrPC with
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
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
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

    - match type of HincrPC with
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
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
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

    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
  Qed.

End fundamental.
