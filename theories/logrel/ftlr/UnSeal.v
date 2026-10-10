From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import rules_base rules_UnSeal.
From griotte Require Import map_simpl register_tactics.

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
  Lemma unseal_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (UnSeal dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_UnSeal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Htag Hunseal Hwb HincrPC
                      | * Hr1 Hr2 Hvalid HincrPC | ].
    {
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iEval (rewrite /linsert_reg) in "Hmap".
      rewrite /linsert_reg in HPC.

      assert (r1 ≠ PC) as Hne1.
      { intros ->. rewrite llookup_reg_not_cnull // lookup_insert_eq in Hr1. simplify_eq. }
      assert (r2 ≠ PC) as Hne2.
      { intros ->. rewrite llookup_reg_not_cnull // lookup_insert_eq in Hr2. simplify_eq. }
      assert (r1 ≠ cnull) as Hr1null.
      { intros ->. rewrite /llookup_reg in Hr1. apply bind_Some in Hr1 as (? & _ & Hw). simplify_eq. }
      assert (r2 ≠ cnull) as Hr2null.
      { intros ->. rewrite /llookup_reg in Hr2. apply bind_Some in Hr2 as (? & _ & Hw). simplify_eq. }
      rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hr1.
      rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hr2.

      iDestruct ("Hreg" $! r1 _ Hne1 Hr1) as "HVsr".
      iDestruct ("Hreg" $! r2 _ Hne2 Hr2) as "HVsd".
      (* Generate interp instance before step, so we get rid of the later *)
      iDestruct (unsealing_preserves_interp with "HVsd HVsr Hworld_interp")
        as "(#HVsb & Hworld_interp)"; auto.

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      destruct (decide (PC = dst)) as [Heq | Hne]; cycle 1.
      { (* PC ≠ dst *)
        rewrite lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WSealable (machine_word.unseal g0 sb) @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
                 with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
        ; eauto.
        + cbn; intros. by repeat (rewrite lookup_insert_is_Some'; right).
        + iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          { subst ri.
            rewrite lookup_insert_eq in Hvs; injection Hvs as <-.
            destruct (decide (dst = cnull)) ; [by iApply interp_untagged | done].
          }
          { rewrite !lookup_insert_ne // in Hvs.
            iApply "Hreg"; auto.
          }
        + iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
      { (* PC = dst *)
        subst dst.
        rewrite lookup_insert_eq in HPC. injection HPC as HPC <-.
        rewrite !insert_insert_eq.
        iEval (rewrite HPC) in "HVsb".
        assert (t'' = true) as ->.
        { have Hout := get_tag_unseal g0 sb. by rewrite HPC /= Htag in Hout. }
        destruct (executeAllowed p'') eqn:Hpft.
        - iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
          ; eauto.
          iApply (interp_weakening with "IH HVsb"); eauto; try solve_addr; try done;
            try apply subseg_heap_base_same.
        - (* not executable *)
          iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC with "HPC")
          ; [eapply not_isCorrectPC_perm;  simpl in Hp; try discriminate; eauto|].
          iNext. iIntros "HPC /=".
          iApply wp_pure_step_later; auto;iNext; iIntros "_".
          iApply wp_value;auto.
      }
    }

    {
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC.
        injection HPC as HPC _.
        have Hout := get_tag_clear_tag_sealable (machine_word.unseal g0 sb).
        rewrite HPC /= in Hout. subst t''.
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull
                  else WSealable (clear_tag_sealable (machine_word.unseal g0 sb)) @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); iApply interp_untagged; first done.
            by rewrite /= get_tag_clear_tag_sealable. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    {
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
    }
  Qed.

End fundamental.
