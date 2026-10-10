From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base monotone interp_weakening.
From griotte Require Import rules_base rules_Seal.
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

  Lemma seal_case (W : WORLD)(C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Seal dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    iApply (wp_Seal with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq /set_subseteq_instance. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "[Ha Hmap]".
    destruct HSpec as [ * Hr1 Hr2 Htag Hseal Hwb HincrPC
                      | * Hr1 Hr2 Hvalid HincrPC | ].
    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      rewrite /linsert_reg in HPC.
      destruct (decide (PC = dst)) as [<-|HdstPC].
      { rewrite lookup_insert_eq in HPC. simplify_eq. }
      rewrite lookup_insert_ne // lookup_insert_eq in HPC.
      injection HPC as <- <- <- <- <- <- <-.
      iEval (rewrite /linsert_reg) in "Hmap".
      assert (r1 ≠ PC) as Hne.
      { intros ->. rewrite llookup_reg_not_cnull // lookup_insert_eq in Hr1. simplify_eq. }
      assert (r1 ≠ cnull) as Hr1null.
      { intros ->. rewrite /llookup_reg in Hr1. apply bind_Some in Hr1 as (? & _ & Hw). simplify_eq. }
      assert (r2 ≠ cnull) as Hr2null.
      { intros ->. rewrite /llookup_reg in Hr2. apply bind_Some in Hr2 as (? & _ & Hw). simplify_eq. }
      rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hr1.

      (* The sealed payload keeps its identifier. *)
      iAssert (interp W C (WSealable sb @@? π)) as "#HVsb".
      { destruct (decide (r2 = PC)) as [->|Heq].
        - rewrite llookup_reg_not_cnull // lookup_insert_eq in Hr2.
          injection Hr2 as <- <-. iExact "Hinv_interp".
        - rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hr2. iApply "Hreg"; eauto. }

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iDestruct ("Hreg" $! r1 _ Hne Hr1) as "HVsr".
      iMod (sealing_preserves_interp with "HVsb HVsr Hworld_interp") as
        "(%W' & %Hrelated & %Hheap & Hworld_interp & #HVsb')"; auto.
      eapply frame_match_mono in Hframe; eauto.
      iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WSealed a0 sb @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
               with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)) as [->|Hne'].
        { rewrite lookup_insert_eq in Hregs_ri. injection Hregs_ri as <-.
          destruct (decide (dst = cnull)); [by iApply interp_untagged | iExact "HVsb'"]. }
        rewrite !lookup_insert_ne // in Hregs_ri.
        iApply (interp_monotone_same_heap with "[] []"); eauto.
        by iApply "Hreg".
      + iApply (interp_monotone_same_heap with "[] []"); eauto.
        iApply (interp_next_PC with "Hinv_interp"); eauto.

    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WSealed a0 (clear_tag_sealable sb) @@? π]>
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

    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
  Qed.

End fundamental.
