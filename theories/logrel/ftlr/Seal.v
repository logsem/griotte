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

  Lemma seal_case (W : WORLD)(C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (dst r1 r2 : RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr W C regs p p' g b e a w (Seal dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#Halloc #IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
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
    - apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& ? & HPC & Z & Hregs') .
      assert (t'' = true ∧ p'' = p ∧ g'' = g ∧ a'' = a ∧ b'' = b ∧ e'' = e) as (-> & -> & -> & -> & -> & ->).
      { destruct (decide (PC = dst)); simplify_map_eq; naive_solver. }
      assert (r1 ≠ PC) as Hne.
      { destruct (decide (PC = r1)); last auto. simplify_map_eq; auto. }
      assert (r1 ≠ cnull); simplify_map_eq.
      { intros ->; destruct (regs !! cnull) eqn:Hr ; simplify_map_eq. }
      assert (r2 ≠ cnull); simplify_map_eq.
      { intros ->; destruct (regs !! cnull) eqn:Hr ; simplify_map_eq. }

      iAssert (interp W C (WSealable sb)) as "#HVsb".
      { destruct (decide (r2 = PC)) as [Heq|Heq]; simplify_map_eq; first done.
        unshelve iSpecialize ("Hreg" $! r2 _ _ Hr2); eauto.
      }
      iAssert (interp W C (borrow (WSealable sb))) as "#HVsb_borrowed".
      { by iApply interp_borrow_word. }

      iApply wp_pure_step_later; auto; iNext; iIntros "_".

      assert (dst <> PC) as HdstPC by (intros ->; simplify_map_eq).
      simplify_map_eq.

      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      assert (is_Some (<[dst:=WSealed a0 sb]> (<[PC:=WCap true p g b e a]> regs) !! csp)) as [??].
      { destruct (decide (dst = csp)); simplify_map_eq=>//. }

      (* TODO can I extract a lemma from here? *)
      unshelve iDestruct ("Hreg" $! r1 _ _ Hr1) as "HVsr"; eauto.
      iMod (sealing_preserves_interp with "HVsb HVsr Hworld_interp") as
        "(%W' & %Hrelated & %Hheap & Hworld_interp & #HVsb')"; auto.
      eapply frame_match_mono in Hframe; eauto.
      iApply ("IH" $! _ _ _ _ _ (<[dst := _]> (<[PC := _]> regs))
               with "[Halloc] [%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]")
      ; eauto.
      + intro; cbn. by repeat (rewrite lookup_insert_is_Some'; right).
      + iIntros (ri wi Hri Hregs_ri).
        destruct (decide (ri = dst)); simplify_map_eq.
        {
          destruct (decide (dst = cnull)) ; last done.
          iApply interp_int.
        }
        {
          iApply (interp_monotone_same_heap with "[] []"); eauto.
          by iApply "Hreg".
        }
      + iApply (interp_monotone_same_heap with "[] []"); eauto.
        iApply (interp_next_PC with "Hinv_interp"); eauto.

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

    - iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iApply wp_value; auto.
  Qed.

End fundamental.
