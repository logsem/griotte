From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import memory_region map_simpl.
From griotte Require Import rules_base rules_Subseg rules_registry.
From griotte Require Import map_simpl register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (D).

  Lemma subseg_interp_preserved W C t p g b b' e e' a :
      (b <= b')%a ->
      (e' <= e)%a ->
      ftlr_IH -∗
      interp W C (WCap t p g b e a) -∗
      interp W C (WCap t p g b' e' a).
  Proof.
    intros Hb He. iIntros "#IH Hinterp".
    iApply (interp_weakening with "IH Hinterp"); eauto; try apply subseg_heap_base_noid.
    - destruct p; reflexivity.
    - destruct g; reflexivity.
  Qed.

   Lemma subseg_case (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
     (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
     (ρ : region_type) (dst src : RegName) (r1 r2 : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr_old trusted_fault W C regs p p' g b e a w (Subseg dst src r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "@".

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    (* A valid source without an identifier stays clear of the heap, so the
       pure branch of the Subseg rule applies. *)
    iAssert (⌜∀ r t p0 g0 b0 e0 a0,
               regs !!ₗ r = Some (WCap t p0 g0 b0 e0 a0 @@? None) →
               t = true → (b0 < e0)%a → disjoint_from_heap b0 e0⌝)%I as %Hnoid.
    { iIntros (r t0 p0 g0 b0 e0 a0 Hr -> Hlt).
      iAssert (interp W C (Cap p0 g0 b0 e0 a0 @@? None)) as "Hr".
      { destruct (decide (r = cnull)) as [->|Hnull].
        + rewrite llookup_reg_cnull /lnull in Hr. simplify_eq.
        + rewrite llookup_reg_not_cnull // in Hr. iApply "Hreg"; eauto. }
      iDestruct (interp_cap_heap_conditions with "Hr") as %[Hvalid _].
      iPureIntro. exact (Hvalid Hlt). }
    assert (subseg_root_free regs src r1 r2) as Hroot.
    { intros t0 p0 g0 b0 e0 a0 a1 a2 Hsrc Ha1 Ha2 Ht Hlt.
      apply andb_true_iff in Ht as [Ht Hle]. apply andb_true_iff in Ht as [-> Hwi].
      apply isWithin_implies in Hwi.
      specialize (Hnoid _ _ _ _ _ _ _ Hsrc eq_refl ltac:(solve_addr)).
      apply not_true_is_false. intros Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hnoid.
      apply (Hnoid a1); apply elem_of_finz_seq_between; [solve_addr|].
      by apply withinBounds_true_iff in Hheap. }
    (* A narrowed capability with an identifier keeps a heap base. *)
    iMod (observe_regs_prov_heap with "Hmap") as "[Hmap %Hprovheap]".

    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ _ None with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & _ & Hmap)".
    clear Hnoid Hroot.
    destruct HSpec as [t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hsrc Hz1 Hz2 Hao1 Hao2 HincrPC Hregs'
                      | * Hsrc Hz1 Hz2 Hunrep HincrPC Hregs'
                      | t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hsrc Hz1 Hz2 Hoo1 Hoo2 HincrPC Hregs'
                      | * Hsrc Hz1 Hz2 Hunrep HincrPC Hregs'
                      | * Hsrc Hk HincrPC Hregs' | Hfail ].
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        rewrite -andb_assoc.
        destruct (isWithin a1 a2 b0 e0 && (a1 <=? a2)%a) eqn:Hwi;
          last (rewrite andb_false_r; by iApply interp_untagged).
        rewrite andb_true_r.
        apply andb_true_iff in Hwi as [Hwi Hle].
        apply isWithin_implies in Hwi as [Hwi_b Hwi_e].
        destruct t; [|by iApply interp_untagged].
        assert (src ≠ cnull) as Hsrc_cnull
          by (eapply llookup_reg_not_zero_not_cnull; [exact Hsrc | done]).
        rewrite llookup_reg_not_cnull // in Hsrc.
        iSpecialize ("Hreg" $! src _ Hsrc).
        iApply (interp_weakening with "IHnew Hreg"); auto; try solve_addr.
        + intros ι -> _ Hlt.
          eapply (Hprovheap src _ ι b0 e0 Hsrc); [done|done|solve_addr|done|solve_addr].
        + apply PermFlowsToReflexive.
        + apply LocalityFlowsToReflexive.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        by iApply interp_untagged.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        destruct (isWithin a1 a2 b0 e0) eqn:Hwi;
          last (rewrite andb_false_r; by iApply interp_untagged).
        rewrite andb_true_r.
        assert (src ≠ cnull) as Hsrc_cnull
          by (eapply llookup_reg_not_zero_not_cnull; [exact Hsrc | done]).
        rewrite llookup_reg_not_cnull // in Hsrc.
        iSpecialize ("Hreg" $! src _ Hsrc).
        rewrite /isWithin in Hwi.
        iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
        + apply SealPermFlowsToReflexive.
        + apply LocalityFlowsToReflexive.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (Hdst_null).
        by iApply interp_untagged.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { (* The destination loses its tag. *)
      apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - subst regs'. by apply full_map_linsert.
      - subst regs'. iApply (interp_linsert with "Hreg"). iIntros (_).
        iApply interp_clear_tag.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { assert (regs' = regs) as -> by (destruct Hfail; done).
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto. }
  Qed.

End fundamental.
