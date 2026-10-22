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
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
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
     (ρ : region_type) (dst : RegName) (r1 r2 : Z + RegName) (P:D) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) :
    ftlr_instr trusted_fault W C regs p p' g b e a w (Subseg dst r1 r2) ρ P cstk Ws Cs.
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
      iAssert (interp W C (WCap true p0 g0 b0 e0 a0 @@? None)) as "Hr".
      { destruct (decide (r = cnull)) as [->|Hnull].
        + rewrite /llookup_reg in Hr. apply bind_Some in Hr as (? & _ & Hw). simplify_eq.
        + rewrite llookup_reg_not_cnull // in Hr. iApply "Hreg"; eauto. }
      iDestruct (interp_cap_heap_conditions with "Hr") as %[Hvalid _].
      iPureIntro. exact (Hvalid Hlt). }
    assert (subseg_root_free regs dst r1 r2) as Hroot.
    { intros t0 p0 g0 b0 e0 a0 a1 a2 Hdst Ha1 Ha2 Ht Hlt.
      apply andb_true_iff in Ht as [Ht Hle]. apply andb_true_iff in Ht as [-> Hwi].
      apply isWithin_implies in Hwi.
      specialize (Hnoid _ _ _ _ _ _ _ Hdst eq_refl ltac:(solve_addr)).
      apply not_true_is_false. intros Hheap.
      rewrite /disjoint_from_heap elem_of_disjoint in Hnoid.
      apply (Hnoid a1); apply elem_of_finz_seq_between; [solve_addr|].
      by apply withinBounds_true_iff in Hheap. }
    (* A narrowed capability with an identifier keeps a heap base. *)
    iMod (observe_regs_prov_heap with "Hmap") as "[Hmap %Hprovheap]".

    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ None with "[$HPC $Ha $Hmap]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & _ & Hmap)".
    clear Hnoid Hroot.
    destruct HSpec as [t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hdst Hz1 Hz2 Hao1 Hao2 HincrPC Hregs'
                      | * Hdst Hz1 Hz2 Hunrep HincrPC Hregs'
                      | t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hdst Hz1 Hz2 Hoo1 Hoo2 HincrPC Hregs'
                      | * Hdst Hz1 Hz2 Hunrep HincrPC Hregs'
                      | * Hdst Hk HincrPC Hregs' | Hfail ].
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          rewrite -andb_assoc.
          destruct (isWithin a1 a2 b0 e0 && (a1 <=? a2)%a) eqn:Hwi;
            last (rewrite andb_false_r; by iApply interp_untagged).
          rewrite andb_true_r.
          apply andb_true_iff in Hwi as [Hwi Hle].
          apply isWithin_implies in Hwi as [Hwi_b Hwi_e].
          destruct t; [|by iApply interp_untagged].
          rewrite llookup_reg_not_cnull // in Hdst.
          iSpecialize ("Hreg" $! dst _ Hdst).
          iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
          - intros ι -> _ Hlt.
            eapply (Hprovheap dst _ ι b0 e0 Hdst); [done|done|solve_addr|done|solve_addr].
          - apply PermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          by iApply interp_untagged.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          destruct (isWithin a1 a2 b0 e0) eqn:Hwi;
            last (rewrite andb_false_r; by iApply interp_untagged).
          rewrite andb_true_r.
          rewrite llookup_reg_not_cnull // in Hdst.
          iSpecialize ("Hreg" $! dst _ Hdst).
          rewrite /isWithin in Hwi.
          iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
          - apply SealPermFlowsToReflexive.
          - apply LocalityFlowsToReflexive.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Ha_next & ->).
      injection HPC as <- <- <- <- <- <- <-.
      iApply wp_pure_step_later; auto. iNext; iIntros "_".
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }

      iApply ("IH" $! _ _ _ _ _ regs' with "[%] [] [$HPC] [$Hmap] [$Hworld_interp] [$Hcont] [//] Htop [$Hown] [$Htframe]").
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri v Hvs).
        subst regs'. rewrite /linsert_reg in Hvs.
        destruct (decide (ri = dst)).
        { subst ri. rewrite lookup_insert_eq in Hvs. simplify_eq.
          destruct (decide (dst = cnull)); [by iApply interp_untagged|].
          by iApply interp_untagged.
        }
        { iApply "Hreg"; auto. by simplify_map_eq. }
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
      - cbn; intros; subst regs'. rewrite /linsert_reg.
        by repeat (apply lookup_insert_is_Some'; right).
      - iIntros (ri wi Hregs_ri).
        subst regs'. rewrite /linsert_reg in Hregs_ri.
        destruct (decide (ri = dst)) as [->|Hne].
        { rewrite lookup_insert_eq in Hregs_ri.
          injection Hregs_ri as <-.
          destruct (decide (dst = cnull)); [by iApply interp_untagged | iApply interp_clear_tag]. }
        rewrite !lookup_insert_ne in Hregs_ri; try congruence.
        iApply "Hreg"; eauto.
      - iApply (interp_next_PC with "Hinv_interp"); eauto.
    }
    { assert (regs' = regs) as -> by (destruct Hfail; done).
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ; auto; contradiction. }
      iApply (ftlr_trap with "Htrap Hreg Htop HPC Hmap Hworld_interp Hcont Hown Htframe"); eauto. }
  Qed.

End fundamental.
