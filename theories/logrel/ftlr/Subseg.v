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

  (* TODO: move to program_logic/rules/rules_registry.v *)
  (** Every tagged, non-empty register capability with an identifier lies in
      the heap: provenance and the registry's heap clause (§4.3). *)
  Definition regs_prov_heap (regs : LReg) : Prop :=
    ∀ r v ι b e, regs !! r = Some v →
      get_tag v.(lw) = true → memory_cap_bounds v.(lw) = Some (b, e) → (b < e)%a →
      v.(lprov) = Some ι → ∀ x, (b <= x < e)%a → is_heap_address x = true.

  (* TODO: move to program_logic/rules/rules_registry.v *)
  Lemma observe_regs_prov_heap E (regs : LReg) :
    ([∗ map] k↦y ∈ regs, k ↦ᵣ y) -∗
    |~{E}~> ([∗ map] k↦y ∈ regs, k ↦ᵣ y) ∗ ⌜regs_prov_heap regs⌝.
  Proof.
    iIntros "Hmap".
    iApply (si_upd_ghost _ ([∗ map] k↦y ∈ regs, k ↦ᵣ y) with "Hmap").
    intros σ. iApply si_ghost_update.
    iIntros (lreg lmem R C Her) "Hlr Hsr Hm Hst HR HC Hmap".
    iDestruct (gen_heap_valid_inclSepM with "Hlr Hmap") as %Hincl.
    iModIntro. iExists R, C. iFrame. iPureIntro. split; first done.
    intros r v ι b e Hv Ht Hb Hlt Hι x Hx.
    destruct (erasure_reg_word _ _ _ _ _ r v Her (lookup_weaken _ _ _ _ Hv Hincl)) as [Hprov _].
    destruct (Hprov ι b e Ht Hb Hlt Hι) as (y & Hy & Hyb & Hye).
    eapply (reg_ok_heap _ _ _ (er_registry _ _ _ _ _ Her)); first exact Hy.
    rewrite /re_covers. solve_addr.
  Qed.

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
    ftlr_instr W C regs p p' g b e a w (Subseg dst r1 r2) ρ P cstk Ws Cs.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked Hi.
    iIntros "#IH #Hinv_interp #Hreg #Hinva #Hrcond #Hwcond #Hmono WorldRes Hcont %Hframe Hworld_interp Hown Htframe".
    iIntros "Hstate HPC Hmap".
    iInsert "Hmap" PC.

    iDestruct (WorldRes_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    (* A valid source without an identifier stays clear of the heap, so the
       pure branch of the Subseg rule applies (§4.4, case 3 never arises). *)
    iAssert (⌜∀ r t p0 g0 b0 e0 a0,
               <[PC:=WCap true p g b e a @@? None]> regs !!ₗ r = Some (WCap t p0 g0 b0 e0 a0 @@? None) →
               t = true → (b0 < e0)%a → disjoint_from_heap b0 e0⌝)%I as %Hnoid.
    { iIntros (r t0 p0 g0 b0 e0 a0 Hr -> Hlt).
      iAssert (interp W C (WCap true p0 g0 b0 e0 a0 @@? None)) as "Hr".
      { destruct (decide (r = PC)) as [->|HrPC].
        - rewrite llookup_reg_not_cnull // lookup_insert_eq in Hr.
          injection Hr as <- <- <- <- <-. iExact "Hinv_interp".
        - destruct (decide (r = cnull)) as [->|Hnull].
          + rewrite /llookup_reg in Hr. apply bind_Some in Hr as (? & _ & Hw). simplify_eq.
          + rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hr. iApply "Hreg"; eauto. }
      iDestruct (interp_cap_heap_conditions with "Hr") as %[Hvalid _].
      iPureIntro. exact (Hvalid Hlt). }
    assert (subseg_root_free (<[PC:=WCap true p g b e a @@? None]> regs) dst r1 r2) as Hroot.
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

    iApply (wp_Subseg _ _ _ _ _ _ _ _ _ _ _ _ None with "[$Ha $Hmap]"); eauto.
    { simplify_map_eq; auto. }
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply lookup_insert_is_Some'; eauto. }

    iIntros "!>" (regs' retv). iDestruct 1 as (HSpec) "(Ha & _ & Hmap)".
    clear Hnoid Hroot.
    destruct HSpec as [t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hdst Hz1 Hz2 Hao1 Hao2 HincrPC
                      | * Hdst Hz1 Hz2 Hunrep HincrPC
                      | t p0 g0 b0 e0 a0 π n1 n2 a1 a2 Hdst Hz1 Hz2 Hoo1 Hoo2 HincrPC
                      | * Hdst Hz1 Hz2 Hunrep HincrPC | ].
    { rewrite -andb_assoc in HincrPC.
      destruct (isWithin a1 a2 b0 e0 && (a1 <=? a2)%a) eqn:Hwi.
      { rewrite andb_true_r in HincrPC.
        apply andb_true_iff in Hwi as [Hwi Hle].
        apply isWithin_implies in Hwi as [Hwi_b Hwi_e].
        apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
        iEval (rewrite /linsert_reg) in "Hmap". rewrite /linsert_reg in HPC.
        iApply wp_pure_step_later; [done|].
        iNext ; iIntros "_".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ;auto;contradiction. }
        destruct (decide (PC = dst)) as [<-|HdstPC].
        { rewrite lookup_insert_eq in HPC. injection HPC as <- <- <- <- <- <- <-.
          rewrite llookup_reg_not_cnull // lookup_insert_eq in Hdst.
          injection Hdst as <- <- <- <- <- <- <-.
          rewrite !insert_insert_eq.
          iApply ("IH" $! _ _ _ _ _ regs with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          iModIntro. iApply (subseg_interp_preserved with "IH"); eauto.
          iApply (interp_next_PC with "Hinv_interp"); eauto. }
        rewrite lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WCap t p0 g0 a1 a2 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        { intros rr; rewrite !lookup_insert_is_Some'; eauto. }
        { iIntros (ri v Hri Hvs).
          destruct (decide (ri = dst)).
          { subst ri. rewrite lookup_insert_eq in Hvs. injection Hvs as <-.
            destruct (decide (dst = cnull)); [by iApply interp_untagged|].
            destruct t; [|by iApply interp_untagged].
            rewrite llookup_reg_not_cnull // in Hdst.
            pose proof Hdst as Hdst'.
            rewrite lookup_insert_ne // in Hdst.
            iSpecialize ("Hreg" $! dst _ Hri Hdst).
            iApply (interp_weakening with "IH Hreg"); auto; try solve_addr.
            - intros ι -> _ Hlt.
              eapply (Hprovheap dst _ ι b0 e0 Hdst'); [done|done|solve_addr|done|solve_addr].
            - apply PermFlowsToReflexive.
            - apply LocalityFlowsToReflexive.
          }
          { rewrite !lookup_insert_ne // in Hvs. iApply "Hreg"; auto. }
        }
        iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
      { rewrite andb_false_r in HincrPC.
        apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
        iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
        destruct (decide (dst = PC)) as [->|HdstPC].
        + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
          iApply (wp_bind (fill [SeqCtx])).
          iExtract "Hmap" PC as "HPC".
          iApply (wp_notCorrectPC_tag with "HPC"); first done.
          iNext; iIntros "HPC /=".
          iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
          iApply wp_value; auto.
        + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
          injection HPC as <- <- <- <- <- <- <-.
          iEval (rewrite /linsert_reg) in "Hmap".
          iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
          iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
          { destruct ρ; auto; contradiction. }
          iApply ("IH" $! _ _ _ _ _
            (<[dst:=if decide (dst = cnull) then lnull else WCap false p0 g0 a1 a2 a0 @@? π]>
               (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
            with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
          * intros rr; rewrite !lookup_insert_is_Some'; eauto.
          * iIntros (ri wi Hri Hregs_ri).
            destruct (decide (ri = dst)) as [->|Hne].
            { rewrite lookup_insert_eq in Hregs_ri.
              injection Hregs_ri as <-.
              destruct (decide (dst = cnull)); by iApply interp_untagged. }
            rewrite !lookup_insert_ne in Hregs_ri; try congruence.
            iApply "Hreg"; eauto.
          * iApply (interp_next_PC with "Hinv_interp"); eauto.
      }
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
        iApply (wp_bind (fill [SeqCtx])).
        iExtract "Hmap" PC as "HPC".
        iApply (wp_notCorrectPC_tag with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
        iApply wp_value; auto.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WCap false p0 g0 b0 e0 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); by iApply interp_untagged. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull
                  else WSealRange (t && isWithin a1 a2 b0 e0) p0 g0 a1 a2 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); [by iApply interp_untagged|].
            destruct (isWithin a1 a2 b0 e0) eqn:Hwi;
              last (rewrite andb_false_r; by iApply interp_untagged).
            rewrite andb_true_r.
            rewrite llookup_reg_not_cnull // lookup_insert_ne // in Hdst.
            iSpecialize ("Hreg" $! dst _ Hri Hdst).
            rewrite /isWithin in Hwi.
            iApply (interp_weakening_ot with "Hreg"); auto; try solve_addr.
            - apply SealPermFlowsToReflexive.
            - apply LocalityFlowsToReflexive. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { apply incrementPC_Some_inv in HincrPC as (t''&p''&g''&b''&e''&a''& a_next & π'' & HPC & Z & ->).
      iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
      destruct (decide (dst = PC)) as [->|HdstPC].
      + rewrite /linsert_reg lookup_insert_eq in HPC; simplify_eq.
      + rewrite /linsert_reg lookup_insert_ne // lookup_insert_eq in HPC.
        injection HPC as <- <- <- <- <- <- <-.
        iEval (rewrite /linsert_reg) in "Hmap".
        iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
        iDestruct (close_world_interp with "Hworld_interp Hstate Hinva WorldRes") as "Hworld_interp"; eauto.
        { destruct ρ; auto; contradiction. }
        iApply ("IH" $! _ _ _ _ _
          (<[dst:=if decide (dst = cnull) then lnull else WSealRange false p0 g0 b0 e0 a0 @@? π]>
             (<[PC:=WCap true p g b e a @@? None]> regs)) p g b e a_next None
          with "[%] [] [Hmap] [$Hworld_interp] [$Hcont] [//] [$Hown] [$Htframe]"); eauto.
        * intros rr; rewrite !lookup_insert_is_Some'; eauto.
        * iIntros (ri wi Hri Hregs_ri).
          destruct (decide (ri = dst)) as [->|Hne].
          { rewrite lookup_insert_eq in Hregs_ri.
            injection Hregs_ri as <-.
            destruct (decide (dst = cnull)); by iApply interp_untagged. }
          rewrite !lookup_insert_ne in Hregs_ri; try congruence.
          iApply "Hreg"; eauto.
        * iApply (interp_next_PC with "Hinv_interp"); eauto.
    }

    { iApply wp_pure_step_later; [done|]. iNext; iIntros "_".
      iApply wp_value; auto. }
  Qed.

End fundamental.
