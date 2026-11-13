From griotte Require Export logrel.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import ftlr_base ftlr_contract interp_weakening.
From griotte Require Import shapes.step instructions.control.
From griotte Require Import map_simpl register_tactics.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma jalr_case (m : InterruptStatus) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p': Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (rdst rsrc : RegName) (P:V):
    ftlr_contract m W C regs p p' g b e a w (Jalr rdst rsrc) ρ P.
  Proof.
    apply ftlr_contract_intro_at.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".
    iDestruct (thread_in_elim with "Hthread") as %Hth_in.

    iDestruct (pc_open_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".

    (* A tagged target keeps the thread at a posture where it may run. *)
    iAssert (⌜∀ wsrc, regs !!ₗ rsrc = Some wsrc → jalr_target_ok rdst rsrc wsrc.(lw) = true →
              route_pre th m → route_pre th (jalr_mie regs rsrc m)⌝)%I as %Hroute.
    { iIntros ([ws πw] Hws Htgt Hpre_m). rewrite /jalr_mie Hws.
      destruct ws as [z | sb | k [] p0 g0 b0 e0 a0 | ot sb]; cbn; try done.
      destruct (decide (rsrc = cnull)) as [->|Hnull].
      { rewrite llookup_reg_cnull in Hws. by rewrite /lnull in Hws. }
      rewrite llookup_reg_not_cnull // in Hws.
      iDestruct ("Hreg" $! rsrc _ Hws) as "Hws".
      iEval (rewrite interp_unfold) in "Hws".
      iDestruct "Hws" as "(_ & _ & %Hclause)".
      iPureIntro. by apply (route_pre_sentry m C). }
    iApply (wp_Jalr with "[$HPC $Ha $Hmap $Hmie]"); eauto.
    { rewrite /subseteq /map_subseteq. intros rr _.
      apply elem_of_dom. apply Hsome. }

    iIntros "!>" (lpc' regs' retv). iDestruct 1 as (HSpec) "(HPC & Ha & Hmap & HT)".
    destruct (step_outcome_cases _ _ _ _ _ _ HSpec) as [ [Hnext ->] | [_ (-> & -> & ->)] ];
      cycle 1.
    { iDestruct "HT" as "[ [%Hc _] | [_ Hmie] ]"; first done.
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
      iNext. iApply (ftlr_post_at_fault with "HPC Hmap Hreg Hworld_interp Hmie"); eauto. }
    apply jalr_outcome_Some_inv in Hnext as (wsrc & pc_a' & Hrsrc & Htgt & Hpca' & -> & Hregs').
    iDestruct "HT" as "[ [_ Hmie] | [%Hc _] ]"; last done.
    iEval (rewrite /jalr_mie Hrsrc) in "Hmie".

    (* The link: a return sentry when [rdst = cra], the unsealed PC otherwise. *)
    iAssert (interp W C (jalr_link rdst m true p g b e pc_a')) as "Hinterp_ret".
    { rewrite /jalr_link. destruct (decide (rdst = cra)) as [Hcra | Hcra].
      2: { iApply (interp_weakening with "IH Hthread Hinv_interp");
           [solve_addr | solve_addr | apply subseg_heap_base_same
           | apply PermFlowsToReflexive | apply LocalityFlowsToReflexive]. }
      destruct Hp as [Hexec _].
      iDestruct (interp_cap_disjoint with "Hinv_interp") as %[_ Hheap]; first exact Hexec.
      assert (not_heap_range b e) as Hsentry.
      { split; last exact Hheap.
        apply not_true_is_false. intros Hbase_heap.
        apply withinBounds_true_iff in Hbase_heap.
        rewrite /disjoint_from_heap elem_of_disjoint in Hheap.
        eapply (Hheap b); apply elem_of_finz_seq_between; solve_addr. }
      assert (sentry_kind_mie (ret_kind m) = Some InterruptEnabled →
              CtxSwitch ∉ cmpt_threads C) as Hsep.
      { destruct m; cbn; [|done]. intros _. by apply route_pre_enabled_sep. }
      iApply (interp_weakeningSentry with "IH Hinv_interp");eauto;try solve_addr.
      - by apply executeAllowed_nonO.
      - reflexivity.
    }

    (* A [cnull] destination leaves the registers unchanged. *)
    assert (∀ x, is_Some (regs' !! x)) as Hsome'.
    { intros x. rewrite Hregs'. case_decide; first apply Hsome.
      rewrite /linsert_reg decide_False // lookup_insert_is_Some.
      destruct (decide (rdst = x)); auto; right; split; auto. }
    iAssert (∀ ri wi, ⌜regs' !! ri = Some wi⌝ → interp W C wi)%I as "#Hreg'".
    { iIntros (ri wi Hri). rewrite Hregs' in Hri. case_decide; first by iApply "Hreg".
      rewrite /linsert_reg decide_False // in Hri.
      destruct (decide (ri = rdst)); simplify_map_eq; [iExact "Hinterp_ret" | by iApply "Hreg"]. }
    iClear "Hinterp_ret". clear Hregs'.

    (* The new PC is the source word with the PC permission, and keeps its
       identifier. *)
    destruct wsrc as [wsrc πs].
    rewrite /lupdatePcPerm /lift_word /=.
    iAssert (interp W C (wsrc @@? πs)) as "#Hwsrc".
    { destruct (decide (rsrc = cnull)) as [->|Hnull].
      + rewrite llookup_reg_cnull /lnull in Hrsrc.
        injection Hrsrc as <- <-. by iApply interp_untagged.
      + rewrite llookup_reg_not_cnull // in Hrsrc.
        iApply "Hreg"; eauto. }

    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.

    (* The next-PC witness, at the posture after the jump: the enter
       condition of a sentry, the induction hypothesis otherwise. *)
    iAssert (▷ interp_expr_at (default m (jalr_target_mie wsrc)) interp interp_continuation
               W C (updatePcPerm wsrc @@? πs) ∗
             ⌜route_pre th (default m (jalr_target_mie wsrc))⌝)%I as "[Hnext %Hpre']".
    { destruct wsrc as [z | sb | k [] p0 g0 b0 e0 a0 | ot sb];
        cbn [updatePcPerm jalr_target_mie default].
      4: { by rewrite /jalr_target_ok /= in Htgt. }
      3: { iEval (rewrite interp_unfold) in "Hwsrc".
           iDestruct "Hwsrc" as "(_ & #Hinterp_src & %Hclause)".
           iSplit; last (iPureIntro; by apply (route_pre_sentry m C)).
           iAssert (future_world g0 W W) as "Hfuture".
           { iApply futureworld_refl. }
           destruct g0; iEval (cbn) in "Hinterp_src".
           - (* A Global sentry, at the running thread of its compartment. *)
             iSpecialize ("Hinterp_src" $! th with "Hthread").
             iSpecialize ("Hinterp_src" $! W with "Hfuture").
             iApply ("Hinterp_src" $! Global with "[%]").
             apply LocalityFlowsToReflexive.
           - iSpecialize ("Hinterp_src" $! W with "Hfuture").
             iApply ("Hinterp_src" $! Local with "[%]").
             apply LocalityFlowsToReflexive. }
      all: iSplit; last done.
      all: iNext; iApply interp_expression_at; iApply "IH"; iExact "Hwsrc". }
    iNext.
    iApply (ftlr_post_at_next with "HPC Hmap Hreg' Hnext Hworld_interp Hmie"); done.
  Qed.

End fundamental.
