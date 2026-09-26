From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel interp_weakening monotone.
From griotte Require Export
  ftlr_base
  Jmp Jnz Jalr Mov Load Store BinOp Restrict
  Subseg Get ClearTag Lea Seal UnSeal ReadSR WriteSR.
From griotte Require Import register_tactics.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma interp_pc_heap_cell_live W C p g b e a :
    isCorrectPC (WCap true p g b e a) ->
    interp W C (WCap true p g b e a) -∗
    ⌜heap_cell_live (heap_std W) a⌝.
  Proof.
    iIntros (Hpc) "Hinterp".
    iDestruct (interp_cap_disjoint with "Hinterp") as %[_ Hdisjoint].
    { by inversion Hpc. }
    iPureIntro.
    apply heap_cell_live_nonheap.
    apply not_true_is_false. intros Hheap.
    apply withinBounds_true_iff in Hheap.
    rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
    eapply (Hdisjoint a); apply elem_of_finz_seq_between.
    - apply withinBounds_true_iff.
      exact (isCorrectPC_withinBounds true p g b e a Hpc).
    - exact Hheap.
  Qed.

  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) :
    ⊢ interp W C (WCap true p g b e a) →
      interp_expression W C (WCap true p g b e a).
  Proof.
    iIntros "#Hinv_interp".
    iIntros (cstk Ws Cs regs) "#Halloc [[Hfull Hreg] [Hmreg [Hworld_interp [Hcont [Hown [Hframe %Hframe]]]]]]".
    assert ( readAllowed p = true \/ readAllowed p = false )
      as [Hread_p|Hread_p] by (destruct_perm p ; naive_solver)
    ; cycle 1.
    { (* if p not readable, then execution will fail *)
      apply notreadAllowed_is_notexecuteAllowed in Hread_p.
      iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
      iApply (wp_bind (fill [SeqCtx])).
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      { intro Hcontra ; destruct p ; inv Hcontra; congruence. }
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }
    clear Hread_p.

    iRevert "Hinv_interp".
    iLöb as "IH'" forall (W C regs p g b e a cstk Ws Cs Hframe).
    iAssert ftlr_IH as "IH" ; [|iClear "IH'"].
    { iModIntro; iNext.
      iIntros (W_ih C_ih cstk_ih Ws_ih Cs_ih r_ih p_ig g_ih b_ih e_ih a_ih)
        "#Halloc_ih %Hfull #Hregs Hmreg Hworld_interp Hcont %Hframe' Hown Htframe Hinterp".
      iApply ("IH'" with "[%] [] [] [Hmreg] [$] [$] [$] [$]");eauto.
      done.
    }
    iIntros "#Hinv_interp".
    iDestruct "Hfull" as "%". iDestruct "Hreg" as "#Hreg".
    iApply (wp_bind (fill [SeqCtx])).
    destruct (decide (isCorrectPC (WCap true p g b e a))) as [HcorrectPC|] ; cycle 1.
    { (* Not correct PC *)
      rewrite /registers_pointsto.
      iExtract "Hmreg" PC as "HPC".
      iApply (wp_notCorrectPC with "HPC"); eauto.
      iNext. iIntros "HPC /=".
      iApply wp_pure_step_later; auto.
      iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    }

    (* Correct PC *)
    iDestruct (interp_pc_heap_cell_live with "Hinv_interp") as %Hpc_live;
      first exact HcorrectPC.
    assert ((b <= a)%a ∧ (a < e)%a) as Hbae.
    { eapply in_range_is_correctPC; eauto. solve_addr. }

    iAssert (⌜ validPCperm p g ⌝)%I as "%Hp".
    { (* if not, contradiction by correctPC or validity *)
      inv HcorrectPC; subst; auto.
      iSplit; first done.
      iIntros (Hpwl).
      destruct p ; cbn in Hpwl ; try congruence.
      destruct w ; cbn in Hpwl ; try congruence.
      destruct g; last done.
      (* Contradiction -- WL and Global are not safe *)
      rewrite fixpoint_interp1_eq interp1_eq.
      replace (isO (BPerm _ WL _ _)) with false by (cbn; destruct rx; done).
      cbn.
      destruct rx; auto.
      iDestruct "Hinv_interp" as "[_ %Hcontra]". naive_solver.
    }

    iPoseProof "Hinv_interp" as "#Hinv".
    iEval (rewrite !fixpoint_interp1_eq interp1_eq) in "Hinv".
    destruct (isO p) eqn: HnO.
    { inv HcorrectPC; simplify_eq
      ; eapply executeAllowed_nonO in H6
      ; congruence.
    }
    destruct (has_sreg_access p) eqn:HpXRS; first done.


    iDestruct "Hinv" as "[#Hinv %Hpwl_cond]".

    iDestruct (extract_from_region_inv _ _ a with "Hinv") as "H";auto.

    assert (readAllowed p = true) as Hra.
    {
      destruct Hp as [Hexec _]
      ; by eapply executeAllowed_is_readAllowed.
    }
    iDestruct (interp_in_registers with "[Hreg] [H]")
      as (p'' P'' Hflp'' Hperscond_P'') "(Hrela & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate_a)"
    ;eauto ; iClear "Hinv".
    assert (∃ (ρ : region_type), (std W) !! a = Some ρ ∧ ρ ≠ Revoked)
      as [ρ [Hρ Hne ] ].
    { destruct (isWL p),g; simplify_eq ; eauto.
      destruct Hstate_a as [Htemp | Hperm];eauto. }

    iEval (rewrite world_interp_eq /world_interp_def) in "Hworld_interp".
    iDestruct "Hworld_interp" as "(Hregion_world & Hsts & Hseals_world)".
    iDestruct (sts_full_world_heap_wf with "Hsts") as %Hheap_wf.
    iAssert (world_interp W C) with "[Hregion_world Hsts Hseals_world]" as "Hworld_interp".
    { rewrite world_interp_eq /world_interp_def. iFrame. }

    iDestruct (open_world_interp W C a p'' _ ρ with "[$Hrela] [$Hworld_interp]")
      as "(Hworld_interp & Hstate & (%w & WorldRes) )"
    ; [exact Hpc_live | destruct ρ; auto; contradiction | exact Hρ |].

    rewrite /registers_pointsto ; iExtract "Hmreg" PC as "HPC".
    destruct (decodeInstrW w) eqn:Hi. (* proof by cases on each instruction *)
    + (* Jmp *)
      iApply (jmp_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Jnz *)
      iApply (jnz_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Jalr *)
      iApply (jalr_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Mov *)
      iApply (mov_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Load *)
      iApply (load_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Store *)
      iApply (store_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Lt *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* Add *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* Sub *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* Mul *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* LAnd *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* LOr *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* LShiftL *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* LShiftR *)
      iApply (binop_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto; naive_solver.
    + (* Lea *)
      iApply (lea_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Restrict *)
      iApply (restrict_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Subseg *)
      iApply (subseg_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetB *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetB _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetE *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetE _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetA *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetA _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetP *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetP _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetL *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetL _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetWType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetWType _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* GetOType *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetOType _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Seal *)
      iApply (seal_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* UnSeal *)
      iApply (unseal_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* ReadSR *)
      iApply (readsr_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* WriteSR *)
      iApply (writesr_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]")
      ;eauto.
    + (* Fail *)
      iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
      iApply (wp_fail with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value.
      iIntros (Hcontr); inversion Hcontr.
    + (* Halt *)
      iDestruct (WorldRes_acc with "WorldRes") as " [ (>Ha & Hinterp) WorldRes ]".
      iApply (wp_halt with "[HPC Ha]"); eauto; iFrame.
      iNext. iIntros "[HPC Ha] /=".
      assert ( ∀ Wv : WORLD * CmptName * Word, Persistent (safeC P'' Wv) ) as Hperscond_safeP''.
      { rewrite /persistent_cond in Hperscond_P''; apply _. }
      iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
      iDestruct (close_world_interp with "Hworld_interp Hstate Hrela WorldRes") as "Hworld_interp"; eauto.
      { destruct ρ;auto;contradiction. }
      iApply wp_pure_step_later; auto; iNext ; iIntros "_".
      iApply wp_value; auto.
    + (* GetTag *)
      iApply (get_case _ _ _ _ _ _ _ _ _ _ _ _ _ (GetTag _ _) with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]"); eauto.
    + (* ClearTag *)
      iApply (cleartag_case with
               "Halloc [$IH] [$Hinv_interp] [$Hreg] [$Hrela]
               [$Hrcond] [$Hwcond] [$HmonoR] [$WorldRes]
               [$Hcont] [//] [$Hworld_interp] [$Hown] [$Hframe]
               [$Hstate] [$HPC] [Hmreg]"); eauto.
  Qed.

  Theorem fundamental W C w :
    ⊢ interp W C w -∗ interp_expression W C w.
  Proof.
    iIntros "Hw"; destruct w as [| [ [] c | ] | | ].
    2: { iApply fundamental_cap; done. }
    all: iIntros (????) "#Halloc (? & Hreg & ?)"; unfold interp_conf.
    all: iApply (wp_wand with "[-]"); [ | iIntros (?) "H"; iApply "H"].
    all: iApply (wp_bind (fill [SeqCtx])); cbn.
    all: unfold registers_pointsto; rewrite -insert_delete_eq.
    all: iDestruct (big_sepM_insert with "Hreg") as "[HPC ?]"; first by rewrite lookup_delete_eq.
    all: iApply (wp_notCorrectPC with "HPC"); first by inversion 1.
    all: iNext; iIntros; cbn; iApply wp_pure_step_later; auto.
    all: iNext; iIntros "_"; iApply wp_value; iIntros (?); congruence.
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a:
    executeAllowed p = true ->
    ⊢ interp W C (WCap true p g b e a) -∗ exec_cond W C p g b e interp.
  Proof.
    iIntros (Hp) "#Hw".
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iDestruct (interp_cap_disjoint with "Hw") as %[_ Hdisjoint]; first done.
    assert (is_heap_address b = false) as Hnonheap.
    { apply not_true_is_false. intros Hb.
      destruct Hin as [Hba0 Ha0e].
      apply withinBounds_true_iff in Hb.
      rewrite /disjoint_from_heap elem_of_disjoint in Hdisjoint.
      eapply (Hdisjoint b); apply elem_of_finz_seq_between; solve_addr. }
    destruct g.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_nl_cap_nonheap with "Hw") as "Hw'";
        [exact Hnonheap|exact Hdisjoint|exact Hrelated|done|].
      iApply (fundamental W');eauto.
      iApply interp_lea; eauto.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_cap_nonheap with "Hw") as "Hw'";
        [exact Hnonheap|exact Hdisjoint|exact Hrelated|].
      iApply (fundamental W');eauto.
      iApply interp_lea; eauto.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  Lemma exec_wp W C p g b e a :
    isCorrectPC (WCap true p g b e a) ->
    ⊢ exec_cond W C p g b e interp -∗
    ∀ W', future_world g W W' → ▷ (interp_expr interp (interp_cont interp) W' C (WCap true p g b e a)).
  Proof.
    iIntros (Hvpc) "Hexec".
    rewrite /exec_cond /enter_cond.
    iIntros (W'). rewrite /future_world.
    assert (a ∈ₐ[[b,e]])%I as Hin.
    { rewrite /in_range. inversion Hvpc; subst. auto. }
    destruct g.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
  Qed.

  Lemma fundamental_ih :
    ⊢ ftlr_IH.
  Proof.
    iModIntro; iNext.
    iIntros (???????????) "#Halloc????????#Hv".
    iDestruct (fundamental with "Hv") as "Hcont".
    iApply "Hcont"; iFrame "∗#".
  Qed.

  Lemma jmp_or_fail_spec W C w φ :
    ⊢
    (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w))
         then
           (∃ p g b e a,
               (⌜w = WCap true p g b e a ∨ w = WSentry true p g b e a ⌝
                ∗ □ ∀ W', future_world g W W'
                          → ▷ (interp_expr interp (interp_cont interp) W' C) (updatePcPerm w)))
         else φ FailedV ∗ PC ↦ᵣ updatePcPerm w
                          -∗ WP Seq (Instr Executable) {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w))).
    - inversion i.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "[$Hw]") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_.
        rewrite /= fixpoint_interp1_eq /=.
        iSplit;[eauto|]. iModIntro.
        iDestruct "Hw" as "[%Hnonheap #Hw]".
        rewrite /enter_cond.
        iIntros (W') "Hfuture".
        iSpecialize ("Hw" with "Hfuture").
        iSpecialize ("Hw" $! g0 (LocalityFlowsToReflexive g0)).
        iExact "Hw".
    - iIntros "[Hfailed HPC]".
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC");eauto.
      iNext. iIntros "_". iApply wp_pure_step_later;auto.
      iNext; iIntros "_". iApply wp_value. iFrame.
  Qed.

End fundamental.
