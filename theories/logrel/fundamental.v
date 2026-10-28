From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel interp_weakening monotone.
From griotte Require Export
  ftlr_base ftlr_step
  Jmp JCond Jalr Mov CLoad Store BinOp Restrict
  Subseg Get ClearTag Lea SetA Seal UnSeal SpecialRW SetMIE Mret FailHalt Auipcc.
From griotte Require Import register_tactics.
Import CoreWPNotations.

Section fundamental_generic.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** Weakening of the instruction premise of a case lemma. *)
  Lemma ftlr_instr_base_mono (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr Q : Prop) :
    (Q → Pinstr) →
    ftlr_instr_base W C regs p p' g b e a w ρ P Pinstr →
    ftlr_instr_base W C regs p p' g b e a w ρ P Q.
  Proof.
    intros HQP H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked HQ.
    exact (H Hp Hsome HcorrectPC Hbae Hfp Hpers Hpwl Hregion Hnotrevoked (HQP HQ)).
  Qed.

  #[local] Ltac by_binop_case :=
    eapply ftlr_instr_base_mono; [| eapply binop_case]; intros ->; eauto 10.
  #[local] Ltac by_jcond_case :=
    eapply jcond_case; eauto.
  #[local] Ltac by_get_case :=
    eapply get_case; rewrite /is_Get; eauto 10.

  (** The case lemmas of all the instructions. *)
  Lemma ftlr_instr_cases :
    ∀ W C regs p p' g b e a w i ρ P, ftlr_instr W C regs p p' g b e a w i ρ P.
  Proof.
    intros W C regs p p' g b e a w i ρ P.
    (* proof by cases on each instruction *)
    destruct i.
    - (* Jmp *) apply jmp_case.
    - (* Jeq *) by_jcond_case.
    - (* Jne *) by_jcond_case.
    - (* Jlt *) by_jcond_case.
    - (* Jle *) by_jcond_case.
    - (* Jalr *) apply jalr_case.
    - (* Mov *) apply mov_case.
    - (* CLoad *) apply load_case.
    - (* Store *) apply store_case.
    - (* Lt *) by_binop_case.
    - (* Le *) by_binop_case.
    - (* Add *) by_binop_case.
    - (* Sub *) by_binop_case.
    - (* Mul *) by_binop_case.
    - (* LAnd *) by_binop_case.
    - (* LOr *) by_binop_case.
    - (* LShiftL *) by_binop_case.
    - (* LShiftR *) by_binop_case.
    - (* Lea *) apply lea_case.
    - (* SetA *) apply seta_case.
    - (* Restrict *) apply restrict_case.
    - (* Subseg *) apply subseg_case.
    - (* GetB *) by_get_case.
    - (* GetE *) by_get_case.
    - (* GetLen *) by_get_case.
    - (* GetA *) by_get_case.
    - (* GetP *) by_get_case.
    - (* GetL *) by_get_case.
    - (* GetWType *) by_get_case.
    - (* GetOType *) by_get_case.
    - (* Seal *) apply seal_case.
    - (* UnSeal *) apply unseal_case.
    - (* SpecialRW *) apply specialrw_case.
    - (* SetMIE *) apply setmie_case.
    - (* Mret *) apply mret_case.
    - (* Fail *) apply fail_case.
    - (* Halt *) apply halt_case.
    - (* GetTag *) by_get_case.
    - (* ClearTag *) apply cleartag_case.
    - (* Auipcc *) apply auipcc_case.
  Qed.

End fundamental_generic.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    (trusted_fault : CSTK → LWord → LReg → iProp Σ)
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation E := (interpO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation K := (contO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The fundamental theorem, by Löb induction: its induction hypothesis
      is [ftlr_IH]. Each step is the step lemma, with the world owned by
      the thread. *)
  Theorem fundamental W C w :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C w -∗
      interp_expression W C w.
  Proof.
    iIntros "#Htrap".
    iLöb as "IH" forall (W C w).
    iIntros "#Hw".
    iIntros (cstk Ws Cs regs)
      "(#Hreg & #Htop & HPC & Hregs & Hworld & Hcont & Hown & Hcstk & %Hframe)".
    iApply (ftlr_step (λ _, True)%I (λ _, True)%I trusted_fault W C InterruptEnabled w
              cstk Ws Cs regs ftlr_instr_cases Hframe
              with "[] Htrap [] Hw Hreg Htop HPC Hregs [Hworld] Hcont Hown Hcstk [] []").
    - iApply world_accessor_exclusive.
    - by iModIntro.
    - rewrite world_resources_exclusive. iFrame "Hworld".
      iApply shared_credit_exclusive.
    - done.
    - done.
  Qed.

  (* The premise [trap_vector_safe trusted_fault (lword_of_word mtcc_vec)] is discharged in
     the switcher by [switcher_mtcc_vec_safe]
     (switcher/switcher_exception.v). *)
  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) (π : option AId) :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C (Cap p g b e a @@? π) →
      interp_expression W C (Cap p g b e a @@? π).
  Proof.
    iIntros "#Htrap #Hinv_interp".
    iApply (fundamental with "Htrap Hinv_interp").
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a π :
    executeAllowed p = true ->
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      interp W C (Cap p g b e a @@? π) -∗
      exec_cond W C p g b e π interp.
  Proof.
    iIntros (Hp) "#Htrap #Hw".
    destruct (decide (b < e)%a) as [Hbe|Hbe]; cycle 1.
    { iIntros (a0 W' Hin). exfalso. solve_addr. }
    iDestruct (interp_exec_noid with "Hw") as %->; [done|done|].
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iDestruct (interp_cap_disjoint with "Hw") as %[_ Hdisjoint]; first done.
    destruct g.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_nl_cap_nonheap with "Hw") as "Hw'";
        [exact Hdisjoint|exact Hrelated|done|].
      iApply (fundamental W' with "Htrap"); eauto.
      iApply interp_lea; eauto.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_cap_nonheap with "Hw") as "Hw'";
        [exact Hdisjoint|exact Hrelated|].
      iApply (fundamental W' with "Htrap"); eauto.
      iApply interp_lea; eauto.
  Qed.

  (* We can use the above fact to create a special "jump or fail pattern" when jumping to an unknown adversary *)
  Lemma exec_wp W C p g b e a π :
    isCorrectPC (Cap p g b e a) ->
    ⊢ exec_cond W C p g b e π interp -∗
    ∀ W', future_world g W W' →
          ▷ (interp_expr interp (interp_cont interp) W' C (Cap p g b e a @@? π)).
  Proof.
    iIntros (Hvpc) "Hexec".
    rewrite /exec_cond /enter_cond.
    iIntros (W'). rewrite /future_world.
    assert (a ∈ₐ [b, e)) as Hin.
    { inversion Hvpc; subst. auto. }
    destruct g.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
    - iIntros (Hrelated).
      iSpecialize ("Hexec" $! a W' Hin Hrelated).
      iFrame.
  Qed.

  Lemma fundamental_ih :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
      ftlr_IH.
  Proof.
    iIntros "#Htrap".
    iModIntro; iNext.
    iIntros (W C w) "Hw".
    iApply (fundamental with "Htrap Hw").
  Qed.

  Lemma jmp_or_fail_spec W C (w : LWord) φ :
    ⊢ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w.(lw)))
         then
           (∃ p g b e a π,
               (⌜w = Cap p g b e a @@? π ∨ (∃ k, w = Sentry k p g b e a @@? π)⌝
                ∗ □ ∀ W', future_world g W W'
                          → ▷ (interp_expr interp (interp_cont interp) W' C) (lupdatePcPerm w)))
         else trap_safe (lupdatePcPerm w) ⊤ φ ∗ PC ↦ₚ[th] lupdatePcPerm w
                          -∗ WP Exec @[th] {{ φ }} )).
  Proof.
    iIntros "#Htrap #Hw".
    destruct (decide (isCorrectPC (updatePcPerm w.(lw)))).
    - inversion i.
      destruct w as [w π]; cbn in H.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Htrap Hw") as "Hexec";[auto|].
        iApply exec_wp;auto.
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        rewrite /= interp_unfold /=.
        iSplit;[iPureIntro; right; eauto|]. iModIntro.
        iDestruct "Hw" as "[%Hnonheap #Hw]".
        rewrite /enter_cond.
        iIntros (W') "Hfuture".
        iSpecialize ("Hw" with "Hfuture").
        iSpecialize ("Hw" $! g0 (LocalityFlowsToReflexive g0)).
        iExact "Hw".
    - iIntros "[Hfailed HPC]".
      by iApply (wp_notCorrectPC_trap with "HPC Hfailed").
  Qed.

End fundamental.
