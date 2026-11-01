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

  (** Weakening of the instruction premise of a case lemma. *)
  Lemma ftlr_instr_base_mono (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (P : V) (Pinstr Q : Prop) :
    (Q → Pinstr) →
    ftlr_instr_base W C regs p p' g b e a w ρ P Pinstr →
    ftlr_instr_base W C regs p p' g b e a w ρ P Q.
  Proof.
    intros HQP H Hp Hsome HcorrectPC Hbae Hfp Hpers HQ.
    exact (H Hp Hsome HcorrectPC Hbae Hfp Hpers (HQP HQ)).
  Qed.

  #[local] Ltac by_binop_case :=
    eapply ftlr_instr_base_mono; [| eapply binop_case]; intros ->; eauto 10.
  #[local] Ltac by_jcond_case :=
    eapply jcond_case; eauto.
  #[local] Ltac by_get_case :=
    eapply get_case; rewrite /is_Get; eauto 10.

  (** A case that does not see the posture frames the MIE fragment: the
      posture is kept, and the next-PC witness holds at every posture. *)
  Lemma ftlr_instr_frame (m : InterruptStatus) (W : WORLD) (C : CmptName)
    (regs : leibnizO LReg) (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i : instr) (ρ : region_part) (P : V) :
    ftlr_instr W C regs p p' g b e a w i ρ P →
    ftlr_instr_at m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hcase Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "(#IH & #Hthread & #Hinv_interp & #Hreg & #Hinva & #Hrcond & #Hwcond & WorldRes
      & Hworld_interp & HPC & Hmap & Hmie & %Hpre)".
    iApply (wp_wand with "[- Hmie]").
    { iApply (Hcase with "[$IH $Hthread $Hinv_interp $Hreg $Hinva $Hrcond $Hwcond $WorldRes
                          $Hworld_interp $HPC $Hmap]"); eauto. }
    iIntros (v) "Hpost". iNext.
    iDestruct "Hpost" as (W') "(%Hrel & Hworld & Hpost)".
    iExists W', m. iFrame "Hworld Hmie". iSplit; first done. iSplit; first done.
    destruct v; try (rewrite ftlr_post_at_eq //; iExact "Hpost").
    rewrite /ftlr_post_at /ftlr_post.
    iDestruct "Hpost" as (regs' pc) "(Hfull & HPC & Hregs & Hreg' & Hpc)".
    iExists regs', pc. iFrame. by iApply interp_expression_at.
  Qed.

  (** The case lemmas of all the instructions: Jalr sees the posture, the
      others frame it. *)
  Lemma ftlr_instr_cases :
    ∀ W C regs p p' g b e a w i ρ P m, ftlr_instr_at m W C regs p p' g b e a w i ρ P.
  Proof.
    (* A case stated at a fixed link then fails at once instead of unfolding. *)
    Opaque ftlr_instr_base.
    intros W C regs p p' g b e a w i ρ P m.
    (* proof by cases on each instruction *)
    destruct i.
    - (* Jmp *) apply ftlr_instr_frame, jmp_case.
    - (* Jeq *) apply ftlr_instr_frame; by_jcond_case.
    - (* Jne *) apply ftlr_instr_frame; by_jcond_case.
    - (* Jlt *) apply ftlr_instr_frame; by_jcond_case.
    - (* Jle *) apply ftlr_instr_frame; by_jcond_case.
    - (* Jalr *) apply jalr_case.
    - (* Mov *) apply ftlr_instr_frame, mov_case.
    - (* CLoad *) apply ftlr_instr_frame, load_case.
    - (* Store *) apply ftlr_instr_frame, store_case.
    - (* Lt *) apply ftlr_instr_frame; by_binop_case.
    - (* Le *) apply ftlr_instr_frame; by_binop_case.
    - (* Add *) apply ftlr_instr_frame; by_binop_case.
    - (* Sub *) apply ftlr_instr_frame; by_binop_case.
    - (* Mul *) apply ftlr_instr_frame; by_binop_case.
    - (* LAnd *) apply ftlr_instr_frame; by_binop_case.
    - (* LOr *) apply ftlr_instr_frame; by_binop_case.
    - (* LShiftL *) apply ftlr_instr_frame; by_binop_case.
    - (* LShiftR *) apply ftlr_instr_frame; by_binop_case.
    - (* Lea *) apply ftlr_instr_frame, lea_case.
    - (* SetA *) apply ftlr_instr_frame, seta_case.
    - (* Restrict *) apply ftlr_instr_frame, restrict_case.
    - (* Subseg *) apply ftlr_instr_frame, subseg_case.
    - (* GetB *) apply ftlr_instr_frame; by_get_case.
    - (* GetE *) apply ftlr_instr_frame; by_get_case.
    - (* GetLen *) apply ftlr_instr_frame; by_get_case.
    - (* GetA *) apply ftlr_instr_frame; by_get_case.
    - (* GetP *) apply ftlr_instr_frame; by_get_case.
    - (* GetL *) apply ftlr_instr_frame; by_get_case.
    - (* GetWType *) apply ftlr_instr_frame; by_get_case.
    - (* GetOType *) apply ftlr_instr_frame; by_get_case.
    - (* Seal *) apply ftlr_instr_frame, seal_case.
    - (* UnSeal *) apply ftlr_instr_frame, unseal_case.
    - (* SpecialRW *) apply ftlr_instr_frame, specialrw_case.
    - (* SetMIE *) apply ftlr_instr_frame, setmie_case.
    - (* Mret *) apply ftlr_instr_frame, mret_case.
    - (* Fail *) apply ftlr_instr_frame, fail_case.
    - (* Halt *) apply ftlr_instr_frame, halt_case.
    - (* GetTag *) apply ftlr_instr_frame; by_get_case.
    - (* ClearTag *) apply ftlr_instr_frame, cleartag_case.
    - (* Auipcc *) apply ftlr_instr_frame, auipcc_case.
  Qed.

End fundamental_generic.

(** The fundamental theorem at every thread, by one Löb induction: a Global
    sentry made by a step runs at every thread of its compartment. *)
Section fundamental_threads.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Lemma fundamental_all_threads :
    ⊢ ∀ (t : Thread) (W : WORLD) (C : CmptName) (w : LWord),
        interp (th := t) W C w -∗ interp_expression (th := t) W C w.
  Proof.
    iLöb as "IH".
    iIntros (t W C w) "#Hw".
    iIntros (m cstk Ws Cs regs)
      "(#Hthread & #Htrap & #Hreg & #Htop & HPC & Hregs & Hwres & Hcred & Hcont & Hown & Hcstk
        & %Hframe & %Hpre & Hmie & Hheld)".
    iApply (ftlr_step (th := t) W C m w cstk Ws Cs regs ftlr_instr_cases Hframe Hpre
              with "[] Hthread Htrap [] Hw Hreg Htop HPC Hregs [$Hwres $Hcred] Hcont Hown Hcstk
                    Hheld Hmie").
    - iApply world_accessor_full.
    - by iModIntro.
  Qed.

End fundamental_threads.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    {cthreads : CmptThreads}
    {CL : ∀ t, CritLink Σ t}
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

  (** The fundamental theorem: its induction hypothesis is [ftlr_IH], at
      every thread. The trap vector's safety for an untrusted fault is a
      premise of the safe execution. *)
  Theorem fundamental W C w :
    ⊢ interp W C w -∗
      interp_expression W C w.
  Proof. iApply fundamental_all_threads. Qed.

  Theorem fundamental_cap
    (W : WORLD) (C : CmptName)
    (p : Perm) (g : Locality)
    (b e a : Addr) (π : option AId) :
    ⊢ interp W C (Cap p g b e a @@? π) →
      interp_expression W C (Cap p g b e a @@? π).
  Proof.
    iIntros "#Hinv_interp".
    iApply (fundamental with "Hinv_interp").
  Qed.

  (* The fundamental theorem implies the exec_cond *)
  Lemma interp_exec_cond W C p g b e a π :
    executeAllowed p = true ->
    ⊢ interp W C (Cap p g b e a @@? π) -∗
      exec_cond W C p g b e π interp.
  Proof.
    iIntros (Hp) "#Hw".
    destruct (decide (b < e)%a) as [Hbe|Hbe]; cycle 1.
    { iIntros (a0 W' Hin). exfalso. solve_addr. }
    iDestruct (interp_exec_noid with "Hw") as %->; [done|done|].
    iIntros (a0 W' Hin) "#Hfuture". iModIntro.
    assert (isO p = false) by (by eapply executeAllowed_nonO).
    iDestruct (interp_cap_disjoint with "Hw") as %[_ Hdisjoint]; first done.
    destruct g.
    - iDestruct (interp_global_world_free W W' with "Hw") as "Hw'"; first done.
      iApply (fundamental W'); eauto.
      iApply interp_lea; eauto.
    - iDestruct "Hfuture" as %Hrelated.
      iDestruct (interp_monotone_cap_nonheap with "Hw") as "Hw'";
        [exact Hdisjoint|exact Hrelated|].
      iApply (fundamental W'); eauto.
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

  Lemma jmp_or_fail_spec W C (w : LWord) φ :
    ⊢ (interp W C w
     -∗ (if decide (isCorrectPC (updatePcPerm w.(lw)))
         then
           (∃ p g b e a π,
               (⌜w = Cap p g b e a @@? π ∨ (∃ k, w = Sentry k p g b e a @@? π)⌝
                ∗ □ ∀ W' m, future_world g W W'
                          → ▷ (interp_expr_at (default m (jalr_target_mie w.(lw)))
                                 interp (interp_cont interp) W' C) (lupdatePcPerm w)))
         else trap_safe (lupdatePcPerm w) ⊤ φ ∗ PC ↦ₚ[th] lupdatePcPerm w
                          -∗ WP Exec @[th] {{ φ }} )).
  Proof.
    iIntros "#Hw".
    destruct (decide (isCorrectPC (updatePcPerm w.(lw)))).
    - inversion i.
      destruct w as [w π]; cbn in H.
      destruct w;inv H.
      + destruct p; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        iSplit;[eauto|]. iModIntro.
        iDestruct (interp_exec_cond with "Hw") as "Hexec";[auto|].
        iIntros (W' m) "Hfuture".
        iDestruct (exec_wp W C _ _ b e a with "Hexec Hfuture") as "Hwp"; first done.
        iNext. iApply "Hwp".
      + destruct p0; cbn in * ; simplify_eq.
        iExists _,_,_,_,_,_.
        rewrite /= interp_unfold /=.
        iSplit;[iPureIntro; right; eauto|]. iModIntro.
        iDestruct "Hw" as "(%Hnonheap & #Hw & _)".
        rewrite /enter_cond.
        iIntros (W' m) "Hfuture".
        destruct g0; iEval (cbn) in "Hw".
        * (* A Global sentry, at the running thread of its compartment. *)
          iApply later_interp_expr_at_thread_in. iIntros "#Hth".
          iSpecialize ("Hw" $! th with "Hth").
          iSpecialize ("Hw" with "Hfuture").
          iSpecialize ("Hw" $! Global (LocalityFlowsToReflexive Global) m).
          iExact "Hw".
        * iSpecialize ("Hw" with "Hfuture").
          iSpecialize ("Hw" $! Local (LocalityFlowsToReflexive Local) m).
          iExact "Hw".
    - iIntros "[Hfailed HPC]".
      by iApply (wp_notCorrectPC_trap with "HPC Hfailed").
  Qed.

End fundamental.
