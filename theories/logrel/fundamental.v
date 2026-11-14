From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre lifting.
From griotte Require Export logrel interp_weakening monotone ftlr_base ftlr_step.
From griotte Require Import ftlr_dispatch.
Import CoreWPNotations.

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
      "(#Hthread & #Htrap & #Hreg & #Htop & HPC & Hregs & Hhwm & Hwres & Hcred & Hcont & Hown
        & Hcstk & %Hframe & %Hpre & Hmie & Hheld)".
    iApply (ftlr_step (th := t) W C m w cstk Ws Cs regs ftlr_case Hframe Hpre
              with "[] Hthread Htrap [] Hw Hreg Htop HPC Hregs Hhwm [$Hwres $Hcred] Hcont Hown
                    Hcstk Hheld Hmie").
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
