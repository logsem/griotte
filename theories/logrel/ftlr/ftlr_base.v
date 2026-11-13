From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel region_open.
From griotte Require Import monotone interp_weakening.

(** * The WP of a thread at the core link

    [WP e @core[th] {{ Φ }}] is the WP of thread [th] at [link_core], where
    the cases of the fundamental theorem run their instruction. The
    notations are in a module, imported only by the files of the
    fundamental theorem. *)
Module CoreWPNotations.
  Notation "'WP' e '@core[' th ] {{ Φ } }" :=
    (@wp _ _ _ _
       (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th) (CL := link_core)))
       NotStuck ⊤ e%E Φ)
    (at level 20, th custom thread, e, Φ at level 200,
     format "'[hv' 'WP'  e  '/' '@core[' th ]  '/' {{  Φ  } } ']'") : bi_scope.
  Notation "'WP' e '@core[' th ] {{ v , Q } }" :=
    (@wp _ _ _ _
       (@wp' _ _ _ (memG_irisG (th := th) (ceriseg := ceriseG_of th) (CL := link_core)))
       NotStuck ⊤ e%E (λ v, Q))
    (at level 20, th custom thread, e, Q at level 200, v at level 200 as pattern,
     format "'[hv' 'WP'  e  '/' '@core[' th ]  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
End CoreWPNotations.
Import CoreWPNotations.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  (** The induction hypothesis of the fundamental theorem: later, every safe
      word is safe to execute, at every thread. *)
  Definition ftlr_IH : iProp Σ :=
    □ ▷ (∀ (t : Thread) (W : WORLD) (C : CmptName) (w : LWord),
           interp (th := t) W C w -∗ interp_expression (th := t) W C w).

  (** The post-state of an instruction step in a case of the fundamental
      theorem, at the post-world [W]: after [NextIV], the PC and the
      registers, the registers safe and the PC safe to execute; after
      [FaultedV], the PC and the registers, safe up to the world's filter;
      after [HaltedV], nothing; a switch value: [False]. *)
  Definition ftlr_post (W : WORLD) (C : CmptName) (v : tval (kind_of th)) : iProp Σ :=
    match v with
    | NextIV =>
        ∃ (regs : LReg) (pc : LWord),
          ⌜∀ r, is_Some (regs !! r)⌝ ∗
          PC ↦ₚ[th] pc ∗
          regs[th] regs ∗
          (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) ∗
          interp_expression W C pc
    | FaultedV =>
        ∃ (regs : LReg) (pc : LWord),
          PC ↦ₚ[th] pc ∗
          regs[th] regs ∗
          interp_reg interp W C regs
    | HaltedV => True
    | TSwV _ => False
    end.

  (** The post-state of an instruction step that may change the posture:
      after [NextIV], the PC is safe to execute at the post-step posture
      [m]; otherwise as [ftlr_post]. *)
  Definition ftlr_post_at (m : InterruptStatus) (W : WORLD) (C : CmptName)
      (v : tval (kind_of th)) : iProp Σ :=
    match v with
    | NextIV =>
        ∃ (regs : LReg) (pc : LWord),
          ⌜∀ r, is_Some (regs !! r)⌝ ∗
          PC ↦ₚ[th] pc ∗
          regs[th] regs ∗
          (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) ∗
          interp_expr_at m interp interp_continuation W C pc
    | _ => ftlr_post W C v
    end.

  (** The hand-off of a case, after the next instruction. *)
  Lemma ftlr_post_next W C (regs : LReg) (pc : LWord) :
    (∀ r, is_Some (regs !! r)) →
    PC ↦ₚ[th] pc -∗
    regs[th] regs -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp_expression W C pc -∗
    world_interp W C -∗
    ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C NextIV.
  Proof.
    iIntros (Hfull) "HPC Hregs Hreg Hpc Hworld".
    iExists W. iFrame. iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    by iPureIntro.
  Qed.

  (** The hand-off of a case, after a fault. *)
  Lemma ftlr_post_fault W C (regs : LReg) (pc : LWord) :
    (∀ r, is_Some (regs !! r)) →
    PC ↦ₚ[th] pc -∗
    regs[th] regs -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    world_interp W C -∗
    ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C FaultedV.
  Proof.
    iIntros (Hfull) "HPC Hregs Hreg Hworld".
    iExists W. iFrame "HPC Hregs Hworld". iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    by iApply (interp_reg_intro with "Hreg").
  Qed.

  (** A thread that may run at InterruptEnabled is a user thread, so its
      compartment has no context-switch thread. *)
  Lemma route_pre_enabled_sep C :
    route_pre th InterruptEnabled → th ∈ cmpt_threads C → CtxSwitch ∉ cmpt_threads C.
  Proof.
    intros Hpre Hin. destruct th as [n|]; first by eapply cmpt_threads_sep.
    by specialize (Hpre eq_refl).
  Qed.

  (** A jump through a sentry of kind [k] valid in [C] keeps the thread at a
      posture where it may run. *)
  Lemma route_pre_sentry m C k :
    route_pre th m →
    th ∈ cmpt_threads C →
    (sentry_kind_mie k = Some InterruptEnabled → CtxSwitch ∉ cmpt_threads C) →
    route_pre th (default m (sentry_kind_mie k)).
  Proof.
    intros Hpre Hin Hsep.
    destruct (sentry_kind_mie k) as [ [|] |] eqn:Hk; cbn; [|done|done].
    intros ->. exfalso. exact (Hsep eq_refl Hin).
  Qed.

  (** The post-state of [ftlr_post_at] is that of [ftlr_post] after a
      fault or a halt. *)
  Lemma ftlr_post_at_eq m W C v : v ≠ NextIV → ftlr_post_at m W C v ⊣⊢ ftlr_post W C v.
  Proof. by destruct v. Qed.

  (** The hand-off of a case that sees the posture, after the next
      instruction at the posture [m]. *)
  Lemma ftlr_post_at_next m W C (regs : LReg) (pc : LWord) :
    (∀ r, is_Some (regs !! r)) →
    route_pre th m →
    PC ↦ₚ[th] pc -∗
    regs[th] regs -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    interp_expr_at m interp interp_continuation W C pc -∗
    world_interp W C -∗
    MIE ↦ₜ[th] m -∗
    ∃ W' m', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗
             MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝ ∗ ftlr_post_at m' W' C NextIV.
  Proof.
    iIntros (Hfull Hpre) "HPC Hregs Hreg Hpc Hworld Hmie".
    iExists W, m. iFrame "Hworld Hmie".
    iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    iSplit; first done.
    rewrite /ftlr_post_at. iExists regs, pc. iFrame. by iPureIntro.
  Qed.

  (** The hand-off of a case that sees the posture, after a fault at the
      posture [m]. *)
  Lemma ftlr_post_at_fault m W C (regs : LReg) (pc : LWord) :
    (∀ r, is_Some (regs !! r)) →
    route_pre th m →
    PC ↦ₚ[th] pc -∗
    regs[th] regs -∗
    (∀ (r : RegName) (v : LWord), ⌜regs !! r = Some v⌝ → interp W C v) -∗
    world_interp W C -∗
    MIE ↦ₜ[th] m -∗
    ∃ W' m', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗
             MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝ ∗ ftlr_post_at m' W' C FaultedV.
  Proof.
    iIntros (Hfull Hpre) "HPC Hregs Hreg Hworld Hmie".
    iExists W, m. rewrite ftlr_post_at_eq //. iFrame "HPC Hregs Hworld Hmie".
    iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    iSplit; first done.
    by iApply (interp_reg_intro with "Hreg").
  Qed.

  (** The hand-off of a case, after a halt. *)
  Lemma ftlr_post_halt W C :
    world_interp W C -∗
    ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C HaltedV.
  Proof.
    iIntros "Hworld". iExists W. iFrame. iPureIntro.
    apply related_sts_pub_refl_world.
  Qed.

End fundamental.

(** The post-states print folded in the cases' goals. *)
#[global] Arguments ftlr_post : simpl never.
#[global] Arguments ftlr_post_at : simpl never.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (CSTK -n> list WORLD -n> WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Lemma interp_weakening W C t p p' g g' b b' e e' a a' π :
    (b <= b')%a ->
    (e' <= e)%a ->
    subseg_heap_base π b b' e' ->
    PermFlowsTo p' p ->
    LocalityFlowsTo g' g ->
    ftlr_IH -∗
    thread_in th C -∗
    interp W C (WCap t p g b e a @@? π) -∗
    interp W C (WCap t p' g' b' e' a' @@? π).
  Proof.
    intros Hb He Hgate Hp Hl. iIntros "#IH #Hth HA".
    destruct t; last (iApply interp_untagged; done).
    destruct (isO p') eqn:HpO'.
    { iDestruct (interp_cap_heap_conditions with "HA") as "[#Hvalid #Hcoverage]".
      iEval (rewrite interp_unfold interp1_eq HpO').
      iSplit.
      - iApply (heap_cap_ok_perm with "[]"); first exact Hp.
        by iApply (heap_cap_ok_subseg with "Hvalid").
      - destruct (decide (b' < e')%a) as [Hbe'|Hbe']; cycle 1.
        { rewrite (finz_seq_between_empty b' e'); auto; solve_addr. }
        rewrite (isWithin_finz_seq_between_decomposition b' e' b e); last solve_addr.
        iEval (rewrite !big_sepL_app) in "Hcoverage". iDestruct "Hcoverage" as "[_ [Hcov _] ]".
        iApply (big_sepL_impl with "Hcov"). iIntros "!>" (k x Hx) "Hx %Hheap".
        iApply (heap_cap_O_key_weakening with "(Hx [//])"); done. }
    destruct (isO p) eqn:HpO.
    { eapply notisO_flowsfrom in Hp ; eauto; congruence. }
    { iApply (interp_weakeningEO _ _ true p p' g g' with "Hth HA"); eauto. }
  Qed.

End fundamental.

(** A sentry made from a capability: a Global one runs at every thread of
    the compartment, through the induction hypothesis at that thread. *)
Section fundamental_sentry.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma interp_weakeningSentry W C sk t p g g' b b' e e' a a' :
      not_heap_range b' e' ->
      isO p = false ->
      (b <= b')%a ->
      (e' <= e)%a ->
      LocalityFlowsTo g' g ->
      (sentry_kind_mie sk = Some InterruptEnabled → CtxSwitch ∉ cmpt_threads C) ->
      ftlr_IH -∗
      interp W C (WCap t p g b e a) -∗
      interp W C (WSentry sk t p g' b' e' a').
  Proof.
    intros Hsentry HpnotO Hb He Hl Hsep.
    iIntros "#IH #HA".
    destruct t; last (iApply interp_untagged; done).
    iEval (rewrite interp_unfold /=).
    iSplit; first done.
    iSplit; last done.
    destruct g'; cbn.
    - (* A Global sentry, at every thread [t'] of [C]. *)
      destruct g; cbn in Hl; last done.
      iIntros "!>" (t') "#Hth'". rewrite /enter_cond.
      iIntros (W') "_". iIntros (g'' Hflows m). iNext.
      iApply (interp_expression_at (th := t')).
      iApply ("IH" $! t' W' C).
      iDestruct (interp_global_thread_world_free th t' W W' C (Cap p Global b e a)
                   with "HA") as "HA'"; first done.
      iApply (interp_weakeningEO (th := t') W' C true p p Global g'' b b' e e' a a' None
                with "Hth' HA'");
        [done|done|done|done|apply subseg_heap_base_noid|apply PermFlowsToReflexive|done].
    - (* A Local sentry, at the holder's thread, in the public futures. *)
      iIntros "!>". rewrite /enter_cond.
      iIntros (W') "%Hfuture". iIntros (g'' Hflows m).
      iApply later_interp_expr_at_thread_in. iIntros "#Hth". iNext.
      iApply interp_expression_at.
      iApply ("IH" $! th W' C).
      destruct g''; cbn in Hflows; try done.
      iAssert (interp W' C (Cap p g b e a))%I as "#HA'".
      { destruct g.
        - iApply (interp_global_world_free with "HA"). done.
        - iApply (interp_monotone_cap_valid with "[] HA"). done. }
      iApply (interp_weakeningEO W' C true p p g Local b b' e e' a a' None
                with "Hth HA'");
        [done|done|done|done|apply subseg_heap_base_noid|apply PermFlowsToReflexive|by destruct g].
  Qed.

End fundamental_sentry.
