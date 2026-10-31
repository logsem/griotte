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
    (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th) (CL := link_core)))
       NotStuck ⊤ e%E Φ)
    (at level 20, th custom thread, e, Φ at level 200,
     format "'[hv' 'WP'  e  '/' '@core[' th ]  '/' {{  Φ  } } ']'") : bi_scope.
  Notation "'WP' e '@core[' th ] {{ v , Q } }" :=
    (@wp _ _ _ _ (@wp' _ _ _ (memG_irisG (ceriseg := ceriseG_of th) (CL := link_core)))
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
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
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
      after [HaltedV], nothing. *)
  Definition ftlr_post (W : WORLD) (C : CmptName) (v : griotte_lang.val) : iProp Σ :=
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
    end.

  Definition ftlr_instr_base
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (P : V) (Pinstr : Prop)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (Cap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → Pinstr
    -> ("#IH" ∷ ftlr_IH ∗
        "#Hthread" ∷ thread_in th C ∗
        "#Hinv_interp" ∷ interp W C (Cap p g b e a) ∗
        "#Hreg" ∷ (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) ∗
        "#Hinva" ∷ region_rel_part ρ W C (LNonHeap a) p' P ∗
        "#Hrcond" ∷ □ (if decide (readAllowed_a_in_lregs regs a)
                       then ▷ (rcond_l P C p' interp)
                       else emp) ∗
        "#Hwcond" ∷ □ (if decide (writeAllowed_a_in_lregs regs a)
                       then ▷ (if isWL p then wcond_wl P C interp else wcond_nwl P C interp)
                       else emp) ∗
        "WorldRes" ∷ ▷ pc_open W C (LNonHeap a) p' P w ρ ∗
        "Hworld_interp" ∷ world_interp_open W C [LNonHeap a] ∗
        "HPC" ∷ PC ↦ₚ[th] (Cap p g b e a) ∗
        "Hmap" ∷ regs[th] regs)
    -∗ WP Instr Executable @core[th]
       {{ v, ▷ ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C v }}.

  Definition ftlr_instr
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_part) (P : V)
    : Prop :=
    ftlr_instr_base W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i).

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

  (** The hand-off of a case, after a halt. *)
  Lemma ftlr_post_halt W C :
    world_interp W C -∗
    ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C HaltedV.
  Proof.
    iIntros "Hworld". iExists W. iFrame. iPureIntro.
    apply related_sts_pub_refl_world.
  Qed.

End fundamental.

(** The post-state prints folded in the cases' goals. *)
#[global] Arguments ftlr_post : simpl never.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
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
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : CritLink Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma interp_weakeningSentry W C sk t p g g' b b' e e' a a' :
      not_heap_range b' e' ->
      isO p = false ->
      (b <= b')%a ->
      (e' <= e)%a ->
      LocalityFlowsTo g' g ->
      ftlr_IH -∗
      interp W C (WCap t p g b e a) -∗
      interp W C (WSentry sk t p g' b' e' a').
  Proof.
    intros Hsentry HpnotO Hb He Hl.
    iIntros "#IH #HA".
    destruct t; last (iApply interp_untagged; done).
    iEval (rewrite interp_unfold /=).
    iSplit; first done.
    destruct g'; cbn.
    - (* A Global sentry, at every thread [t'] of [C]. *)
      destruct g; cbn in Hl; last done.
      iIntros "!>" (t') "#Hth'". rewrite /enter_cond.
      iIntros (W') "_". iIntros (g'' Hflows). iNext.
      iApply ("IH" $! t' W' C).
      iDestruct (interp_global_thread_world_free th t' W W' C (Cap p Global b e a)
                   with "HA") as "HA'"; first done.
      iApply (interp_weakeningEO (th := t') W' C true p p Global g'' b b' e e' a a' None
                with "Hth' HA'");
        [done|done|done|done|apply subseg_heap_base_noid|apply PermFlowsToReflexive|done].
    - (* A Local sentry, at the holder's thread, in the public futures. *)
      iIntros "!>". rewrite /enter_cond.
      iIntros (W') "%Hfuture". iIntros (g'' Hflows).
      iApply later_interp_expr_thread_in. iIntros "#Hth". iNext.
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
