From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.

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
    {cstackg : CSTACKG Σ} {CL : CritLink Σ}
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
      word is safe to execute. *)
  Definition ftlr_IH : iProp Σ :=
    □ ▷ (∀ (W : WORLD) (C : CmptName) (w : LWord), interp W C w -∗ interp_expression W C w).

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

  (** The content of the region of the PC: a Global region holds the
      world-free image of its predicate. *)
  Definition pc_content (ρ : region_part) (W : WORLD) (C : CmptName) (P : V) (w : LWord)
    : iProp Σ :=
    match ρ with
    | InGlobal => P ∅ C w
    | InLocal => P W C w
    end.

  (** The opened region of the PC, at key [k] of part [ρ], holding [w]. *)
  Definition pc_open_def (W : WORLD) (C : CmptName) (k : LAddr) (p' : Perm) (P : V)
      (w : LWord) (ρ : region_part) : iProp Σ :=
    match ρ with
    | InGlobal => ⌜std W !! k ≠ Some Temporary⌝ ∗ PermRes C k p' (safeGC P) w
    | InLocal => TmpRes W C k p' (safeC P) w
    end.
  #[local] Definition pc_open_aux : seal (@pc_open_def). Proof. by eexists. Qed.
  Definition pc_open := pc_open_aux.(unseal).
  #[local] Definition pc_open_unseal : @pc_open = @pc_open_def := pc_open_aux.(seal_eq).

  (** The cell of the PC, with its content. *)
  Lemma pc_open_acc W C k p' P w ρ :
    pc_open W C k p' P w ρ -∗
    (k ↦ₖ w ∗ pc_content ρ W C P w) ∗
    (k ↦ₖ w ∗ pc_content ρ W C P w -∗ pc_open W C k p' P w ρ).
  Proof.
    rewrite pc_open_unseal. destruct ρ; cbn.
    - iIntros "($ & %HpO & $ & $)". iIntros "[$ $]". done.
    - iIntros "(%HpO & $ & $ & #Hmono)". iIntros "[$ $]". by iFrame "#".
  Qed.

  (** Opening the region of the PC. *)
  Lemma pc_open_intro W C k p' (P : V) w ρ :
    (ρ = InGlobal → std W !! k ≠ Some Temporary) →
    match ρ with
    | InGlobal => PermRes C k p' (safeGC P) w
    | InLocal => TmpRes W C k p' (safeC P) w
    end -∗
    pc_open W C k p' P w ρ.
  Proof.
    rewrite pc_open_unseal. iIntros (HnT) "H". destruct ρ; [|done].
    iFrame. iPureIntro. by apply HnT.
  Qed.

  (** Closing the region of the PC. *)
  Lemma pc_close W C k p' P w ρ :
    persistent_cond P →
    world_interp_open W C [k] -∗
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    world_interp W C.
  Proof.
    rewrite pc_open_unseal. iIntros (Hpers) "Hw #Hrel Hres".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    rewrite open_world_interp_empty.
    destruct ρ; cbn.
    - iDestruct "Hres" as "[%HnT Hres]".
      iDestruct (close_world_interp_permanent W C [] k p' (safeGC P) w
                   with "Hw Hrel Hres") as "[$ _]"; [set_solver|done].
    - iDestruct "Hrel" as "(Hrel & %HT & _)".
      iDestruct (close_world_interp_temporary W C [] k p' (safeC P) w
                   with "Hw Hrel Hres") as "[$ _]"; [set_solver|done].
  Qed.

  (** The cell of an opened region, with its content, for any new word. *)
  Lemma pc_open_acc_forall W C k p' P w ρ :
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    (k ↦ₖ w ∗ pc_content ρ W C P w) ∗
    (∀ w', k ↦ₖ w' ∗ pc_content ρ W C P w' -∗ pc_open W C k p' P w' ρ).
  Proof.
    rewrite pc_open_unseal. iIntros "#Hrel". destruct ρ; cbn.
    - iIntros "(%HnT & %HpO & Hc & HP)". iFrame "Hc HP".
      iIntros (w') "[Hc HP]". by iFrame "∗%".
    - iDestruct "Hrel" as "(_ & _ & #Hmono)".
      iIntros "(%HpO & Hc & HP & _)". iFrame "Hc HP".
      iIntros (w') "[Hc HP]". iFrame "∗%". iApply "Hmono".
  Qed.

  (** Closing an opened region, with other keys open. *)
  Lemma pc_close_next W C s k p' P w ρ :
    k ∉ s →
    persistent_cond P →
    world_interp_open W C ({[k]} ∪ s) -∗
    region_rel_part ρ W C k p' P -∗
    pc_open W C k p' P w ρ -∗
    world_interp_open W C s.
  Proof.
    rewrite pc_open_unseal. iIntros (Hks Hpers) "Hw #Hrel Hres".
    assert (∀ x, Persistent (safeGC P x)) as HpersG by (intros x; apply (Hpers (_, _, _))).
    assert (∀ x, Persistent (safeC P x)) as HpersL by (intros x; apply Hpers).
    destruct ρ; cbn.
    - iDestruct "Hres" as "[%HnT Hres]".
      iDestruct (close_world_interp_permanent W C s k p' (safeGC P) w
                   with "Hw Hrel Hres") as "[$ _]"; done.
    - iDestruct "Hrel" as "(Hrel & %HT & _)".
      iDestruct (close_world_interp_temporary W C s k p' (safeC P) w
                   with "Hw Hrel Hres") as "[$ _]"; done.
  Qed.

  Lemma pc_content_persistent ρ W C P w :
    persistent_cond P → Persistent (pc_content ρ W C P w).
  Proof. intros Hpers. destruct ρ; [apply (Hpers (∅, C, w))|apply (Hpers (W, C, w))]. Qed.

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
        "#Hinv_interp" ∷ interp W C (Cap p g b e a) ∗
        "#Hreg" ∷ (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) ∗
        "#Hinva" ∷ region_rel_part ρ W C (LNonHeap a) p' P ∗
        "#Hrcond" ∷ □ (if decide (readAllowed_a_in_lregs regs a)
                       then ▷ (rcond P C p' interp)
                       else emp) ∗
        "#Hwcond" ∷ □ (if decide (writeAllowed_a_in_lregs regs a)
                       then ▷ wcond P C interp
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

  (** The hand-off of a case that changes the world to a public future
      world [W']. *)
  Lemma ftlr_post_future W W' C v :
    related_sts_pub_world W W' →
    (∃ W'', ⌜related_sts_pub_world W' W''⌝ ∗ world_interp W'' C ∗ ftlr_post W'' C v) -∗
    ∃ W'', ⌜related_sts_pub_world W W''⌝ ∗ world_interp W'' C ∗ ftlr_post W'' C v.
  Proof.
    iIntros (Hrel) "(%W'' & %Hrel' & Hworld & Hpost)".
    iExists W''. iFrame. iPureIntro. by eapply related_sts_pub_trans_world.
  Qed.

End fundamental.

(** The post-state prints folded in the cases' goals. *)
#[global] Arguments ftlr_post : simpl never.
