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
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
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

  Definition ftlr_instr_base
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr : Prop)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (Cap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! LNonHeap a = Some ρ
    → ρ ≠ Revoked
    → Pinstr
    -> ("#IH" ∷ ftlr_IH ∗
        "#Hinv_interp" ∷ interp W C (Cap p g b e a) ∗
        "#Hreg" ∷ (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) ∗
        "#Hinva" ∷ rel C (LNonHeap a) p' (safeC P) ∗
        "#Hrcond" ∷ □ (if decide (readAllowed_a_in_lregs regs a)
                       then ▷ (rcond P C p' interp)
                       else emp) ∗
        "#Hwcond" ∷ □ (if decide (writeAllowed_a_in_lregs regs a)
                       then ▷ wcond P C interp
                       else emp) ∗
        "#Hmono" ∷ monoReq W C a p' P ∗
        "WorldRes" ∷ ▷ WorldRes W C a p' (safeC P) w ρ ∗
        "Hworld_interp" ∷ world_interp_open W C [LNonHeap a] ∗
        "Hstate" ∷ sts_state_std C (LNonHeap a) ρ ∗
        "HPC" ∷ PC ↦ₚ[th] (Cap p g b e a) ∗
        "Hmap" ∷ regs[th] regs)
    -∗ WP Instr Executable @core[th]
       {{ v, ▷ ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C v }}.

  Definition ftlr_instr
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V)
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
