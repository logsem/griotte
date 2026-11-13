From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Export logrel.
From griotte Require Import ftlr_base.
Import CoreWPNotations.

(** * The contract of a case of the fundamental theorem

    Every case of the fundamental theorem proves [ftlr_contract], the case
    that the step lemma consumes. A case that does not see the posture of
    the thread nor the lent volatile part proves it through
    [ftlr_contract_intro]; a case that sees the posture only, through
    [ftlr_contract_intro_at]. *)

Section ftlr_contract.
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
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  (** The post-state of an environment call, at the post-step posture [m]
      (InterruptDisabled): the lent volatile part pinned by the step (MEPCC
      from the PC [pc], cause [MCAUSE_ECALL_MACHINE], value [MTVAL_NONE],
      MPIE the pre-step posture [b]), the PC at the trap vector, the safe
      registers, and the PC safe to execute at the resume, at [b]. *)
  Definition ftlr_ecall_post (m : InterruptStatus) (W : WORLD) (C : CmptName)
      (v : tval (kind_of th)) : iProp Σ :=
    ∃ (b : InterruptStatus) (pc : LWord) (regs : LReg),
      ⌜m = InterruptDisabled⌝ ∗
      ⌜v = tval_sw (kind_of th) Ecall NextIV⌝ ∗
      ⌜route_pre th b⌝ ∗
      ⌜∀ r, is_Some (regs !! r)⌝ ∗
      vol_lent (lmepcc_of_pc pc) (lword_of_word (WInt MCAUSE_ECALL_MACHINE)) MTVAL_NONE b ∗
      PC ↦ₚ[th] lword_of_word mtcc_vec ∗
      regs[th] regs ∗
      (∀ (r : RegName) (w : LWord), ⌜regs !! r = Some w⌝ → interp W C w) ∗
      interp_expr_at b interp interp_continuation W C (yield_resume_pc (lmepcc_of_pc pc)).

  (** The post-state of the step lemma: an environment call, or a case's
      post-state with the lent volatile part at InterruptDisabled. *)
  Definition ftlr_post_sw (m : InterruptStatus) (W : WORLD) (C : CmptName)
      (v : tval (kind_of th)) : iProp Σ :=
    ftlr_ecall_post m W C v ∨ (lent_if_dis m ∗ ftlr_post_at m W C v).

  (** The post-state of a case as the step lemma consumes it, for a
      post-state [Q] of the accessor's body: a public future world, its
      world interpretation, the MIE fragment at the post-step posture [m'],
      the lent volatile part back at InterruptEnabled, and [Q]. *)
  Definition ftlr_contract_post W C
      (Q : InterruptStatus → WORLD → tval (kind_of th) → iProp Σ)
      (v : tval (kind_of th)) : iProp Σ :=
    ▷ ∃ W' m',
      ⌜related_sts_pub_world W W'⌝ ∗
      world_interp W' C ∗
      (MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝) ∗
      (if m' is InterruptEnabled then vol_lent_any else True) ∗
      Q m' W' v.

  (** The contract of a case of the fundamental theorem, for the
      instruction [i] at the posture [m]: the safe PC and registers, the
      opened region of the PC, the MIE fragment and the lent volatile part,
      which goes back to the world accessor at InterruptEnabled. The
      post-state is the one of the accessor's body, [ftlr_post_sw]: an
      environment call, or a case's post-state with the lent part at
      InterruptDisabled. *)
  Definition ftlr_contract (m : InterruptStatus)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i : instr) (ρ : region_part) (P : V)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (Cap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → decodeInstrW w.(lw) = i
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
        "Hmap" ∷ regs[th] regs ∗
        "Hmie" ∷ MIE ↦ₜ[th] m ∗
        "%Hpre" ∷ ⌜route_pre th m⌝ ∗
        "Hvol" ∷ vol_lent_any)
    -∗ WP Instr Executable @core[th]
       {{ ftlr_contract_post W C (λ m' W', ftlr_post_sw m' W' C) }}.

  (** The precondition of [ftlr_contract] up to a tail [X], for the
      premises of [ftlr_contract_intro] and [ftlr_contract_intro_at]. *)
  Definition ftlr_contract_pre W C (regs : LReg) (p p' : Perm) (g : Locality) (b e a : Addr)
      (w : LWord) (ρ : region_part) (P : V) (X : iProp Σ) : iProp Σ :=
    "#IH" ∷ ftlr_IH ∗
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
    X.

  (** A part [Y] of the tail can be set aside. *)
  Lemma ftlr_contract_pre_frame {W C regs p p' g b e a w ρ P} (X X' Y : iProp Σ) :
    (X ⊢ X' ∗ Y) →
    ftlr_contract_pre W C regs p p' g b e a w ρ P X ⊢
    ftlr_contract_pre W C regs p p' g b e a w ρ P X' ∗ Y.
  Proof.
    intros HX. rewrite /ftlr_contract_pre HX. by rewrite !assoc.
  Qed.

  (** The post-state of a case that sees neither the posture nor the lent
      volatile part, at a value. *)
  Definition ftlr_contract_intro_post W C (v : tval (kind_of th)) : iProp Σ :=
    ▷ ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗ ftlr_post W' C v.

  (** A case that does not touch the volatile registers frames the lent
      part: back to the accessor at InterruptEnabled, in the post-state at
      InterruptDisabled. *)
  Lemma vol_lent_frame m :
    vol_lent_any -∗ (if m is InterruptEnabled then vol_lent_any else True) ∗ lent_if_dis m.
  Proof. iIntros "H". destruct m; iFrame. Qed.

  (** A case that sees the posture [m] but not the lent volatile part
      frames the lent part. *)
  Lemma ftlr_contract_intro_at m W C regs p p' g b e a w i ρ P :
    (validPCperm p g →
     (∀ x : RegName, is_Some (regs !! x)) →
     isCorrectPC (Cap p g b e a) →
     (b <= a)%a ∧ (a < e)%a →
     PermFlowsTo p p' →
     persistent_cond P →
     decodeInstrW w.(lw) = i →
     ftlr_contract_pre W C regs p p' g b e a w ρ P
       ("Hmap" ∷ regs[th] regs ∗
        "Hmie" ∷ MIE ↦ₜ[th] m ∗
        "%Hpre" ∷ ⌜route_pre th m⌝) -∗
     WP Instr Executable @core[th]
       {{ v, ▷ ∃ W' m', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗
                        MIE ↦ₜ[th] m' ∗ ⌜route_pre th m'⌝ ∗ ftlr_post_at m' W' C v }}) →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hcase Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "Hpre".
    iDestruct (ftlr_contract_pre_frame _ ("Hmap" ∷ regs[th] regs ∗ "Hmie" ∷ MIE ↦ₜ[th] m ∗
                                 "%Hpre" ∷ ⌜route_pre th m⌝) vol_lent_any
                with "Hpre") as "[Hpre Hvol]"; first by iIntros "($ & $ & $ & $)".
    iApply (wp_wand with "[Hpre]"); first by iApply (Hcase with "Hpre").
    iIntros (v) "Hpost !>".
    iDestruct "Hpost" as (W' m' Hrel) "(Hworld & Hmie & %Hroute' & Hpost)".
    iDestruct (vol_lent_frame m' with "Hvol") as "[Hvol Hlent]".
    iExists W', m'. iFrame "Hworld Hmie Hvol".
    iSplit; first done. iSplit; first done.
    iRight. iFrame.
  Qed.

  (** A case that sees neither the posture nor the lent volatile part
      frames both: the posture is kept, and the next-PC witness holds at
      every posture. *)
  Lemma ftlr_contract_intro m W C regs p p' g b e a w i ρ P :
    (validPCperm p g →
     (∀ x : RegName, is_Some (regs !! x)) →
     isCorrectPC (Cap p g b e a) →
     (b <= a)%a ∧ (a < e)%a →
     PermFlowsTo p p' →
     persistent_cond P →
     decodeInstrW w.(lw) = i →
     ftlr_contract_pre W C regs p p' g b e a w ρ P ("Hmap" ∷ regs[th] regs) -∗
     WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}) →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hcase. apply ftlr_contract_intro_at.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "Hpre".
    iDestruct (ftlr_contract_pre_frame _ ("Hmap" ∷ regs[th] regs) (MIE ↦ₜ[th] m ∗ ⌜route_pre th m⌝)
                with "Hpre") as "[Hpre [Hmie %Hroute] ]"; first by iIntros "[$ $]".
    iApply (wp_wand with "[Hpre]"); first by iApply (Hcase with "Hpre").
    iIntros (v) "Hpost". iNext.
    iDestruct "Hpost" as (W') "(%Hrel & Hworld & Hpost)".
    iExists W', m. iFrame "Hworld Hmie". iSplit; first done. iSplit; first done.
    destruct v; try (rewrite ftlr_post_at_eq //; iExact "Hpost").
    rewrite /ftlr_post_at /ftlr_post.
    iDestruct "Hpost" as (regs' pc) "(Hfull & HPC & Hregs & Hreg' & Hpc)".
    iExists regs', pc. iFrame. by iApply interp_expression_at.
  Qed.

End ftlr_contract.
