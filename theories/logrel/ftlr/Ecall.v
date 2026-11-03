From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Export logrel.
From griotte Require Import ftlr_base interp_weakening rules_Ecall.
Import CoreWPNotations.

(** * The environment call in the fundamental theorem

    The step lemma dispatches [Ecall] here, before the table of the other
    cases: the environment call consumes the lent volatile part, and its
    post-state keeps the values that the step pins in it. *)

(** A correct PC is its own MEPCC. *)
Lemma lmepcc_of_pc_correct p g b e a :
  isCorrectPC (Cap p g b e a) → lmepcc_of_pc (Cap p g b e a) = Cap p g b e a.
Proof.
  intros Hpc%isCorrectPCb_isCorrectPC.
  rewrite /lmepcc_of_pc /mepcc_of_pc /=. cbn in Hpc. by rewrite Hpc.
Qed.

(** The PC after an environment call at a correct PC is a capability with
    the same permission, locality and bounds. *)
Lemma yield_resume_pc_cap p g b e a :
  ∃ a', yield_resume_pc (Cap p g b e a) = Cap p g b e a'.
Proof.
  rewrite /yield_resume_pc /incrementPC /incrementPC_gen /=.
  destruct (a + 1)%a as [a'|]; eauto.
Qed.

(** The value of an environment call, by kind. *)
Lemma tval_sw_ecall_cases (th : Thread) (v : tval (kind_of th)) :
  v = tval_sw (kind_of th) Ecall NextIV →
  (th ≠ CtxSwitch ∧ v = YieldV) ∨ (th = CtxSwitch ∧ v = NextIV).
Proof.
  intros ->. destruct (decide (th = CtxSwitch)) as [Hth | Hth].
  - right. split; first done. by apply tval_sw_ecall_ctx.
  - left. split; first done. by apply tval_sw_ecall_user.
Qed.

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

  (** The case of the environment call: as [ftlr_instr_at], with the lent
      volatile part, and the post-state [ftlr_ecall_post] at
      InterruptDisabled. *)
  Definition ftlr_ecall_at (m : InterruptStatus)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (P : V)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (Cap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → decodeInstrW w.(lw) = Ecall
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
       {{ v, ▷ ∃ W', ⌜related_sts_pub_world W W'⌝ ∗ world_interp W' C ∗
                     MIE ↦ₜ[th] InterruptDisabled ∗
                     ftlr_ecall_post InterruptDisabled W' C v }}.

  Lemma ecall_case (m : InterruptStatus) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_part) (P : V) :
    ftlr_ecall_at m W C regs p p' g b e a w ρ P.
  Proof.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".
    iDestruct (pc_open_acc with "WorldRes") as " [ (Ha & Hinterp) WorldRes ]".
    iApply (wp_ecall (th := th) with "[$HPC $Ha $Hmie $Hvol]"); [done | done |].
    iIntros "!> (HPC & Ha & Hmie & Hvol)".
    iDestruct ("WorldRes" with "[$Ha $Hinterp]") as "WorldRes".
    iDestruct (pc_close with "Hworld_interp Hinva WorldRes") as "Hworld_interp"; eauto.
    iNext. iExists W. iFrame "Hworld_interp Hmie".
    iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
    iExists m, (Cap p g b e a), regs. iFrame "Hvol HPC Hmap Hreg".
    iSplit; first done. iSplit; first done. iSplit; first done. iSplit; first done.
    rewrite lmepcc_of_pc_correct //.
    destruct (yield_resume_pc_cap p g b e a) as [a' ->].
    iApply interp_expression_at. iApply "IH".
    by iApply (interp_next_PC with "Hinv_interp").
  Qed.

End fundamental.
