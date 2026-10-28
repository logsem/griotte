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
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
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

  Definition ftlr_instr_base (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr : Prop) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
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

  Definition ftlr_instr (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base trusted_fault W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i) cstk Ws Cs.

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
    iExists W. iFrame. iSplit; first (iPureIntro; apply related_sts_pub_refl_world).
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

(** The old shape of the cases, while the cases are ported. *)
Section fundamental_old.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation V := (interpO Σ).
  #[local] Notation R := (regsO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Definition ftlr_IH_old : iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (r_ih : leibnizO LReg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr) (π_ih : option AId),
            full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ PC ↦ₚ[th] Cap p_ih g_ih b_ih e_ih a_ih @@? π_ih
            -∗ registers_pointsto r_ih
            -∗ world_interp W_ih C_ih
            -∗ interp_continuation cstk Ws Cs
            -∗ ⌜frame_match Ws Cs cstk W_ih C_ih⌝
            -∗ top_cmpt_untrusted interp W_ih C_ih cstk
            -∗ na_own (tpool th) ⊤
            -∗ ◯(CSTK)[th] cstk
            -∗ □ interp W_ih C_ih (Cap p_ih g_ih b_ih e_ih a_ih @@? π_ih)
            -∗ safe[th]))%I.

  (** The induction hypothesis gives its old shape. *)
  Lemma ftlr_IH_old_intro :
    ftlr_IH -∗ ftlr_IH_old.
  Proof.
    iIntros "#IH". iModIntro; iNext.
    iIntros (W C cstk Ws Cs regs p g b e a π)
      "%Hfull #Hregs HPC Hmap Hworld Hcont %Hframe #Htop Hown Hcstk #Hv".
    iApply ("IH" with "Hv"); iFrame "∗#".
    iSplit; last done.
    by iApply (interp_reg_intro with "Hregs").
  Qed.

  Definition ftlr_instr_base_old (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr : Prop) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
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
    -> ("#IH" ∷ ftlr_IH_old ∗
        "#IHnew" ∷ ftlr_IH ∗
        "#Htrap" ∷ trap_vector_safe trusted_fault (lword_of_word mtcc_vec) ∗
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
        "Hcont" ∷ interp_continuation cstk Ws Cs ∗
        "%Hframe" ∷ ⌜frame_match Ws Cs cstk W C⌝ ∗
        "#Htop" ∷ top_cmpt_untrusted interp W C cstk ∗
        "Hworld_interp" ∷ world_interp_open W C [LNonHeap a] ∗
        "Hown" ∷ na_own (tpool th) ⊤ ∗
        "Htframe" ∷ ◯(CSTK)[th] cstk ∗
        "Hstate" ∷ sts_state_std C (LNonHeap a) ρ ∗
        "HPC" ∷ PC ↦ₚ[th] (Cap p g b e a) ∗
        "Hmap" ∷ regs[th] regs)
    -∗ WP Instr Executable @[th] {{ v, WP Seq (griotte_lang.of_val v) @[th] {{ HO th }} }}.

  (** A fault in a case of the fundamental theorem, once the case has closed
      the world: trap entry leads to the safe trap vector, with safe
      registers, in an untrusted topmost compartment. *)
  Lemma ftlr_trap (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (regs : LReg) (w : LWord) :
    (∀ x : RegName, is_Some (regs !! x)) →
    frame_match Ws Cs cstk W C →
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) -∗
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    top_cmpt_untrusted interp W C cstk -∗
    PC ↦ₚ[th] w -∗
    regs[th] regs -∗
    world_interp W C -∗
    interp_continuation cstk Ws Cs -∗
    na_own (tpool th) ⊤ -∗
    ◯(CSTK)[th] cstk -∗
    WP Seq (Instr Faulted) @[th] {{ HO th }}.
  Proof.
    iIntros (Hfull Hframe) "Htrap Hreg Htop HPC Hmap Hworld Hcont Hown Hcstk".
    iApply (wp_trap with "HPC").
    iApply (interp_trap_safe_untrusted with
             "Htrap [Hreg] Htop [$Hmap $Hworld $Hcont $Hown $Hcstk]");
      [done | done | by iApply (interp_reg_intro with "Hreg") | done].
  Qed.

  Definition ftlr_instr_old (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base_old trusted_fault W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i) cstk Ws Cs.

End fundamental_old.
