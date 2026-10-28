From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.

Section fundamental.
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

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  Definition ftlr_IH: iProp Σ :=
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

  Definition ftlr_instr (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base trusted_fault W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i) cstk Ws Cs.

End fundamental.
