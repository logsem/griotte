From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
  Implicit Types interp : (V).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (r_ih : leibnizO LReg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr) (π_ih : option AId),
            full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ PC ↦ₚ WCap true p_ih g_ih b_ih e_ih a_ih @@? π_ih
            -∗ registers_pointsto r_ih
            -∗ world_interp W_ih C_ih
            -∗ interp_continuation cstk Ws Cs
            -∗ ⌜frame_match Ws Cs cstk W_ih C_ih⌝
            -∗ na_own cerise_nais ⊤
            -∗ cstack_frag cstk
            -∗ □ interp W_ih C_ih (WCap true p_ih g_ih b_ih e_ih a_ih @@? π_ih)
            -∗ interp_conf W_ih C_ih))%I.

  Definition ftlr_instr_base (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (ρ : region_type) (P : V) (Pinstr : Prop) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap true p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! LNonHeap a = Some ρ
    → ρ ≠ Revoked
    → Pinstr
    -> ("#IH" ∷ ftlr_IH ∗
        "#Hinv_interp" ∷ interp W C (WCap true p g b e a) ∗
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
        "Hworld_interp" ∷ world_interp_open W C [LNonHeap a] ∗
        "Hown" ∷ na_own cerise_nais ⊤ ∗
        "Htframe" ∷ cstack_frag cstk ∗
        "Hstate" ∷ sts_state_std C (LNonHeap a) ρ ∗
        "HPC" ∷ PC ↦ₚ (WCap true p g b e a) ∗
        "Hmap" ∷ ([∗ map] k↦y ∈ regs, k ↦ᵣ y))
    -∗ WP Instr Executable
        {{ v, WP Seq (griotte_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → na_own cerise_nais ⊤}} }}.

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i) cstk Ws Cs.

End fundamental.
