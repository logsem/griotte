From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {cstackg : CSTACKG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (r_ih : leibnizO Reg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr),
            full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ registers_pointsto (<[PC:= WCap p_ih g_ih b_ih e_ih a_ih]> r_ih)
            -∗ region W_ih C_ih
            -∗ sts_full_world W_ih C_ih
            -∗ interp_continuation cstk Ws Cs
            -∗ ⌜frame_match Ws Cs cstk W_ih C_ih⌝
            -∗ na_own logrel_nais ⊤
            -∗ cstack_frag cstk
            -∗ □ interp W_ih C_ih (WCap p_ih g_ih b_ih e_ih a_ih)
            -∗ interp_conf W_ih C_ih))%I.

  Definition ftlr_instr_base (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P : V) (Pinstr : Prop) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → isO p' = false
    → (persistent_cond P)
    (* → (if isWL p then region_state_pwl W a else region_state_nwl W a g) *)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → Pinstr
    -> ftlr_IH
    -∗ fixpoint interp1 W C (WCap p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ rel C a p' (safeC P)
    -∗ □ (if decide (readAllowed_a_in_regs (<[PC:=WCap p g b e a]> regs) a)
            then ▷ (rcond P C p' interp)
            else emp)
    -∗ □ (if decide (writeAllowed_a_in_regs (<[PC:=(WCap p g b e a)]> regs) a)
          then ▷ wcond P C interp
          else emp)
    -∗ monoReq W C a p' P
    -∗ (▷ (if decide (ρ = Temporary)
           then (if isWL p'
                 then future_pub_mono C (safeC P) w
                 else (if isDL p' then future_pub_mono C (safeC P) w else future_priv_mono C (safeC P) w))
           else future_priv_mono C (safeC P) w))
    -∗ ▷ P W C w
    -∗ interp_continuation cstk Ws Cs
    -∗ ⌜frame_match Ws Cs cstk W C⌝
    -∗ sts_full_world W C
    -∗ na_own logrel_nais ⊤
    -∗ cstack_frag cstk
    -∗ open_region W C a
    -∗ sts_state_std C a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ (WCap p g b e a)
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → na_own logrel_nais ⊤}} }}.

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base W C regs p p' g b e a w ρ P (decodeInstrW w = i) cstk Ws Cs.

End fundamental.
