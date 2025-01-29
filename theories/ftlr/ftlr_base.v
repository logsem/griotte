From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (pwl p = true -> g = Local).

  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (r_ih : leibnizO Reg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr),
            full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r_ih !! r = Some v⌝ → fixpoint interp1 W_ih v)
            -∗ registers_pointsto (<[PC:= WCap p_ih g_ih b_ih e_ih a_ih]> r_ih)
            -∗ region W_ih
            -∗ sts_full_world W_ih
            -∗ na_own logrel_nais ⊤
            -∗ □ interp W_ih (WCap p_ih g_ih b_ih e_ih a_ih)
            -∗ interp_conf W_ih))%I.

  Definition ftlr_instr (W : WORLD) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (i: instr) (ρ : region_type) (P : D) : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → isO p' = false
    → (∀ Wv : WORLD * leibnizO Word, Persistent (P Wv.1 Wv.2))
    → (if pwl p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : Mem, ρ ≠ Frozen g)
    → decodeInstrW w = i
    -> ftlr_IH
    -∗ fixpoint interp1 W (WCap p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → fixpoint interp1 W v)
    -∗ rel a p' (λ Wv, P Wv.1 Wv.2)
    -∗ □ (if decide (readAllowed_in_r_a (<[PC:=WCap p g b e a]> regs) a)
            then ▷ (∃ p'', ⌜ PermFlowsTo p' p'' ⌝ ∗ rcond p'' P interp)
            else emp)
    -∗ □ (if decide (writeAllowed_in_r_a (<[PC:=(WCap p g b e a)]> regs) a)
          then ▷ wcond P interp
          else emp)
    -∗ monoReq W a p' P
    -∗ (▷ (if decide (ρ = Temporary /\ pwl p' = true)
           then future_pub_mono (safeC P) w
           else future_priv_mono (safeC P) w))
    -∗ ▷ P W w
    -∗ sts_full_world W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ (WCap p g b e a)
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (regs' : Reg) (W' : WORLD),
                        full_map regs' ∧ registers_pointsto regs'
                        ∗ ⌜related_sts_priv_world W W'⌝
                        ∗ na_own logrel_nais ⊤
                        ∗ sts_full_world W' ∗ region W' }} }}.


End fundamental.
