From iris.proofmode Require Import tactics.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.

Section fundamental.
 Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ}
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          {nainv: logrel_na_invs Σ}
          `{MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Notation D := (WORLD -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).


  Definition ftlr_instr (W : WORLD) (r : leibnizO Reg) (p : Perm)
        (g : Locality) (b e a : Addr) (w : Word) (i: instr) (ρ : region_type) (P : D) :=
    p = RX ∨ p = RWX ∨ (p = RWLX /\ g = Directed)
    → (∀ x : RegName, is_Some (r !! x))
    → isCorrectPC (inr (p, g, b, e, a))
    → (b <= a)%a ∧ (a < e)%a
    → (∀ Wv : WORLD * leibnizO Word, Persistent (P Wv.1 Wv.2))
    → (if pwl p then region_state_pwl_mono W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : Mem, ρ ≠ Monostatic g)
    → (∀ w, ρ ≠ Uninitialized w)
    → decodeInstrW w = i
    -> □ ▷ (∀ (a0 : WORLD) (a1 : leibnizO Reg) (a2 : Perm) (a3 : Locality) (a4 a5 a6 : Addr),
              full_map a1
              -∗ (∀ r0 : RegName, ⌜r0 ≠ PC⌝ → fixpoint interp1 a0 (a1 !r! r0))
                 -∗ registers_mapsto (<[PC:=inr (a2, a3, a4, a5, a6)]> a1)
                    -∗ region a0
                       -∗ sts_full_world a0
                          -∗ na_own logrel_nais ⊤
                             -∗ ⌜a2 = RX ∨ a2 = RWX ∨ a2 = RWLX ∧ a3 = Directed⌝
                                → □ region_conditions a0 a2 a3 a4 a5 -∗ interp_conf a0)
    -∗ region_conditions W p g b e
    -∗ (∀ r1 : RegName, ⌜r1 ≠ PC⌝ → ((fixpoint interp1) W) (r !r! r1))
    -∗ rel a (λ Wv, P Wv.1 Wv.2)
    -∗ rcond P interp
    -∗ □ (if decide (writeAllowed_in_r_a (<[PC:=inr (p, g, b, e, a)]> r) a) then wcond P interp else emp)
    -∗ (▷ (if decide (ρ = Monotemporary)
           then future_pub_a_mono a (λ Wv, P Wv.1 Wv.2) w
           else future_priv_mono (λ Wv, P Wv.1 Wv.2) w))
    -∗ ▷ P W w
    -∗ sts_full_world W
    -∗ na_own logrel_nais ⊤
    -∗ open_region a W
    -∗ sts_state_std a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ inr (p, g, b, e, a)
    -∗ ([∗ map] k↦y ∈ delete PC (<[PC:=inr (p, g, b, e, a)]> r), k ↦ᵣ y)
    -∗
        WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → ∃ (r1 : Reg) (W' : WORLD),
                        full_map r1
                        ∧ registers_mapsto r1
                                           ∗ ⌜related_sts_priv_world W W'⌝
                                           ∗ na_own logrel_nais ⊤
                                           ∗ sts_full_world W' ∗ region W' }} }}.

End fundamental.
