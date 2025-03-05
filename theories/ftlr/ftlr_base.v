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
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation D := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (D).

  Definition validPCperm (p : Perm) (g : Locality) :=
    executeAllowed p = true ∧ (isWL p = true -> g = Local).

  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (r_ih : leibnizO Reg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr),
            full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ registers_pointsto (<[PC:= WCap p_ih g_ih b_ih e_ih a_ih]> r_ih)
            -∗ region W_ih C_ih
            -∗ sts_full_world W_ih C_ih
            -∗ na_own logrel_nais ⊤
            -∗ □ interp W_ih C_ih (WCap p_ih g_ih b_ih e_ih a_ih)
            -∗ interp_conf W_ih C_ih))%I.

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (i: instr) (ρ : region_type) (P : D) : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap p g b e a)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → isO p' = false
    → (persistent_cond P)
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! a = Some ρ
    → ρ ≠ Revoked
    → (∀ g : Mem, ρ ≠ Frozen g)
    → decodeInstrW w = i
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
    -∗ (▷ (if decide (ρ = Temporary /\ isWL p' = true)
           then future_pub_mono C (safeC P) w
           else future_priv_mono C (safeC P) w))
    -∗ ▷ P W C w
    -∗ sts_full_world W C
    -∗ na_own logrel_nais ⊤
    -∗ open_region W C a
    -∗ sts_state_std C a ρ
    -∗ a ↦ₐ w
    -∗ PC ↦ᵣ (WCap p g b e a)
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (cap_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → na_own logrel_nais ⊤}} }}.
    (* -∗ WP Instr Executable *)
    (*     {{ v, WP Seq (cap_lang.of_val v) *)
    (*              {{ v0, ⌜v0 = HaltedV⌝ *)
    (*                     → ∃ (regs' : Reg) (W' : WORLD) (WC' : CVIEW), *)
    (*                       ∃ (regs' : Reg) (W' : WORLD) (WC WC' : CVIEW), *)
    (*                         ⌜W !! C = Some WC⌝ ∧ ⌜W' !! C = Some WC'⌝ *)
    (*                         ∧ full_map regs' ∧ registers_pointsto regs' *)
    (*                         ∗ ⌜related_sts_priv_world WC WC'⌝ *)
    (*                         ∗ na_own logrel_nais ⊤ *)
    (*                         ∗ sts_full_world W' ∗ region W' }} }}. *)


End fundamental.
