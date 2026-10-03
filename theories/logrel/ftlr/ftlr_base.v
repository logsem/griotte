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
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ registers_pointsto (<[PC:= WCap true p_ih g_ih b_ih e_ih a_ih @@? π_ih]> r_ih)
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
    -> ftlr_IH
    -∗ fixpoint interp1 W C (WCap true p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ rel C (LNonHeap a) p' (safeC P)
    -∗ □ (if decide (readAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a)
            then ▷ (rcond P C p' interp)
            else emp)
    -∗ □ (if decide (writeAllowed_a_in_lregs (<[PC:=WCap true p g b e a @@? None]> regs) a)
          then ▷ wcond P C interp
          else emp)
    -∗ monoReq W C a p' P
    -∗ ▷ WorldRes W C a p' (safeC P) w ρ
    -∗ interp_continuation cstk Ws Cs
    -∗ ⌜frame_match Ws Cs cstk W C⌝
    -∗ world_interp_open W C [LNonHeap a]
    -∗ na_own cerise_nais ⊤
    -∗ cstack_frag cstk
    -∗ sts_state_std C (LNonHeap a) ρ
    -∗ PC ↦ᵣ (WCap true p g b e a)
    -∗ ([∗ map] k↦y ∈ delete PC regs, k ↦ᵣ y)
    -∗ WP Instr Executable
        {{ v, WP Seq (griotte_lang.of_val v)
                 {{ v0, ⌜v0 = HaltedV⌝
                        → na_own cerise_nais ⊤}} }}.

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : LWord) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base W C regs p p' g b e a w ρ P (decodeInstrW w.(lw) = i) cstk Ws Cs.

  (* TODO: move to program_logic/rules/rules_base.v *)
  (** The identifier of the word read from a register, if it is a
      capability; like [read_reg_inr] for its other fields. *)
  Definition read_reg_prov (regs : LReg) (r : RegName) (π : option AId) : Prop :=
    match regs !! r with
    | Some (WCap _ _ _ _ _ _ @@? π') => π' = π
    | _ => True
    end.

  (* TODO: move to program_logic/rules/rules_base.v *)
  Lemma read_reg_prov_cap (regs : LReg) r p g b e a π :
    lw <$> regs !!ₗ r = Some (WCap true p g b e a) →
    read_reg_prov regs r π →
    regs !! r = Some (WCap true p g b e a @@? π).
  Proof.
    intros Hinr Hπ.
    destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hinr) as (_ & π' & Hr).
    rewrite /read_reg_prov Hr in Hπ. by subst π'.
  Qed.

  (* TODO: move to logrel/logrel.v *)
  (** The region of an address reached through a capability is the PC's
      region exactly when the address is the PC's and the capability has no
      identifier: a capability with an identifier reaches it under another key. *)
  Lemma addr_key_pc π ea pc_a :
    addr_key π ea = LNonHeap pc_a → π = None ∧ ea = pc_a.
  Proof. destruct π; cbn; intros; simplify_eq; done. Qed.

End fundamental.
