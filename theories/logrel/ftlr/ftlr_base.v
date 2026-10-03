From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Export logrel.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
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

  (** An executable PC never points into the heap, so its region key is non-heap. *)
  Lemma interp_pc_addr_key W C p g b e a :
    isCorrectPC (WCap true p g b e a) ->
    interp W C (WCap true p g b e a) -∗
    ⌜addr_key W a = LNonHeap a⌝.
  Proof.
    iIntros (Hpc) "Hinterp".
    iDestruct (interp_cap_disjoint with "Hinterp") as %[_ Hdisjoint].
    { by inversion Hpc. }
    iPureIntro. apply (addr_key_disjoint W b e a Hdisjoint).
    apply elem_of_finz_seq_between, withinBounds_true_iff.
    exact (isCorrectPC_withinBounds true p g b e a Hpc).
  Qed.

  Definition ftlr_IH: iProp Σ :=
    (□ ▷ (∀ (W_ih : WORLD) (C_ih : CmptName) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (r_ih : leibnizO Reg)
            (p_ih : Perm) (g_ih : Locality) (b_ih e_ih a_ih : Addr),
            allocator_ctx -∗ full_map r_ih
            -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜r_ih !! r = Some v⌝ → interp W_ih C_ih v)
            -∗ registers_pointsto (<[PC:= WCap true p_ih g_ih b_ih e_ih a_ih]> r_ih)
            -∗ world_interp W_ih C_ih
            -∗ interp_continuation cstk Ws Cs
            -∗ ⌜frame_match Ws Cs cstk W_ih C_ih⌝
            -∗ na_own cerise_nais ⊤
            -∗ cstack_frag cstk
            -∗ □ interp W_ih C_ih (WCap true p_ih g_ih b_ih e_ih a_ih)
            -∗ interp_conf W_ih C_ih))%I.

  Definition ftlr_instr_base (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (ρ : region_type) (P : V) (Pinstr : Prop) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    validPCperm p g
    → (∀ x : RegName, is_Some (regs !! x))
    → isCorrectPC (WCap true p g b e a)
    → heap_addr_live (heap_std W) a
    → heap_wf (heap_std W)
    → (b <= a)%a ∧ (a < e)%a
    → PermFlowsTo p p'
    → (persistent_cond P)
    → (if isWL p then region_state_pwl W a else region_state_nwl W a g)
    → std W !! LNonHeap a = Some ρ
    → ρ ≠ Revoked
    → Pinstr
    -> allocator_ctx -∗ ftlr_IH
    -∗ fixpoint interp1 W C (WCap true p g b e a)
    -∗ (∀ (r : RegName) v, ⌜r ≠ PC⌝ → ⌜regs !! r = Some v⌝ → interp W C v)
    -∗ rel C (LNonHeap a) p' (safeC P)
    -∗ □ (if decide (readAllowed_a_in_regs (<[PC:=WCap true p g b e a]> regs) a)
            then ▷ (rcond P C p' interp)
            else emp)
    -∗ □ (if decide (writeAllowed_a_in_regs (<[PC:=(WCap true p g b e a)]> regs) a)
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

  Definition ftlr_instr (W : WORLD) (C : CmptName) (regs : leibnizO Reg)
    (p p' : Perm) (g : Locality) (b e a : Addr)
    (w : Word) (i: instr) (ρ : region_type) (P : V) (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    : Prop :=
    ftlr_instr_base W C regs p p' g b e a w ρ P (decodeInstrW w = i) cstk Ws Cs.

End fundamental.
