From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs capability_monotonicity_base rules_regs_steps.
#[local] Open Scope capability_scope.

(** * Subseg

    Subseg is stepped by [iInstr] with the register rules of [rules_regs.v],
    from its register steps in closed form ([rules_regs_steps.v]). The rule
    below has a witness: the rebase on an identifier. *)

(** ** The rules with a witness *)

Section subseg_witness_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** The rebase: an identifier-less source narrowed to exactly the range of
      a non-dead identifier [ι] takes [ι]. The source is not executable,
      since an identified word never is. The allocate step
      ([rules_registry]) gives [alloc_obj] and the status token. *)
  Lemma wp_subseg_rebase E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 p g b e a w1 n1 w2 n2 a1 a2 pc_a'
      ι q s dq :
    decodeInstrW w.(lw) = Subseg dst dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ Cap p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ alloc_obj ι a1 a2
        ∗ ι ↦st{q} s }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ (Cap p g a1 a2 a) @@ ι
          ∗ alloc_obj ι a1 a2
          ∗ ι ↦st{q} s
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hs Hpx Hpc_a' Hcnull Hcnull' Hcnull'' Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & #Hobj & Htok) HΦ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%Hne12 & %Hne1d & %Hne2d)]".
    set (regs := <[r1 := WInt n1 @@? π1]> (<[r2 := WInt n2 @@? π2]>
                   (<[dst := Cap p g b e a @@? None]> (∅ : LReg)))).
    assert (regs !! dst = Some (Cap p g b e a @@? None)) as Hd.
    { rewrite /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r1) = Some n1) as Hz1.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r2) = Some n2) as Hz2.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    pose proof (subseg_agree_cap pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst dst
                  (inr r1) (inr r2) true p g b e a None n1 n2 a1 a2
                  ltac:(by rewrite llookup_reg_not_cnull) Hz1 Hz2 Hn1 Hn2) as Hagree.
    rewrite Hwb Hle' in Hagree.
    (* The agreement reads only the physical word: the identifier [ι] of the
       written word is not in it. *)
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ regs dst (λ _, Cap p g a1 a2 a @@ ι) 1 (λ S, S dst)
              (λ v, v = Cap p g a1 a2 a @@ ι) (alloc_obj ι a1 a2 ∗ ι ↦st{q} s)
              (λ R _, ∃ γ, R !! ι = Some (a1, a2, γ, s))
              with "[$HPC $Hpc_a $Hobj $Htok $Hmap]");
      [done | rewrite /regs_instr_ok; by apply sw_of_none | done
      | by eapply subseg_rebase_source | exact Hagree
      | right; rewrite /regs; set_solver+ | |].
    { iIntros (R C) "HR _ [#Hobj' Htok']".
      iDestruct (reg_lookup_obj with "HR Hobj'") as %(γ & s' & HRι).
      iDestruct (reg_lookup_own with "HR Htok'") as %(b' & e' & γ' & HRι').
      rewrite HRι in HRι'. simplify_eq. iPureIntro. by eexists. }
    iIntros "!>" (lpc' regs' retv) "(%Hout & HPC & Hpc_a & [_ Htok] & Hmap)".
    rewrite /regs_outcome (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a') in Hout.
    destruct Hout as (-> & -> & v & -> & ->).
    rewrite linsert_reg_not_cnull //. subst regs.
    iRegsMap "Hmap"; eauto. iApply "HΦ". iFrame "∗ #".
  Qed.
End subseg_witness_rules.
