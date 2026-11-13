From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import ftlr_base ftlr_contract capability_monotonicity interp_weakening
  shapes.step.
Import CoreWPNotations.
#[local] Open Scope capability_scope.

(** * The fundamental theorem by shapes of instructions

    A case of the fundamental theorem is proved once per shape of
    instruction. Each instruction then only needs a pure membership: a
    property of a step function, here [exec_opt]. This file holds the
    helpers shared by the shapes, then the stop and register-step shapes,
    each with its membership, its membership tactic and its case. The
    memory shape is in [ftlr_mem_access.v], the classification of the
    instructions in [ftlr_dispatch.v], and the instructions with a
    dedicated proof in [Jalr.v] and [Ecall.v]. *)

(** ** Shared helpers *)

Section shapes_pure.
  Context `{MP : MachineParameters}.

  (** The memberships are stated for a step function [step], as in
      [rules_mem_access.v]: the cases of the fundamental theorem take
      [exec_opt]; another semantics reuses the definitions and tactics with
      its own. [exec_with step] is the total step, a failure being a fault, as
      [exec] is of [exec_opt]. *)
  Definition exec_with (step : instr → Perm → ExecConf → option Conf)
      (i : instr) (p : Perm) (φ : ExecConf) : Conf :=
    match step i p φ with None => (Faulted, φ) | Some conf => conf end.

  Lemma exec_with_exec_opt i p φ : exec_with exec_opt i p φ = exec i p φ.
  Proof. done. Qed.

  (** Not a switch instruction, at every kind. *)
  Definition not_switch_instr (i : instr) : Prop := ∀ k, sw_of k i = None.

End shapes_pure.

(** Debugging: with a [debug_shapes] hypothesis in the context, the
    membership tactics print why they reject an instruction (see
    [debug_classify] in [ftlr_dispatch.v]). Without it they fail
    silently, with the same message. *)
Inductive debug_shapes := DebugShapes.

Ltac reject_shape msg :=
  lazymatch goal with
  | _ : debug_shapes |- _ => idtac "    rejected:" msg
  | _ => idtac
  end;
  fail 0 msg.

(** Closes [not_switch_instr i]: [sw_of k i] computes to [None] at every kind. *)
Ltac solve_not_switch_instr := intros ?; first [by apply sw_of_none | reject_shape "a switch instruction"].

(** [SI_close] takes the erasure only. *)
#[local] Arguments SI_close {MP Σ pcG0 gen_heapGS0 gen_heapGS1 gen_heapGS2 gen_heapGS3
  allocRegistryG0 addrAllocG0 H mtdcG0 mieG0 mpieG0 postureG0 mtdcLentG0 σ lpc lreg ls lmem R C}.

Section shapes_shared.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).

  (** A safe PC has no system-register access. *)
  Lemma interp_pc_no_sreg_access W C p g b e a :
    executeAllowed p = true →
    interp W C (Cap p g b e a) -∗ ⌜has_sreg_access p = false⌝.
  Proof.
    iIntros (Hexec) "Hinterp".
    destruct (has_sreg_access p) eqn:Hsr; last done.
    iEval (rewrite interp_unfold interp1_eq) in "Hinterp".
    rewrite (executeAllowed_nonO _ Hexec) Hsr. done.
  Qed.

  (** An identifier-less capability in [interp] is off the heap. *)
  Lemma interp_no_prov_disjoint_from_heap W C v : interp W C v -∗ ⌜no_prov_disjoint_from_heap v⌝.
  Proof.
    iIntros "#Hv" (p g b e a x -> Hb He).
    iDestruct (interp_cap_heap_conditions with "Hv") as "[Hvalid _]".
    iDestruct ("Hvalid" with "[%]") as %Hdisj; first solve_addr.
    iPureIntro. eapply disjoint_from_heap_not_in; first done.
    apply withinBounds_true_iff. solve_addr.
  Qed.

  (** A word below a safe word is safe: [interp] is monotone in [lword_le]
      (the induction hypothesis for the executable capabilities). *)
  Lemma lword_le_sound W C v' v :
    v' ⊑ₗ v →
    ftlr_IH -∗
    thread_in th C -∗
    interp W C v -∗
    interp W C v'.
  Proof.
    iIntros (Hle) "#IH #Hthread #Hv".
    destruct Hle as [v' v Ht | v | t t' p p' g g' b b' e e' a a' π Ht Hp Hg Hb He Hheap
                    | t t' p p' g g' b b' e e' a a' π Ht Hp Hg Hb He].
    - by iApply interp_untagged.
    - done.
    - destruct t'; last by iApply interp_untagged.
      rewrite (Ht eq_refl).
      by iApply (interp_weakening with "IH Hthread Hv").
    - destruct t'; last by iApply interp_untagged.
      rewrite (Ht eq_refl).
      by iApply (interp_weakening_ot with "Hv").
  Qed.

  (** Unsealing reads a seal predicate, hence the later and the open world. *)
  Lemma lderivable_sound W C s (lregs : LReg) (lpc v : LWord) :
    lderivable lregs lpc v →
    ftlr_IH -∗
    thread_in th C -∗
    interp W C lpc -∗
    (∀ (r : RegName) v, ⌜lregs !! r = Some v⌝ → interp W C v) -∗
    world_interp_open W C s -∗
    ▷ (interp W C v ∗ world_interp_open W C s).
  Proof.
    iIntros (Hder) "#IH #Hthread #Hpc #Hreg Hworld".
    destruct Hder as [r v0 v Hr Hle | v Hle
                     | r1 r2 p g b e a πr sb π Hr1 Hr2 Hps Hwb
                     | r1 r2 p g b e a πr o sb π Hr1 Hr2 Hps Hwb].
    - iFrame "Hworld". iApply (lword_le_sound with "IH Hthread"); first exact Hle.
      by iApply "Hreg".
    - iFrame "Hworld". by iApply (lword_le_sound with "IH Hthread Hpc").
    - iFrame "Hworld".
      iApply (sealing_preserves_interp with "Hthread [] []"); [done | done | |].
      + by iApply "Hreg".
      + by iApply "Hreg".
    - iApply (unsealing_preserves_interp with "Hthread [] [] Hworld"); [done | done | |].
      + by iApply "Hreg".
      + by iApply "Hreg".
  Qed.

  (** In the fundamental theorem, the owned registers are all the logical
      registers. *)
  Lemma full_regs_incl_eq (regs lreg : LReg) :
    (∀ x, is_Some (regs !! x)) → regs ⊆ lreg → lreg = regs.
  Proof.
    intros Hsome Hincl. apply map_eq. intros x.
    destruct (Hsome x) as [v Hv]. rewrite Hv. by eapply lookup_weaken.
  Qed.

  (** The post-state after a fault. *)
  Lemma ftlr_contract_intro_post_fault W C regs pc :
    (∀ r, is_Some (regs !! r)) →
    PC ↦ₚ[th] pc -∗
    regs[th] regs -∗
    ▷ ((∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) ∗ world_interp W C) -∗
    ftlr_contract_intro_post W C FaultedV.
  Proof.
    iIntros (Hfull) "HPC Hmap Hpost !>". iDestruct "Hpost" as "[Hreg Hworld]".
    iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld"); done.
  Qed.

  (** The post-state after a step that moves a safe PC by [n]. *)
  Lemma ftlr_contract_intro_post_next W C regs p g b e a n lpc' :
    (∀ r, is_Some (regs !! r)) →
    isCorrectPC (Cap p g b e a) → incrementPC_gen (Cap p g b e a) n = Some lpc' →
    ftlr_IH -∗
    interp W C (Cap p g b e a) -∗
    PC ↦ₚ[th] lpc' -∗
    regs[th] regs -∗
    ▷ ((∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) ∗ world_interp W C) -∗
    ftlr_contract_intro_post W C NextIV.
  Proof.
    iIntros (Hfull Hcorrect Hinc) "#IH #Hpc HPC Hmap Hpost".
    apply incrementPC_gen_Some_inv in Hinc
      as (t'' & p'' & g'' & b'' & e'' & a'' & a_next & π'' & Hpc & Ha_next & ->).
    injection Hpc as <- <- <- <- <- <- <-.
    iNext. iDestruct "Hpost" as "[Hreg Hworld]".
    iApply (ftlr_post_next with "HPC Hmap Hreg [] Hworld"); first done.
    iApply "IH". by iApply (interp_next_PC with "Hpc").
  Qed.

  (** The closing of the PC's region, at the fraction [dq] of the PC's
      cell, for any word left in it. *)
  Definition pc_cell_close W C (a : Addr) (dq : dfrac) (P : D) (ρ : region_part) : iProp Σ :=
    ∀ w',
      world_interp_open W C [LNonHeap a] -∗
      a ↦ₐ{dq} w' -∗
      pc_content ρ W C P w' -∗
      world_interp W C.

  (** The PC's cell, with its content and the closing of the PC's region,
      for a step that may write the cell: the memory accesses. *)
  Lemma pc_cell_open W C a p' P w ρ :
    persistent_cond P →
    region_rel_part ρ W C (LNonHeap a) p' P -∗
    ▷ pc_open W C (LNonHeap a) p' P w ρ -∗
    ▷ (a ↦ₐ w ∗
       pc_content ρ W C P w ∗
       pc_cell_close W C a (DfracOwn 1) P ρ).
  Proof.
    iIntros (Hpers) "#Hinva WorldRes !>".
    iDestruct (pc_open_acc_forall with "Hinva WorldRes") as "[ [$ $] Hreopen]".
    iIntros (w') "Hworld_interp Ha Hcontent".
    iApply (pc_close with "Hworld_interp Hinva (Hreopen [$Ha $Hcontent])"); first done.
  Qed.

  (** The PC's cell at a fraction [dq], with the closing of the PC's region
      at the same word, for a step that only fetches the instruction. *)
  Lemma pc_cell_fetch W C a p' P w ρ :
    persistent_cond P →
    region_rel_part ρ W C (LNonHeap a) p' P -∗
    ▷ pc_open W C (LNonHeap a) p' P w ρ -∗
    ∃ dq,
      ▷ (a ↦ₐ{dq} w ∗
         (world_interp_open W C [LNonHeap a] -∗ a ↦ₐ{dq} w -∗ world_interp W C)).
  Proof.
    iIntros (Hpers) "#Hinva WorldRes".
    iDestruct (pc_cell_open with "Hinva WorldRes") as "Hcell"; first done.
    iExists (DfracOwn 1). iNext. iDestruct "Hcell" as "($ & Hcontent & Hclose)".
    iIntros "Hworld_interp Ha". iApply ("Hclose" with "Hworld_interp Ha Hcontent").
  Qed.

  (** The step of a case whose instruction is not a switch instruction: the
      PC's cell is lent to the step and given back, and a failed step is
      closed. The continuation gets a successful step, the world open at
      the PC and the closing of the PC's region. *)
  Lemma ftlr_case_step_not_switch_instr W C (regs : LReg) p p' g b e a w i ρ P :
    not_switch_instr i → decodeInstrW w.(lw) = i → isCorrectPC (Cap p g b e a) → persistent_cond P →
    (∀ x : RegName, is_Some (regs !! x)) →
    (∀ (r : RegName) v, ⌜regs !! r = Some v⌝ → interp W C v) -∗
    region_rel_part ρ W C (LNonHeap a) p' P -∗
    ▷ pc_open W C (LNonHeap a) p' P w ρ -∗
    world_interp_open W C [LNonHeap a] -∗
    PC ↦ₚ[th] (Cap p g b e a) -∗
    regs[th] regs -∗
    ▷ (∀ r sr m st td lsreg lmem R claims c σ',
         ⌜erasure R claims (MkExecConf (Cap p g b e a) r sr m st td) (Cap p g b e a) regs
            (ls_join lsreg) lmem⌝ -∗
         ⌜exec_opt i p (MkExecConf (Cap p g b e a) r sr m st td) = Some (c, σ')⌝ -∗
         PC_auth (Cap p g b e a) -∗
         gen_heap_interp regs -∗
         sys_interp lsreg -∗
         gen_heap_interp lmem -∗
         gen_heap_interp st -∗
         reg_auth R -∗
         addr_alloc_auth claims -∗
         PC ↦ₚ[th] (Cap p g b e a) -∗
         regs[th] regs -∗
         world_interp_open W C [LNonHeap a] -∗
         (world_interp_open W C [LNonHeap a] -∗ world_interp W C)
         ==∗
         ⌜sys_kept (MkExecConf (Cap p g b e a) r sr m st td) σ'⌝ ∗
         cerise_state_interp σ' ∗
         from_option (ftlr_contract_intro_post W C) False (flag_val c)) -∗
    WP Instr Executable @core[th] {{ ftlr_contract_intro_post W C }}.
  Proof.
    iIntros (Hsw Hi HcorrectPC Hpers Hsome) "#Hreg #Hinva WorldRes Hworld_interp HPC Hmap Hcont".
    iDestruct (pc_cell_fetch with "Hinva WorldRes") as (dq) "[Ha Hpc_close]"; first done.
    iApply (wp_instr_step_nosw (CL := link_core) with "HPC Ha Hmap"); [by rewrite Hi | done |].
    iNext. iIntros (r sr m st td lreg lsreg lmem R claims c σ') "@".
    pose proof (full_regs_incl_eq regs lreg Hsome Hlregs) as ->.
    rewrite Hi /exec in Hstep.
    destruct (exec_opt i p _) as [conf|] eqn:Hexec; cycle 1.
    { simplify_eq.
      iDestruct ("Hpc_close" with "Hworld_interp Hpc_a") as "Hworld_interp".
      iApply (instr_close_fail with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap"); first done.
      iIntros "HPC Hmap".
      iApply (ftlr_contract_intro_post_fault with "HPC Hmap [$Hreg $Hworld_interp]"); done. }
    subst conf.
    iApply ("Hcont" with "[//] [//] HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hworld_interp").
    iIntros "Hworld_interp". iApply ("Hpc_close" with "Hworld_interp Hpc_a").
  Qed.

End shapes_shared.

(** ** Stop

    A stop instruction faults or halts: it changes nothing but the
    outcome. *)

Section stop_pure.
  Context `{MP : MachineParameters}.

  (** Stop: the instruction faults or halts, for a PC without system-register
      access. Stated on the total step: [Fail] and [Halt] step to
      [Some (Faulted, φ)] or [Some (Halted, φ)], and the system-register
      instructions fail for such a PC. *)
  Definition stop_member (step : instr → Perm → ExecConf → option Conf) (i : instr) : Prop :=
    ∀ p φ, executeAllowed p = true → has_sreg_access p = false →
      exec_with step i p φ = (Faulted, φ) ∨ exec_with step i p φ = (Halted, φ).

End stop_pure.

(** Closes [stop_member step i]: the total step faults or halts, once a
    system-register test is rewritten by [has_sreg_access p = false]. *)
Ltac solve_stop_member :=
  let Hsr := fresh "Hsr" in
  intros ? ? _ Hsr; rewrite /exec_with /= ?Hsr;
  first [by left | by right | reject_shape "a step may neither fault nor halt"].

Section stop.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).

  (** Stop: through [wp_instr_step], since [Mret] and the exit marker are
      switch instructions. *)
  Lemma stop_case (m : InterruptStatus) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (i : instr) (ρ : region_part) (P : D) :
    stop_member exec_opt i →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hstop. apply ftlr_contract_intro. clear m.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".
    iDestruct (interp_pc_no_sreg_access with "Hinv_interp") as %Hnsr; first apply Hp.
    iDestruct (pc_cell_fetch with "Hinva WorldRes") as (dq) "[Ha Hpc_close]"; first done.
    iApply (wp_instr_step (CL := link_core) with "HPC Ha Hmap"); first done.
    iNext. iIntros (r sr m st td lreg lsreg lmem R claims c σ') "@".
    iDestruct ("Hpc_close" with "Hworld_interp Hpc_a") as "Hworld_interp".
    iModIntro.
    rewrite Hi -exec_with_exec_opt in Hstep.
    destruct (Hstop p (MkExecConf (Cap p g b e a) r sr m st td) (proj1 Hp) Hnsr) as [Hex | Hex];
      rewrite Hex in Hstep; simplify_eq.
    - iSplit; first (iPureIntro; apply sys_kept_refl).
      iSplitR "HPC Hmap Hworld_interp".
      { iApply (SI_close Her with "HPCa Hr Hsr Hm Hst HR HC"). }
      iNext. iApply (ftlr_post_fault with "HPC Hmap Hreg Hworld_interp"); done.
    - iSplit; first (iPureIntro; apply sys_kept_refl).
      iSplitR "Hworld_interp".
      { iApply (SI_close Her with "HPCa Hr Hsr Hm Hst HR HC"). }
      iNext. iApply (ftlr_post_halt with "Hworld_interp").
  Qed.

End stop.

(** ** Register step

    A register step writes at most one derivable word to a register and
    moves the PC: the written word has no more authority than the
    pre-state's registers and PC ([capability_monotonicity.v]). *)

Section regs_pure.
  Context `{MP : MachineParameters}.

  (** Register step: a register step writes at most one derivable word to
      a register and moves the PC by an offset. A register update moves it
      by [1] ([nextPC]); a jump writes no register, as a write to [cnull]
      ([update_reg_cnull]). *)
  Definition regs_member (step : instr → Perm → ExecConf → option Conf) (i : instr) : Prop :=
    ∀ p φ c, step i p φ = Some c →
      ∃ (dst : RegName) (w : Word) (n : Z),
        derivable φ w ∧ advancePC ((regs_effect φ) .[dst :=ᵣ w]) n = Some c.

End regs_pure.

Create HintDb flows_refl.
#[export] Hint Resolve PermFlowsToReflexive LocalityFlowsToReflexive
  SealPermFlowsToReflexive : flows_refl.

(** Closes [w' ⊑ w]: the same word, an untagged [w'], or a narrowing
    of a capability or a sealing range, one premise of [wle_cap] or
    [wle_sr] at a time. *)
Ltac solve_word_le :=
  first [ apply wle_refl
        | apply wle_untagged; done
        | apply wle_cap;
          [ first [by eauto | reject_shape "a tagged result from an untagged source"]
          | first [by eauto with flows_refl | reject_shape "the permission grows"]
          | first [by eauto with flows_refl | reject_shape "the locality grows"]
          | first [solve_addr | reject_shape "the base moves down"]
          | first [solve_addr | reject_shape "the end moves up"]
          | rewrite /rebased_bounds_ok;
            first [by left | right; solve_addr | reject_shape "the base is above the end"] ]
        | apply wle_sr;
          [ first [by eauto | reject_shape "a tagged result from an untagged source"]
          | first [by eauto with flows_refl | reject_shape "the permission grows"]
          | first [by eauto with flows_refl | reject_shape "the locality grows"]
          | first [solve_addr | reject_shape "the base moves down"]
          | first [solve_addr | reject_shape "the end moves up"] ] ].

(** Closes [derivable φ w]: untagged, or [word_le] of a register read or of
    the PC, or a sealing or unsealing. A result whose tag is computed by a
    test, [t && c], is untagged when the test fails; otherwise the facts the
    test checked are hypotheses (Subseg's [isWithin] and [<=?]). The
    register read is searched among all lookups (Store has two). *)
Ltac solve_derivable :=
  let Htag := fresh "Htag" in
  try match goal with
    | |- derivable _ (WCap (?t && ?c) _ _ _ _ _) => destruct (t && c) eqn:Htag
    | |- derivable _ (WSealRange (?t && ?c) _ _ _ _ _) => destruct (t && c) eqn:Htag
    end;
  repeat match goal with
    | H : _ && _ = true |- _ => apply andb_true_iff in H as [? ?]
    | H : isWithin _ _ _ _ = true |- _ => apply isWithin_implies in H
    | H : (_ <=? _)%a = true |- _ => apply Z.leb_le in H
    end;
  first
    [ apply derivable_untagged; by rewrite /= ?get_tag_clear_tag ?get_tag_clear_tag_sealable
    | match goal with
      | H : reg _ !!ᵣ _ = Some _ |- _ => eapply derivable_reg; [exact H | solve_word_le]
      end
    | eapply derivable_seal; eassumption
    | eapply derivable_unseal; eassumption
    | apply derivable_pc; match goal with H : pcc _ = _ |- _ => rewrite H end; solve_word_le
    | reject_shape "the written word is not derivable from a register or the PC" ].

(** Early-fail checks on the unfolded step [H : exec_opt … = Some c], before
    the case split, so that a failing shape try costs little. A register
    step only writes a register and moves the PC: it fails if the step
    touches more than the registers (a system-register or memory write, a
    memory read, or a configuration built by hand rather than by
    [advancePC]). The checks only prune: the proofs do not depend on them. *)
Ltac fail_if_not_regs_step H :=
  lazymatch type of H with
  | context [update_sreg _ _ _] => reject_shape "writes a system register"
  | context [update_mem _ _ _] => reject_shape "writes the memory"
  | context [mem _ !! _] => reject_shape "reads the memory"
  | context [Some (_, _)] => reject_shape "builds the configuration (not by advancePC)"
  | _ => idtac
  end.

(** Each successful branch ends in a PC move: after a register write, by
    [nextPC] (offset [1]); without one, a jump, by [nextPC] or [advancePC]
    (a write of [WInt 0] to [cnull]). *)
Ltac solve_regs_member :=
  let Hex := fresh "Hex" in
  intros ? ? ? Hex; rewrite /regs_effect; cbn in Hex;
  rewrite ?/word_of_argument ?/exec_jcond in Hex;
  fail_if_not_regs_step Hex;
  repeat (simplify_option_eq; try case_match);
  lazymatch goal with
  | H : nextPC (update_reg _ _ _) = Some _ |- _ =>
      do 2 eexists; exists 1%Z; split; [| exact H]; solve_derivable
  | H : nextPC _ = Some _ |- _ =>
      exists cnull, (WInt 0), 1%Z; rewrite update_reg_cnull;
      split; [by apply derivable_untagged | exact H]
  | H : advancePC _ _ = Some _ |- _ =>
      exists cnull, (WInt 0); eexists; rewrite update_reg_cnull;
      split; [by apply derivable_untagged | exact H]
  | _ => reject_shape "a successful step is not one register write and a PC move"
  end.

(** The closing lemma of the register-step case, with its spec as an argument by
    name. *)
#[local] Arguments instr_close_reg_update_advancePC {MP Σ ceriseg k pc r sr m st td lpc lreg lsreg lmem
  R C regs dst v w n c σ' Φ} P.

Section regs.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {cthreads : CmptThreads} {CL : ∀ t, CritLink Σ t}
    `{MP: MachineParameters}
    {CR : ∀ t, CritRoute Σ t (CL t)}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  #[local] Notation D := (interpO Σ).

  (** Register step: the written word is derivable, so it lifts to a derivable
      logical word, which is safe. *)
  Lemma regs_case (m : InterruptStatus) (W : WORLD) (C : CmptName) (regs : leibnizO LReg)
    (p p' : Perm) (g : Locality) (b e a : Addr) (w : LWord)
    (i : instr) (ρ : region_part) (P : D) :
    regs_member exec_opt i →
    not_switch_instr i →
    ftlr_contract m W C regs p p' g b e a w i ρ P.
  Proof.
    intros Hmember Hsw. apply ftlr_contract_intro. clear m.
    intros Hp Hsome HcorrectPC Hbae Hfp Hpers Hi.
    iIntros "@".
    iAssert (⌜∀ r v, regs !! r = Some v → no_prov_disjoint_from_heap v⌝)%I as %Hnoid.
    { iIntros (r v Hv). iApply interp_no_prov_disjoint_from_heap. by iApply "Hreg". }
    iApply (ftlr_case_step_not_switch_instr with "Hreg Hinva WorldRes Hworld_interp HPC Hmap"); [done..|].
    iIntros "!>" (r sr m st td lsreg lmem R claims c σ' Her Hexec)
      "HPCa Hr Hsr Hm Hst HR HC HPC Hmap Hworld_interp Hclose_pc".
    destruct (Hmember _ _ _ Hexec) as (dst & w' & n & Hder & Hadv).
    rewrite /regs_effect in Hadv.
    destruct (derivable_lift Her Hnoid w' Hder) as (v & Hok & Hphys & Hlder).
    (* The world stays open until the later of the post-state. *)
    iDestruct (lderivable_sound with "IH Hthread Hinv_interp Hreg Hworld_interp")
      as "Hv_world"; first done.
    iApply (instr_close_reg_update_advancePC (dst := dst) (v := v) (w := w') (n := n)
      (λ lpc' regs' retv,
         (retv = NextIV ∧ incrementPC_gen (Cap p g b e a) n = Some lpc' ∧
            regs' = <[dst := v]ₗ> regs) ∨
         (retv = FaultedV ∧ lpc' = Cap p g b e a ∧ regs' = regs))
      Her with "HPCa Hr Hsr Hm Hst HR HC HPC Hmap [-]").
    { right. apply elem_of_dom, Hsome. }
    { exact Hok. }
    { by rewrite Hadv. }
    { exact Hphys. }
    { intros lpc' Hinc. by left. }
    { intros Hinc. by right. }
    iIntros (lpc' regs' retv [ (-> & Hinc & ->) | (-> & -> & ->) ]) "HPC Hmap".
    - iApply (ftlr_contract_intro_post_next with "IH Hinv_interp HPC Hmap [Hv_world Hclose_pc]");
        [by apply full_map_linsert | done | exact Hinc |].
      iNext. iDestruct "Hv_world" as "[#Hv Hworld_interp]". iSplit.
      + iApply (interp_linsert with "Hreg"). by iIntros (_).
      + by iApply "Hclose_pc".
    - iApply (ftlr_contract_intro_post_fault with "HPC Hmap [Hv_world Hclose_pc]"); first done.
      iNext. iDestruct "Hv_world" as "[_ Hworld_interp]". iFrame "Hreg".
      by iApply "Hclose_pc".
  Qed.

End regs.
