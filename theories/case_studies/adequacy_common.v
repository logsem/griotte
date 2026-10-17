From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import logrel monotone interp_weakening.
From griotte Require Import switcher assert_spec.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import stack_world_resources.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers.
From griotte Require Import allocator_resources heap_region.

(** * Shared building blocks for the case-study adequacy proofs.

    The lemmas below compose: each adequacy proof calls them in turn
    (Iris adequacy wrapper, world initialisation, compartment
    initialisation, adversary world, register split, size obligations),
    and can insert its own initialisation steps in between. *)

(** ** Concrete capabilities of the initial configuration *)
Section initial_capabilities.
  Context `{MP: MachineParameters}.

  (** Initial PC of a compartment: its PCC, pointing to the start of the code. *)
  Definition cmpt_entry_pc (C_cmpt : cmpt) : Word :=
    WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_a_code C_cmpt).

  (** PCC and CGP of a compartment, as stored in its export table. *)
  Definition cmpt_pcc_cap (C_cmpt : cmpt) : Word :=
    WCap true RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt).
  Definition cmpt_cgp_cap (C_cmpt : cmpt) : Word :=
    WCap true RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt).

  (** Stack and trusted-stack capabilities of the switcher. *)
  Definition stack_cap (sw : cmptSwitcher) : Word :=
    WCap true RWL Local (b_stack sw) (e_stack sw) (b_stack sw).
  Definition trusted_stack_cap (sw : cmptSwitcher) : Word :=
    WCap true RWL Local (b_trusted_stack sw) (e_trusted_stack sw) (b_trusted_stack sw).

  (** The (unsealed) export-table capability for the entry at address [a]. *)
  Definition cmpt_export (C_cmpt : cmpt) (a : Addr) : Sealable :=
    SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a.

  Definition stack_addrs (sw : cmptSwitcher) : list Addr :=
    finz.seq_between (b_stack sw) (e_stack sw).

  (** The addresses of the entries of the export table of a compartment. *)
  Definition cmpt_exp_tbl_addrs (C_cmpt : cmpt) : list Addr :=
    finz.seq_between (cmpt_exp_tbl_entries_start C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt).

  Lemma cmpt_exp_tbl_addrs_lookup (C_cmpt : cmpt) (i : nat) (a : Addr) :
    cmpt_exp_tbl_addrs C_cmpt !! i = Some a →
    a = (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a ∧ i < length (cmpt_exp_tbl_entries C_cmpt).
  Proof.
    intros Ha.
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi.
    { apply lookup_lt_Some in Ha.
      rewrite /cmpt_exp_tbl_addrs finz_seq_between_length /finz.dist in Ha.
      solve_addr. }
    rewrite /cmpt_exp_tbl_addrs (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt)))
      in Ha; [|done|done].
    by simplify_eq.
  Qed.

  Lemma cmpt_exp_tbl_addrs_elem_of (C_cmpt : cmpt) (i : nat) :
    i < length (cmpt_exp_tbl_entries C_cmpt) →
    (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a ∈ cmpt_exp_tbl_addrs C_cmpt.
  Proof.
    intros Hi.
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    apply list_elem_of_lookup_2 with i.
    by rewrite /cmpt_exp_tbl_addrs (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt))).
  Qed.

End initial_capabilities.

(** ** Initial register files *)
Definition is_initial_registers_of `{MP: MachineParameters}
  (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :=
  pc = cmpt_entry_pc main ∧
  reg !! cgp = Some (cmpt_cgp_cap main) ∧
  reg !! csp = Some (stack_cap sw) ∧
  (∀ (r : RegName), r ∉ ({[ cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

(** The initial system registers: MTDC holds the trusted stack, mstatus has
    interrupts disabled, and the others hold zero (MTCC is untagged). *)
Definition initial_sreg `{MP: MachineParameters} (sw : cmptSwitcher) (sr : SRegName) : Word :=
  match sr with
  | MTDC => trusted_stack_cap sw
  | MSTATUS => WInt (mstatus_enc InterruptDisabled InterruptDisabled)
  | MTCC | MEPCC | MCAUSE | MTVAL => WInt 0
  end.

Definition is_initial_sregisters_of `{MP: MachineParameters}
  (sw : cmptSwitcher) (sreg : SReg) :=
  ∀ sr, sreg !! sr = Some (initial_sreg sw sr).

(** A concrete initial system-register file, with [w] in MTDC. *)
Definition initial_sregisters_with (w : Word) : SReg :=
  <[MTCC := WInt 0]> (<[MTDC := w]> (<[MEPCC := WInt 0]>
    (<[MSTATUS := WInt (mstatus_enc InterruptDisabled InterruptDisabled)]>
    (<[MCAUSE := WInt 0]> (<[MTVAL := WInt 0]> ∅))))).

Lemma initial_sregisters_with_correct `{MP: MachineParameters} (sw : cmptSwitcher) w :
  w = trusted_stack_cap sw → is_initial_sregisters_of sw (initial_sregisters_with w).
Proof. intros -> sr. by destruct sr; rewrite /initial_sregisters_with; simplify_map_eq. Qed.

Section registers.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP: MachineParameters}.

  Lemma initial_registers_split (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    PC ↦ₚ lword_of_word pc ∗
    ([∗ map] r↦w ∈ lword_of_word <$> reg, r ↦ᵣ w) ⊢
    ∃ (rmap : LReg),
      PC ↦ₚ cmpt_entry_pc main ∗
      cgp ↦ᵣ cmpt_cgp_cap main ∗
      csp ↦ᵣ stack_cap sw ∗
      ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
      ⌜dom rmap = all_registers_s ∖ {[ cgp; csp ]}⌝ ∗
      ⌜∀ r, r ∈ dom rmap → rmap !! r = Some (lword_of_word (WInt 0))⌝.
  Proof.
    intros (-> & Hcgp & Hcsp & Hzero).
    iIntros "[HPC Hreg]".
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]";
      first by rewrite lookup_fmap Hcgp.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]";
      first by rewrite !lookup_delete_ne // lookup_fmap Hcsp.
    iExists _; iFrame.
    iPureIntro; split.
    - rewrite !dom_delete_L lregmap_full_dom; first done.
      intros r.
      destruct (decide (r ∈ ({[ cgp; csp ]} : gset RegName))) as [Hr|Hr].
      + rewrite !elem_of_union !elem_of_singleton in Hr.
        destruct Hr as [ -> | -> ]; rewrite lookup_fmap ?Hcgp ?Hcsp; eauto.
      + rewrite lookup_fmap Hzero //.
    - intros r Hr.
      rewrite !dom_delete_L !elem_of_difference !elem_of_singleton in Hr.
      destruct Hr as [ [_ Hrcgp] Hrcsp].
      rewrite !lookup_delete_ne // lookup_fmap Hzero //; set_solver.
  Qed.

End registers.

(** ** Rootedness of the initial configuration

    The lemmas below discharge the [ghost_init_cond] side condition of
    [cerise_flag_adequacy] for a layout made of the switcher, the assert
    compartment and a list of compartments, with a set [R] of heap roots
    held by the compartments (an allocator holds the root of the heap;
    without an allocator, [R] is empty). Each case study only proves that
    the memory of its compartments is rooted in [R]. *)
Section initial_rootedness.
  Context `{MP: MachineParameters}.

  (** The program memory of a layout: the switcher, the assert compartment,
      then the compartments, in this order. *)
  Definition initial_program_memory
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) : Mem :=
    foldl (λ m C, m ∪ mk_initial_cmpt C)
      (mk_initial_switcher sw ∪ mk_initial_assert Cassert) cmpts.

  Lemma dom_foldl_initial_cmpt (m : Mem) (cmpts : list cmpt) :
    dom m ⊆ dom (foldl (λ m C, m ∪ mk_initial_cmpt C) m cmpts).
  Proof.
    revert m; induction cmpts as [|C cmpts IH]; intros m; cbn; first done.
    etrans; last apply IH. rewrite dom_union_L. set_solver.
  Qed.

  Lemma mem_rooted_foldl_initial_cmpt (H : gset Addr) (m : Mem) (cmpts : list cmpt) :
    mem_rooted H m →
    Forall (λ C, mem_rooted H (mk_initial_cmpt C)) cmpts →
    mem_rooted H (foldl (λ m C, m ∪ mk_initial_cmpt C) m cmpts).
  Proof.
    revert m; induction cmpts as [|C cmpts IH]; intros m Hm Hcmpts; cbn; first done.
    apply Forall_cons in Hcmpts as [HC Hcmpts].
    apply IH; last done. by apply mem_rooted_union.
  Qed.

  Lemma mem_exec_ok_foldl_initial_cmpt (m : Mem) (cmpts : list cmpt) :
    mem_exec_ok m →
    Forall (λ C, mem_exec_ok (mk_initial_cmpt C)) cmpts →
    mem_exec_ok (foldl (λ m C, m ∪ mk_initial_cmpt C) m cmpts).
  Proof.
    revert m; induction cmpts as [|C cmpts IH]; intros m Hm Hcmpts; cbn; first done.
    apply Forall_cons in Hcmpts as [HC Hcmpts].
    apply IH; last done. by apply mem_exec_ok_union.
  Qed.

  Lemma mem_avoids_mmio_foldl_initial_cmpt (m : Mem) (cmpts : list cmpt) :
    mem_avoids_mmio m →
    mem_avoids_mmio (foldl (λ m C, m ∪ mk_initial_cmpt C) m cmpts).
  Proof.
    revert m; induction cmpts as [|C cmpts IH]; intros m Hm; cbn; first done.
    apply IH, mem_avoids_mmio_union; [done|apply mem_avoids_mmio_initial_cmpt].
  Qed.

  Lemma dom_initial_program_memory_switcher_assert
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) :
    dom (mk_initial_switcher sw) ∪ dom (mk_initial_assert Cassert)
      ⊆ dom (initial_program_memory sw Cassert cmpts).
  Proof.
    rewrite -dom_union_L. apply dom_foldl_initial_cmpt.
  Qed.

  (** The initial memory is rooted in [R], provided that each compartment is. *)
  Lemma mem_rooted_initial_memory_roots (R : gset Addr)
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) :
    initial_heap_memory ##ₘ initial_program_memory sw Cassert cmpts →
    Forall is_z (stack_content sw) →
    Forall (λ C, mem_rooted R (mk_initial_cmpt C)) cmpts →
    mem_rooted R (initial_heap_memory ∪ initial_program_memory sw Cassert cmpts).
  Proof.
    intros Hheap Hstack Hcmpts.
    pose proof (dom_initial_program_memory_switcher_assert sw Cassert cmpts) as Hdom.
    apply mem_rooted_union; first apply mem_rooted_initial_heap.
    apply mem_rooted_foldl_initial_cmpt; last done.
    apply mem_rooted_union.
    - apply mem_rooted_initial_switcher. by apply word_rooted_ints.
    - (* The assert flag is in the program memory, hence outside the heap. *)
      apply mem_rooted_initial_assert.
      apply (assert_flag_not_heap_of_disjoint_dom _ _ Hheap). set_solver.
  Qed.

  (** The executable words of the initial memory avoid the heap, provided
      that those of each compartment do. *)
  Lemma mem_exec_ok_initial_memory
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) :
    Forall is_z (stack_content sw) →
    Forall (λ C, mem_exec_ok (mk_initial_cmpt C)) cmpts →
    mem_exec_ok (initial_heap_memory ∪ initial_program_memory sw Cassert cmpts).
  Proof.
    intros Hstack Hcmpts.
    apply mem_exec_ok_union; first apply mem_exec_ok_initial_heap.
    apply mem_exec_ok_foldl_initial_cmpt; last done.
    apply mem_exec_ok_union.
    - apply mem_exec_ok_initial_switcher. by apply word_exec_ok_ints.
    - apply mem_exec_ok_initial_assert.
  Qed.

  (** The compartments' executable words avoid the heap, provided that each
      compartment's words are non-executable or switcher or assert sentries. *)
  Lemma mem_exec_ok_initial_cmpts
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) :
    initial_heap_memory ##ₘ initial_program_memory sw Cassert cmpts →
    Forall (λ C, Forall (initial_exec_word sw Cassert) (cmpt_words C)) cmpts →
    Forall (λ C, mem_exec_ok (mk_initial_cmpt C)) cmpts.
  Proof.
    intros Hheap Hcmpts.
    pose proof (dom_initial_program_memory_switcher_assert sw Cassert cmpts) as Hdom.
    pose proof (assert_disjoint_from_heap_of_disjoint_dom Cassert _ Hheap
      ltac:(set_solver)) as Hassert.
    eapply Forall_impl; first exact Hcmpts.
    intros C. by apply mem_exec_ok_initial_cmpt_words.
  Qed.

  Lemma mem_rooted_initial_memory
    (sw : cmptSwitcher) (Cassert : cmptAssert) (cmpts : list cmpt) :
    initial_heap_memory ##ₘ initial_program_memory sw Cassert cmpts →
    Forall is_z (stack_content sw) →
    Forall (λ C, mem_rooted ∅ (mk_initial_cmpt C)) cmpts →
    mem_rooted ∅ (initial_heap_memory ∪ initial_program_memory sw Cassert cmpts).
  Proof. apply mem_rooted_initial_memory_roots. Qed.

  (** The initial registers are rooted: cgp and csp are capabilities
      outside the heap, and the other registers hold integers. *)
  Lemma initial_pc_rooted_roots (R : gset Addr)
    (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    word_rooted R pc.
  Proof.
    intros (-> & _).
    apply word_rooted_cap_nonheap, cmpt_pcc_base_not_heap.
  Qed.

  Lemma initial_registers_rooted_roots (R : gset Addr)
    (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    ∀ r w, reg !! r = Some w → word_rooted R w.
  Proof.
    intros (_ & Hcgp & Hcsp & Hr) r w Hw.
    destruct (decide (r = cgp)) as [->|]; [rewrite Hcgp in Hw; injection Hw as <-;
      apply word_rooted_cap_nonheap, cmpt_cgp_base_not_heap|].
    destruct (decide (r = csp)) as [->|]; [rewrite Hcsp in Hw; injection Hw as <-;
      apply word_rooted_cap_disjoint, stack_disjoint_from_heap|].
    rewrite Hr in Hw; last set_solver. injection Hw as <-. apply word_rooted_int.
  Qed.

  (** The initial PC is the PCC of [main]; the other initial registers hold
      non-executable capabilities and integers. *)
  Lemma initial_pc_exec_ok (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    word_exec_ok pc.
  Proof. intros (-> & _). apply word_exec_ok_pcc. Qed.

  (** The initial PC is an unsealed executable capability. *)
  Lemma initial_pc_ok (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    pc_ok pc.
  Proof. intros (-> & _) _. done. Qed.

  Lemma initial_registers_exec_ok (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    ∀ r w, reg !! r = Some w → word_exec_ok w.
  Proof.
    intros (_ & Hcgp & Hcsp & Hr) r w Hw.
    destruct (decide (r = cgp)) as [->|]; [rewrite Hcgp in Hw; injection Hw as <-;
      by apply word_exec_ok_not_executable|].
    destruct (decide (r = csp)) as [->|]; [rewrite Hcsp in Hw; injection Hw as <-;
      by apply word_exec_ok_not_executable|].
    rewrite Hr in Hw; last set_solver. injection Hw as <-. apply word_exec_ok_int.
  Qed.

  Lemma initial_registers_rooted (sw : cmptSwitcher) (main : cmpt) (pc : Word) (reg : Reg) :
    is_initial_registers_of sw main pc reg →
    ∀ r w, reg !! r = Some w → word_rooted ∅ w.
  Proof. apply initial_registers_rooted_roots. Qed.

  (** The initial condition, with heap roots [R]. *)
  Lemma ghost_init_cond_roots (R : gset Addr) (pc : Word) (reg : Reg) (sreg : SReg) (m : Mem) :
    (∀ a, a ∈ R → is_heap_address a = true) →
    mem_rooted R m →
    word_rooted R pc →
    (∀ r w, reg !! r = Some w → word_rooted R w) →
    (∀ sr w, sreg !! sr = Some w → word_rooted R w) →
    mem_avoids_mmio m →
    reg !! cnull = Some (WInt 0) →
    mem_exec_ok m →
    word_exec_ok pc →
    (∀ r w, reg !! r = Some w → word_exec_ok w) →
    (∀ sr w, sreg !! sr = Some w → word_exec_ok w) →
    pc_ok pc →
    (∀ sr w, is_pc_sreg sr = true → sreg !! sr = Some w → pc_ok w) →
    ghost_init_cond (pc, reg, sreg, m, initial_heap_shadow) R.
  Proof.
    intros HR Hm Hpc Hreg Hsreg Hmmio Hnull Hmx Hpcx Hregx Hsregx Hpcok Hsregok.
    assert (∀ a, is_heap_address a = true →
      initial_heap_shadow !! a = Some ShadowLive) as Hsh.
    { intros a Ha. rewrite /initial_heap_shadow lookup_fmap /initial_heap_memory
        lookup_gset_to_gmap option_guard_True //.
      by apply elem_of_heap_addresses. }
    constructor; cbn.
    - exact HR.
    - intros a Ha. by apply Hsh, HR.
    - intros a Ha. eexists. by apply Hsh.
    - intros a w b Ha. by eapply Hm.
    - intros b. by eapply Hpc.
    - intros r w b _ Hw. by eapply Hreg.
    - intros sr w b Hw. by eapply Hsreg.
    - exact Hmmio.
    - intros w Hw. rewrite Hnull in Hw. by injection Hw as <-.
    - exact Hmx.
    - exact Hpcx.
    - exact Hregx.
    - exact Hsregx.
    - exact Hpcok.
    - exact Hsregok.
  Qed.

  (** The initial condition of a layout with heap roots [R]. *)
  Lemma ghost_init_cond_initial_layout_roots (R : gset Addr)
    (sw : cmptSwitcher) (Cassert : cmptAssert) (main : cmpt) (cmpts : list cmpt)
    (pm : Mem) (pc : Word) (reg : Reg) (sreg : SReg) :
    (∀ a, a ∈ R → is_heap_address a = true) →
    pm = initial_program_memory sw Cassert cmpts →
    initial_heap_memory ##ₘ pm →
    is_initial_registers_of sw main pc reg →
    is_initial_sregisters_of sw sreg →
    Forall is_z (stack_content sw) →
    Forall (λ C, mem_rooted R (mk_initial_cmpt C)) cmpts →
    Forall (λ C, mem_exec_ok (mk_initial_cmpt C)) cmpts →
    ghost_init_cond (pc, reg, sreg, initial_heap_memory ∪ pm, initial_heap_shadow) R.
  Proof.
    intros HR -> Hheap Hreg Hsreg Hstack Hcmpts Hcmpts_exec.
    pose proof (dom_initial_program_memory_switcher_assert sw Cassert cmpts) as Hdom.
    apply ghost_init_cond_roots; first done.
    - by apply mem_rooted_initial_memory_roots.
    - by eapply initial_pc_rooted_roots.
    - by eapply initial_registers_rooted_roots.
    - (* The trusted stack is in the program memory, hence outside the heap. *)
      intros sr w Hw. rewrite Hsreg in Hw. injection Hw as <-.
      destruct sr; try apply word_rooted_int.
      apply word_rooted_cap_disjoint.
      apply (trusted_stack_disjoint_from_heap_of_disjoint_dom _ _ Hheap). set_solver.
    - apply mem_avoids_mmio_union; first apply mem_avoids_mmio_initial_heap.
      apply mem_avoids_mmio_foldl_initial_cmpt, mem_avoids_mmio_union;
        [apply mem_avoids_mmio_initial_switcher|apply mem_avoids_mmio_initial_assert].
    - destruct Hreg as (_&_&_&Hr). apply Hr. set_solver.
    - by apply mem_exec_ok_initial_memory.
    - by eapply initial_pc_exec_ok.
    - by eapply initial_registers_exec_ok.
    - intros sr w Hw. rewrite Hsreg in Hw. injection Hw as <-.
      by destruct sr; apply word_exec_ok_not_executable.
    - by eapply initial_pc_ok.
    - (* MTCC and MEPCC start untagged. *)
      intros sr w Hsr Hw. rewrite Hsreg in Hw. injection Hw as <-.
      by destruct sr; apply pc_ok_untagged.
  Qed.

  (** The initial condition of a layout without heap roots. *)
  Lemma ghost_init_cond_initial_layout
    (sw : cmptSwitcher) (Cassert : cmptAssert) (main : cmpt) (cmpts : list cmpt)
    (pm : Mem) (pc : Word) (reg : Reg) (sreg : SReg) :
    pm = initial_program_memory sw Cassert cmpts →
    initial_heap_memory ##ₘ pm →
    is_initial_registers_of sw main pc reg →
    is_initial_sregisters_of sw sreg →
    Forall is_z (stack_content sw) →
    Forall (λ C, mem_rooted ∅ (mk_initial_cmpt C)) cmpts →
    Forall (λ C, mem_exec_ok (mk_initial_cmpt C)) cmpts →
    ghost_init_cond (pc, reg, sreg, initial_heap_memory ∪ pm, initial_heap_shadow) ∅.
  Proof. apply ghost_init_cond_initial_layout_roots. set_solver. Qed.

End initial_rootedness.

(** ** Entry-point resources *)

(** The entry-point map for a list of exported (unsealed) entries and their
    number of arguments: each entry is registered both as is and borrowed. *)
Definition exported_entries (ot : OType) (entries : list (Sealable * nat)) : gmap Word nat :=
  list_to_map
    (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)]) <$> entries)).

Lemma global_ne_borrow_sb (sb sb' : Sealable) :
  isGlobalSealable sb = true → sb ≠ borrow_sb sb'.
Proof. destruct sb as [ [] ? [] | [] ? [] ], sb'; cbn; intros Hg Heq; simplify_eq. Qed.

Lemma borrow_sb_inj_global (sb sb' : Sealable) :
  isGlobalSealable sb = true → isGlobalSealable sb' = true →
  borrow_sb sb = borrow_sb sb' → sb = sb'.
Proof.
  destruct sb as [ [] ? [] | [] ? [] ], sb' as [ [] ? [] | [] ? [] ]; cbn; intros; simplify_eq; done.
Qed.

Lemma exported_entries_keys_NoDup (ot : OType) (entries : list (Sealable * nat)) :
  NoDup entries.*1 →
  Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
  NoDup (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)]) <$> entries)).*1.
Proof.
  induction entries as [|[sb n] entries IH]; cbn; intros Hnodup Hglobal; first constructor.
  apply NoDup_cons in Hnodup as [Hsb Hnodup].
  apply Forall_cons in Hglobal as [Hg Hglobal].
  assert (∀ w, w ∈ (concat ((λ e, [(WSealed ot e.1, e.2); (WSealed ot (borrow_sb e.1), e.2)])
                              <$> entries)).*1 →
               ∃ sb', sb' ∈ entries.*1 ∧ (w = WSealed ot sb' ∨ w = WSealed ot (borrow_sb sb')))
    as Hkeys.
  { clear. induction entries as [|[sb' n'] entries IH]; cbn; intros w Hw;
      first by apply elem_of_nil in Hw.
    rewrite !elem_of_cons in Hw.
    destruct Hw as [ -> | [ -> | Hw ] ].
    - exists sb'; split; [left|left]; done.
    - exists sb'; split; [left|right]; done.
    - destruct (IH w Hw) as (sb'' & Hin & Hw'); exists sb''; split; [right|]; done.
  }
  rewrite Forall_forall in Hglobal.
  constructor; [|constructor]; last by apply IH; [|apply Forall_forall].
  - intros Hin; rewrite elem_of_cons in Hin.
    destruct Hin as [Heq | Hin].
    + simplify_eq; by eapply global_ne_borrow_sb.
    + destruct (Hkeys _ Hin) as (sb' & Hsb' & [Heq | Heq]); simplify_eq.
      * done.
      * by eapply global_ne_borrow_sb.
  - intros Hin.
    destruct (Hkeys _ Hin) as (sb' & Hsb' & [Heq | Heq]); simplify_eq.
    + pose proof (Hglobal _ Hsb') as Hg'; by destruct sb as [ [] ? [] | [] ? [] ].
    + apply borrow_sb_inj_global in Heq; [simplify_eq; done | done | by apply Hglobal].
Qed.

Section entries.
  Context {Σ : gFunctors} {entryg : entryGS Σ}.

  Lemma entries_split (ot : OType) (entries : list (Sealable * nat)) :
    NoDup entries.*1 →
    Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
    ([∗ map] w↦n ∈ exported_entries ot entries, w ↦□ₑ n) ⊢
    [∗ list] e ∈ entries, WSealed ot e.1 ↦□ₑ e.2 ∗ WSealed ot (borrow_sb e.1) ↦□ₑ e.2.
  Proof.
    intros Hnodup Hglobal.
    rewrite /exported_entries big_sepM_list_to_map;
      last by apply exported_entries_keys_NoDup.
    clear.
    iIntros "H".
    iInduction entries as [|[sb n] entries] "IH"; cbn; first done.
    iDestruct "H" as "($ & $ & H)".
    by iApply "IH".
  Qed.

End entries.

(** ** Iris adequacy for the assert flag

    The premise receives the program-logic resources of the initial state
    (registers, system registers, memory, shadow table, address claims, the
    non-atomic invariant token and the entry-point resources of [entries],
    sealed with [ot]) and must produce a WP for the machine together with
    the invariant of the assert flag. *)
Lemma cerise_flag_adequacy (Σ : gFunctors)
  {inv_preg : invGpreS Σ}
  {cerise_preg : ceriseGpreS Σ}
  {entry_preg : entryGpreS Σ}
  {na_invg : na_invariants.na_invG Σ}
  `{MP: MachineParameters}
  (ot : OType) (entries : list (Sealable * nat))
  (flagN : namespace) (flag : Addr) (H : gset Addr)
  (pc pc' : Word) (reg reg' : Reg) (sreg sreg' : SReg) (m m' : Mem) (sh sh' : ShadowTbl)
  (es : list griotte_lang.expr) :
  NoDup entries.*1 →
  Forall (λ sb, isGlobalSealable sb = true) entries.*1 →
  ghost_init_cond (pc, reg, sreg, m, sh) H →
  reg !! cnull = Some (WInt 0) →
  (∀ (ceriseg : ceriseG Σ),
     PC ↦ₚ lword_of_word pc -∗
     ([∗ map] r↦w ∈ lword_of_word <$> reg, r ↦ᵣ w) -∗
     ([∗ map] r↦w ∈ sreg, r ↦ₛᵣ lword_of_word w) -∗
     ([∗ map] a↦w ∈ m, a ↦ₐ lword_of_word w) -∗
     ([∗ map] a↦s ∈ sh, a ↦ₛ s) -∗
     ([∗ map] a↦c ∈ init_claims H, addr_alloc a c) -∗
     (* the pool of [ceriseg], not the [na_invg] parameter *)
     @na_own Σ (@cerise_instance.na_invG Σ (@cerise_nainvG Σ ceriseg)) cerise_nais ⊤ -∗
     ([∗ list] e ∈ entries, WSealed ot e.1 ↦□ₑ e.2 ∗ WSealed ot (borrow_sb e.1) ↦□ₑ e.2)
     ={⊤}=∗
     WP Seq (Instr Executable) {{ _, True }} ∗
     inv flagN (flag ↦ₐ WInt 0)) →
  rtc erased_step ([Seq (Instr Executable)], (pc, reg, sreg, m, sh)) (es, (pc', reg', sreg', m', sh')) →
  m' !! flag = Some (WInt 0).
Proof.
  intros Hnodup Hglobal Hinit Hnull Hwp Hstep.
  pose proof (@wp_invariance Σ griotte_lang _ NotStuck) as WPI. cbn in WPI.
  pose (fun (c: ExecConf) => mem c !! flag = Some (WInt 0%Z)) as state_is_good.
  specialize (WPI (Seq (Instr Executable)) (pc, reg, sreg, m, sh) es (pc', reg', sreg', m', sh')
                (state_is_good (pc', reg', sreg', m', sh'))).
  eapply WPI. 2: assumption. intros Hinv κs. clear WPI.
  iMod (cerise_ghost_init (pc, reg, sreg, m, sh) H Hinit)
    as (mem_heapg shadow_heapg pc_g reg_heapg sreg_heapg registryg addr_allocg)
       "(Hσ & HPC & Hreg & Hsreg & Hmem & Hshadow & Hclaims)".
  iEval (rewrite init_lmem_pointsto) in "Hmem".
  rewrite (init_lregs_cnull reg Hnull).
  iMod (entry_init (exported_entries ot entries)) as (entry_g) "Hentries".
  iMod (@na_alloc Σ na_invg) as (cerise_nais) "Hna".
  pose cerise_na_invs := Build_cerise_na_invs _ na_invg cerise_nais.
  pose ceriseg := {|
    cerise_invG := Hinv;
    cerise_nainvG := cerise_na_invs;
    mem_gen_memG := mem_heapg;
    shadowtbl_gen_regG := shadow_heapg;
    cerise_pcG := pc_g;
    reg_gen_regG := reg_heapg;
    sreg_gen_regG := sreg_heapg;
    entryG := entry_g;
    cerise_registryG := registryg;
    cerise_addr_allocG := addr_allocg |}.
  iDestruct (entries_split with "Hentries") as "Hentries"; [done..|].
  iMod (Hwp ceriseg with "HPC Hreg Hsreg Hmem Hshadow Hclaims Hna Hentries") as "[Hwp #Hflag]".
  iModIntro.
  iExists (fun σ _ _ => cerise_state_interp σ)%I.
  iExists (fun _ => True)%I. cbn. iFrame "Hσ".
  iSplitL "Hwp".
  { iApply (wp_mono with "Hwp"); iIntros (?) "?"; done. }
  iIntros "@".
  iExists (⊤ ∖ ↑flagN).
  iInv flagN as ">Hflag'" "Hclose".
  iDestruct (gen_heap_valid with "Hm Hflag'") as %Hm'_flag.
  iModIntro. iPureIntro.
  destruct (erasure_lookup_mem _ _ _ _ _ _ _ _ _ Her Hm'_flag)
    as (pw & Hpw & _ & _ & Hnonheap & _).
  destruct (Hnonheap eq_refl) as [Heq | (_ & Hb)]; last by destruct Hb.
  rewrite /state_is_good Hpw Heq //.
Qed.

(** ** Initial world, seal store and call stack *)
Section world_init.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {Cname : CmptNameG}
    {seal_store_preg : sealStorePreG Σ}
    {sts_preg : STS_preG LAddr region_type OType LWord Σ} {relpreg : relGpreS Σ}
    {cstack_preg : CSTACK_preG Σ}
    `{MP: MachineParameters}.

  Lemma initialise_world (Cs : list CmptName) (ots : gset OType) :
    CNames = list_to_set Cs →
    NoDup Cs →
    ⊢ |==> ∃ (seal_storeg : sealStoreG Σ) (relg : relGS Σ)
            (stsg : STSG LAddr region_type OType LWord Σ) (cstackg : CSTACKG Σ),
      ([∗ set] o ∈ ots, can_alloc_pred o) ∗
      cstack_full [] ∗
      cstack_frag [] ∗
      [∗ list] C ∈ Cs, world_interp (∅, (∅, ∅), ∅, ∅) C.
  Proof.
    intros HCNames HNoDup.
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (world_interp_init ots) as (relg stsg seal_storeg) "(Hworld_interp & Hseal_store)".
    rewrite HCNames big_sepS_list_to_set //.
    iModIntro; iExists seal_storeg, relg, stsg, cstackg; iFrame.
  Qed.

End world_init.

(** ** Worlds of the adversaries *)
Section adversary_world.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The world of an adversary compartment [C_cmpt] after the allocation of its
      imports, code and data (permanent), and of the switcher stack with state [ρ]. *)
  Definition adv_world_with (ρ : region_type) (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt)
    : WORLD :=
    std_update_multiple (std_update_compartment W C_cmpt) (stack_addrs sw) ρ.

  Lemma adv_world_with_heap ρ W sw C_cmpt :
    heap_std (adv_world_with ρ W sw C_cmpt) = heap_std W.
  Proof. by rewrite /adv_world_with std_update_multiple_heap std_update_compartment_heap. Qed.

  Lemma elem_of_dom_std_update_compartment (W : WORLD) (C_cmpt : cmpt) (a : Addr) :
    LNonHeap a ∈ dom (std (std_update_compartment W C_cmpt)) →
    a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
    ∨ a ∈ finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
    ∨ LNonHeap a ∈ dom (std W).
  Proof.
    intros Ha.
    pose proof (cmpt_import_size C_cmpt).
    pose proof (cmpt_code_size C_cmpt).
    rewrite /std_update_compartment in Ha.
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha].
    { left; rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr. }
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha]; first by right; left.
    apply elem_of_dom_std_multiple_update in Ha as [Ha|Ha]; last by right; right.
    left; rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
  Qed.

  (** The data of the main compartment is not in the world of an adversary. *)
  Lemma main_cgp_not_in_adv_world (ρ : region_type) (W : WORLD)
    (sw : cmptSwitcher) (main C_cmpt : cmpt) (a : Addr) :
    main ## C_cmpt →
    switcher_cmpt_disjoint main sw →
    LNonHeap a ∉ dom (std W) →
    a ∈ finz.seq_between (cmpt_b_cgp main) (cmpt_e_cgp main) →
    LNonHeap a ∉ dom (std (adv_world_with ρ W sw C_cmpt)).
  Proof.
    intros HmainC Hsw HaW Ha Hcontra.
    rewrite /adv_world_with in Hcontra.
    apply elem_of_dom_std_multiple_update in Hcontra as [Hcontra|Hcontra].
    { rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_switcher_stack_region
        /cmpt_region /cmpt_cgp_region in Hsw.
      rewrite /stack_addrs in Hcontra.
      set_solver. }
    apply elem_of_dom_std_update_compartment in Hcontra as [Hcontra | [Hcontra | Hcontra] ].
    - rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region
        /cmpt_cgp_region /cmpt_pcc_region in HmainC.
      set_solver.
    - rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region
        /cmpt_cgp_region in HmainC.
      set_solver.
    - done.
  Qed.

  (** A stack outside of the mmio and heap regions, whose addresses are
      temporary in the world, with [interp_in_mem] safety invariants, is safe
      to share. *)
  Lemma interp_stack_temporary (W : WORLD) (C : CmptName) (b e : Addr) :
    disjoint_from_mmio b e →
    disjoint_from_heap b e →
    Forall (λ a, std W !! LNonHeap a = Some Temporary) (finz.seq_between b e) →
    ([∗ list] a ∈ finz.seq_between b e, rel C (LNonHeap a) RWL interp_in_memC) -∗
    interp W C (WCap true RWL Local b e b).
  Proof.
    iIntros (Hmmio Hheap Htemp) "#Hrel".
    iEval (rewrite interp_unfold /=).
    iSplit.
    { iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      rewrite /addr_key.
      iExists RWL, (interp_in_mem RWL).
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp_in_mem).
      iDestruct (big_sepL_lookup with "Hrel") as "$"; first done.
      iSplit; first (iNext ; by iApply zcond_interp_in_mem).
      iSplit; first (iNext ; by iApply rcond_interp_in_mem).
      iSplit; first (iNext ; by iApply wcond_interp_in_mem).
      assert (std W !! LNonHeap a = Some Temporary) by (rewrite Forall_lookup in Htemp; eauto).
      iSplit; last done.
      iApply (monoReq_interp_in_mem _ _ _ _ Temporary); done. }
    iPureIntro; split; first done.
    by apply heap_cap_valid_disjoint.
  Qed.

  Lemma adv_world_free_cmpt (W : WORLD) (C_cmpt : cmpt) :
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! LNonHeap a = None) →
    Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))
    ∧ Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
    ∧ Forall (λ k, std W !! LNonHeap k = None) (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)).
  Proof.
    intros Hfree.
    pose proof (cmpt_import_size C_cmpt).
    pose proof (cmpt_code_size C_cmpt).
    rewrite !Forall_forall.
    split; [|split]; intros a Ha; apply Hfree;
      rewrite /cmpt_region /cmpt_pcc_region /cmpt_cgp_region.
    - assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)); last set_solver.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
    - assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)); last set_solver.
      rewrite !elem_of_finz_seq_between in Ha |- *; solve_addr.
    - set_solver.
  Qed.

  Lemma adv_world_free_stack (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) :
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall (λ k, std (std_update_compartment W C_cmpt) !! LNonHeap k = None) (stack_addrs sw).
  Proof.
    intros Hsw Hfree.
    apply Forall_forall; intros a Ha.
    eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
  Qed.

  Lemma stack_addrs_nonheap (sw : cmptSwitcher) :
    Forall (λ a, is_heap_address a = false) (stack_addrs sw).
  Proof.
    apply Forall_forall; intros a Ha.
    eapply disjoint_from_heap_not_in; first apply stack_disjoint_from_heap.
    apply withinBounds_true_iff. by apply elem_of_finz_seq_between.
  Qed.

  (** ** Sealed entries exported by an adversary *)

  Lemma exported_entries_words_normalise (C_cmpt : cmpt) :
    normalise_sealed_words (exported_entries_words C_cmpt) =
    list_to_set ((λ a, lword_of_word (WSealable (cmpt_export C_cmpt a))) <$> cmpt_exp_tbl_addrs C_cmpt).
  Proof.
    rewrite /normalise_sealed_words /exported_entries_words /exported_entries_sealable
      /cmpt_exp_tbl_addrs /cmpt_export.
    apply set_eq; intros w.
    rewrite elem_of_map elem_of_list_to_set.
    setoid_rewrite elem_of_list_to_set.
    split.
    - intros (w' & -> & Hw').
      apply list_elem_of_fmap in Hw' as (sb & -> & Hsb).
      apply list_elem_of_fmap.
      apply elem_of_app in Hsb as [Hsb|Hsb];
        apply list_elem_of_fmap in Hsb as (a & -> & Ha); by exists a.
    - intros (a & -> & Ha)%list_elem_of_fmap.
      eexists; split; last first.
      { apply list_elem_of_fmap; eexists; split; first done.
        apply elem_of_app; left; apply list_elem_of_fmap; by exists a. }
      done.
  Qed.

  Lemma cmpt_exp_tbl_addrs_exports_NoDup (C_cmpt : cmpt) :
    NoDup ((λ a, lword_of_word (WSealable (cmpt_export C_cmpt a))) <$> cmpt_exp_tbl_addrs C_cmpt).
  Proof.
    apply NoDup_fmap_2_strong; last apply finz_seq_between_NoDup.
    intros a a' _ _ Heq; by simplify_eq.
  Qed.

  Lemma exported_entries_sealed_words (C_cmpt : cmpt) (v : LWord) :
    v ∈ exported_entries_sealed C_cmpt →
    ∃ sb, v = lword_of_word (WSealed switcher.ot_switcher sb) ∧
          heap_authority_base (WSealed switcher.ot_switcher sb) = None ∧
          (∃ g a, sb = SCap true RO g (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt) a) ∧
          {[lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb))]}
            ⊆ exported_entries_words C_cmpt.
  Proof.
    rewrite /exported_entries_sealed /exported_entries_words elem_of_list_to_set.
    intros (sb & -> & Hsb)%list_elem_of_fmap.
    exists sb; split; first done.
    split.
    { rewrite /exported_entries_sealable in Hsb.
      destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        match type of Hauth with
        | heap_cap_base (WSealed ?o (SCap ?t ?p ?g ?b ?e ?a)) = _ =>
            pose proof (sealed_cap_nonheap o t p g b e a (cmpt_exp_tbl_base_not_heap C_cmpt))
              as Hnonheap
        end;
        unfold is_heap_cap in Hnonheap; rewrite Hauth in Hnonheap; discriminate. }
    split.
    { rewrite /exported_entries_sealable in Hsb.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        by eexists _, a. }
    apply union_subseteq; split; apply singleton_subseteq_l, elem_of_list_to_set,
      list_elem_of_fmap.
    - by exists sb.
    - rewrite /exported_entries_sealable in Hsb |- *.
      apply elem_of_app in Hsb as [Hsb|Hsb]; apply list_elem_of_fmap in Hsb as (a & -> & Ha);
        (eexists; split; [done|]); apply elem_of_app; right; apply list_elem_of_fmap; by exists a.
  Qed.

  (** The sealed exported entries are safe, once their sealed words are in the
      sealing part of the world. *)
  Lemma exported_entries_sealed_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) :
    sts_seals_std C switcher.ot_switcher (exported_entries_words C_cmpt) -∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v.
  Proof.
    iIntros "#Hseal".
    iApply big_sepS_intro; iIntros "!>" (v Hv).
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _ & (g & a & ->) & Hsub).
    iEval (rewrite interp_unfold /= /interp_sb).
    iSplit; first (iApply sts_seals_std_weaken; done).
    iPureIntro; cbn.
    apply heap_cap_valid_disjoint, cmpt_exp_tbl_disjoint_from_heap.
  Qed.

  (** Allocate an adversary compartment [C_cmpt] in the world: its imports,
      code and data become permanent, and its exported entries are sealed with
      [ot_switcher] in the world. The caller proves that the exported entries
      satisfy the sealing predicate of the switcher ([Hexports]) and that the
      imports are safe ([Himports]). *)
  Lemma alloc_adversary_compartment {E : coPset} (W : WORLD) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    (∀ a, a ∈ cmpt_region C_cmpt → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp W' C ∗
    interp W' C (cmpt_pcc_cap C_cmpt) ∗
    interp W' C (cmpt_cgp_cap C_cmpt) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v.
  Proof.
    intros W' Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports Hworld".
    destruct (adv_world_free_cmpt W C_cmpt Hfree) as (Hfree_imports & Hfree_code & Hfree_data).
    iAssert (□ ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp_in_mem RWL W' C v) -∗
               [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v)%I as "Hto_interp".
    { iIntros "#Hexp".
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & Hbase & _).
      iApply (interp_in_mem_load_result with "Hv").
      right; split; [reflexivity|].
      apply filter_heap_nonheap; exact Hbase. }
    iMod (alloc_compartment_interp with "HC_imports HC_code HC_data [Himports] Hworld")
      as "($ & $ & $ & _ & #Hexp)"; [done..| |].
    { iIntros "(#Hpcc & #Hcgp & Hworld)".
      iMod (world_interp_open_sealing_update' _ C _ ot_switcher_propC switcher.ot_switcher
              (exported_entries_words C_cmpt) with "Hseal_pred [] [] Hworld")
        as "(Hworld & #Hseal)".
      { iIntros (w); iApply mono_priv_ot_switcher. }
      { rewrite exported_entries_words_normalise big_sepS_list_to_set;
          last apply cmpt_exp_tbl_addrs_exports_NoDup.
        rewrite big_sepL_fmap.
        iApply big_sepL_intro; iIntros "!>" (i a Ha); iNext.
        iApply ("Hexports" with "[//] Hpcc Hcgp"). }
      iDestruct (exported_entries_sealed_interp W' with "Hseal") as "#Hexp".
      iModIntro; iFrame "Hworld".
      iSplitL "Himports"; first (iApply "Himports"; iFrame "#").
      iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
      by iApply interp_to_in_mem. }
    iModIntro. by iApply "Hto_interp".
  Qed.

  (** Initialise the world of an adversary compartment [C_cmpt]:
      - its imports, code and data become permanent;
      - its exported entries are sealed with [ot_switcher] in the world;
      - the switcher stack becomes temporary.
      The caller proves that the exported entries satisfy the sealing
      predicate of the switcher ([Hexports]) and that the imports are safe
      ([Himports]). *)
  Lemma initialise_adversary_world {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Temporary W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    Forall is_z (stack_content sw) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    [[ b_stack sw, e_stack sw ]] ↦ₐ [[ lword_of_word <$> stack_content sw ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    interp Wadv C (stack_cap sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata Hstack.
    iIntros "#Hseal_pred HC_imports HC_code HC_data Hstack #Hexports Himports Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_temp_sepL2_nonheap _ _ (stack_addrs sw)
            (lword_of_word <$> stack_content sw) RWL interp_in_memC
           with "Hworld [Hstack]") as "(Hworld & #Hrel_stk)".
    { apply stack_addrs_nonheap. }
    { done. }
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
    { rewrite big_sepL2_fmap_r.
      iEval (rewrite /region_pointsto big_sepL2_fmap_r) in "Hstack".
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
        pointsto k (DfracOwn (pos_to_Qp 1)) (lword_of_word v))) with "Hstack").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros "Hv". rewrite /TmpRes key_pointsto_nonheap.
      iFrame "Hv".
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      iSplit; first done.
      iSplit.
      { iEval (rewrite /interp_in_mem_pre /=).
        iApply interp_int. }
      rewrite mono_temporary_eq; cbn; iApply future_pub_mono_interp_in_mem_z.
    }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    assert (heap_std W' = heap_std Wadv) as Hheap.
    { by rewrite /Wadv adv_world_with_heap /W' std_update_compartment_heap. }
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hcgp"); eauto).
    iSplit.
    { iApply interp_stack_temporary; last done.
      - apply stack_disjoint_from_mmio.
      - apply stack_disjoint_from_heap.
      - apply Forall_forall; intros a Ha.
        by apply std_sta_update_multiple_lookup_in_i. }
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_monotone_sd_same_heap with "[] Hv").
  Qed.

  (** Same as [initialise_adversary_world], but the switcher stack is
      allocated as revoked: the caller keeps its points-to predicates. *)
  Lemma initialise_adversary_world_revoked {E : coPset}
    (W : WORLD) (sw : cmptSwitcher) (C_cmpt : cmpt) (C : CmptName) :
    let W' := std_update_compartment W C_cmpt in
    let Wadv := adv_world_with Revoked W sw C_cmpt in
    switcher_cmpt_disjoint C_cmpt sw →
    (∀ a, a ∈ cmpt_region C_cmpt ∨ a ∈ stack_addrs sw → std W !! LNonHeap a = None) →
    Forall is_z (cmpt_code C_cmpt) →
    Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    [[ cmpt_b_pcc C_cmpt, cmpt_a_code C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_imports C_cmpt ]] -∗
    [[ cmpt_a_code C_cmpt, cmpt_e_pcc C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_code C_cmpt ]] -∗
    [[ cmpt_b_cgp C_cmpt, cmpt_e_cgp C_cmpt ]] ↦ₐ [[ lword_of_word <$> cmpt_data C_cmpt ]] -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W' C (cmpt_pcc_cap C_cmpt) -∗
        interp W' C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W' C (WSealable (cmpt_export C_cmpt a))) -∗
    ((interp W' C (cmpt_pcc_cap C_cmpt) ∗ interp W' C (cmpt_cgp_cap C_cmpt) ∗
      [∗ set] v ∈ exported_entries_sealed C_cmpt, interp W' C v) -∗
     [∗ list] v ∈ lword_of_word <$> cmpt_imports C_cmpt,
       interp_in_memC (W', C, v) ∗ future_priv_mono C interp_in_memC v) -∗
    world_interp W C
    ={E}=∗
    world_interp Wadv C ∗
    interp Wadv C (cmpt_pcc_cap C_cmpt) ∗
    interp Wadv C (cmpt_cgp_cap C_cmpt) ∗
    StackRevokedResources Wadv C (stack_addrs sw) ∗
    [∗ set] v ∈ exported_entries_sealed C_cmpt, interp Wadv C v.
  Proof.
    intros W' Wadv Hsw Hfree Hcode Hdata.
    iIntros "#Hseal_pred HC_imports HC_code HC_data #Hexports Himports Hworld".
    iMod (alloc_adversary_compartment with
           "Hseal_pred HC_imports HC_code HC_data Hexports Himports Hworld")
      as "(Hworld & #Hpcc & #Hcgp & #Hexp)"; eauto.
    iMod (world_interp_extend_revoked_sepL2_nonheap _ _ (stack_addrs sw) RWL interp_in_memC
           with "Hworld")
      as "(Hworld & Hrel_stk)".
    { apply stack_addrs_nonheap. }
    { apply adv_world_free_stack; first done.
      intros a Ha; apply Hfree; by right. }
    iModIntro; iFrame "Hworld".
    assert (related_sts_priv_world W' Wadv) as Hrelated.
    { apply related_sts_pub_priv_world, related_sts_pub_update_multiple.
      eapply Forall_impl; first (apply adv_world_free_stack; first done).
      - intros a Ha; apply Hfree; by right.
      - intros a Ha; cbn in *; by rewrite not_elem_of_dom.
    }
    assert (heap_std W' = heap_std Wadv) as Hheap.
    { by rewrite /Wadv adv_world_with_heap /W' std_update_compartment_heap. }
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hpcc"); eauto).
    iSplit; first (iApply (interp_monotone_nl_same_heap with "[] [] Hcgp"); eauto).
    iSplitL "Hrel_stk"; first by iApply StackWorldResources_from_rel_stack.
    iApply (big_sepS_impl with "Hexp"); iIntros "!>" (v Hv) "Hv".
    destruct (exported_entries_sealed_words C_cmpt v Hv) as (sb & -> & _).
    by iApply (interp_monotone_sd_same_heap with "[] Hv").
  Qed.

End adversary_world.

Notation adv_world := (adv_world_with Temporary).
Notation adv_world_revoked := (adv_world_with Revoked).

(** ** Exported entry points of an adversary *)
Section adversary_exports.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  (** The [i]-th entry of the export table of an adversary [C_cmpt],
      at address [a], satisfies the sealing predicate of the switcher. *)
  Lemma adversary_export_prop
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (Nswitcher : namespace)
    (i args off : nat) (a : Addr) :
    cmpt_exp_tbl_entries C_cmpt !! i = Some (WInt (encode_entry_point args off)) →
    (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a = a →
    args < 7 →
    is_Some (cmpt_b_pcc C_cmpt + off%nat)%a →
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    switcher_static -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    ([∗ list] a;v ∈ cmpt_exp_tbl_addrs C_cmpt ; cmpt_exp_tbl_entries C_cmpt,
       a ↦ₐ□ lword_of_word v) -∗
    interp W C (cmpt_pcc_cap C_cmpt) -∗
    interp W C (cmpt_cgp_cap C_cmpt) -∗
    WSealed switcher.ot_switcher (cmpt_export C_cmpt a) ↦□ₑ args -∗
    WSealed switcher.ot_switcher (borrow_sb (cmpt_export C_cmpt a)) ↦□ₑ args -∗
    ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a)).
  Proof.
    intros Hi Ha Hargs Hentry_some.
    iIntros "#Hswitcher #Hswitcher_static #Hpcc #Hcgp #Hentries #Hinterp_pcc #Hinterp_cgp #Hentry #Hentry'".
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hsize.
    assert (i < length (cmpt_exp_tbl_entries C_cmpt)) as Hi_lt
        by (by apply lookup_lt_Some in Hi).
    assert (cmpt_exp_tbl_addrs C_cmpt !! i = Some a) as Ha_lookup.
    { rewrite /cmpt_exp_tbl_addrs
        (finz_seq_between_lookup _ _ _ (length (cmpt_exp_tbl_entries C_cmpt))) //.
      f_equal; solve_addr. }
    iDestruct (big_sepL2_lookup with "Hentries") as "Hentry_inv"; [done..|].
    iApply (ot_switcher_interp _ _ _ Global _ args off with
              "Hswitcher Hswitcher_static Hpcc Hcgp Hentry_inv Hinterp_pcc Hinterp_cgp Hentry Hentry'");
      [solve_addr|lia|done].
  Qed.

  (** The [i]-th sealed entry of the export table of an adversary [C_cmpt]
      is safe to share. *)
  Lemma adversary_export_interp (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (i : nat) (a : Addr) :
    (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a = a →
    i < length (cmpt_exp_tbl_entries C_cmpt) →
    ([∗ set] v ∈ exported_entries_sealed C_cmpt, interp W C v) -∗
    interp W C (WSealed switcher.ot_switcher (cmpt_export C_cmpt a)).
  Proof.
    intros <- Hi.
    iIntros "#Hexp".
    iApply (big_sepS_elem_of with "Hexp").
    rewrite /exported_entries_sealed /exported_entries_sealable elem_of_list_to_set.
    apply list_elem_of_fmap; eexists; split; first done.
    apply elem_of_app; left.
    apply list_elem_of_fmap; eexists; split; first done.
    by apply cmpt_exp_tbl_addrs_elem_of.
  Qed.

  (** All the entries of the export table of an adversary [C_cmpt] satisfy
      the sealing predicate of the switcher, given its export table as a list
      of pairs (number of arguments, offset) and the entry-point resources of
      each entry. This is the premise of [initialise_adversary_world]. *)
  Lemma adversary_exports_prop
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt) (Nswitcher : namespace)
    (exports : list (nat * nat)) :
    cmpt_exp_tbl_entries C_cmpt = (λ e : nat * nat, WInt (encode_entry_point e.1 e.2)) <$> exports →
    Forall (λ e, e.1 < 7) exports →
    Forall (λ e : nat * nat, is_Some (cmpt_b_pcc C_cmpt + e.2%nat)%a) exports →
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    switcher_static -∗
    cmpt_exp_tbl_pcc C_cmpt ↦ₐ□ cmpt_pcc_cap C_cmpt -∗
    cmpt_exp_tbl_cgp C_cmpt ↦ₐ□ cmpt_cgp_cap C_cmpt -∗
    ([∗ list] a;v ∈ cmpt_exp_tbl_addrs C_cmpt ; cmpt_exp_tbl_entries C_cmpt,
       a ↦ₐ□ lword_of_word v) -∗
    ([∗ list] i ↦ e ∈ exports,
       WSealed switcher.ot_switcher
         (cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a) ↦□ₑ e.1 ∗
       WSealed switcher.ot_switcher
         (borrow_sb (cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt ^+ i)%a)) ↦□ₑ e.1) -∗
    □ (∀ i a, ⌜cmpt_exp_tbl_addrs C_cmpt !! i = Some a⌝ -∗
        interp W C (cmpt_pcc_cap C_cmpt) -∗
        interp W C (cmpt_cgp_cap C_cmpt) -∗
        ot_switcher_prop W C (WSealable (cmpt_export C_cmpt a))).
  Proof.
    intros Htbl Hargs Hentries_some.
    iIntros "#Hswitcher #Hswitcher_static #Hpcc #Hcgp #Hentries #Hexports !>"
      (i a Ha) "#Hinterp_pcc #Hinterp_cgp".
    destruct (cmpt_exp_tbl_addrs_lookup _ _ _ Ha) as [-> Hi].
    rewrite Htbl length_fmap in Hi.
    destruct (lookup_lt_is_Some_2 _ _ Hi) as [ [args offset] He].
    iDestruct (big_sepL_lookup with "Hexports") as "[Hentry Hentry']"; first exact He.
    iApply (adversary_export_prop _ _ _ _ i args offset
             with "Hswitcher Hswitcher_static Hpcc Hcgp Hentries Hinterp_pcc Hinterp_cgp Hentry Hentry'").
    - by rewrite Htbl list_lookup_fmap He.
    - done.
    - by apply (Forall_lookup_1 _ _ _ _ Hargs He).
    - by apply (Forall_lookup_1 _ _ _ _ Hentries_some He).
  Qed.

End adversary_exports.

(** ** Imports of an adversary

    The imports of an adversary are safe to store in its memory: the
    switcher call sentry, and words sealed in the world (for instance, the
    entries exported by a service compartment). *)
Section adversary_imports.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}.

  Lemma switcher_call_import_safe (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    let w := lword_of_word (WSentry FwdDisable true XSRW_ Local
               switcher.b_switcher switcher.e_switcher switcher.a_switcher_call) in
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    switcher_static -∗
    interp_in_memC (W, C, w) ∗ future_priv_mono C interp_in_memC w.
  Proof.
    intros w; subst w.
    iIntros "#Hswitcher #Hswitcher_static".
    assert (heap_authority_base
              (WSentry FwdDisable true XSRW_ Local
                 switcher.b_switcher switcher.e_switcher switcher.a_switcher_call) = None)
      as Hcall_nonheap.
    { destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      pose proof switcher_call_sentry_not_heap as Hnonheap.
      unfold is_heap_cap in Hnonheap; rewrite Hauth in Hnonheap; discriminate. }
    iEval (cbn); iSplit.
    - iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      by iApply (interp_switcher_call with "[$Hswitcher $Hswitcher_static]").
    - iIntros "!>" (W' W'' Hrel) "_".
      iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      by iApply (interp_switcher_call with "[$Hswitcher $Hswitcher_static]").
  Qed.

  (** A word sealed with [o] is safe, in any world, once the sealable and
      its borrowed version are in the sealing part of the world. *)
  Lemma interp_sealed_of_seals (W : WORLD) (C : CmptName) (o : OType)
    (ws : gset LWord) (sb : Sealable) :
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ ws →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    sts_seals_std C o ws -∗
    interp W C (WSealed o sb).
  Proof.
    iIntros (Hsub Hheap) "#Hseal".
    iEval (rewrite interp_unfold /= /interp_sb).
    destruct (get_tag_sealable sb); last done.
    iSplit; first (iApply (sts_seals_std_weaken with "Hseal"); by destruct sb).
    iPureIntro.
    destruct sb as [ [] p g b e a | [] ? ? ? ]; cbn; try done.
    apply heap_cap_valid_disjoint; by eapply Hheap.
  Qed.

  (** A global word sealed in the world is a safe import. *)
  Lemma sealed_import_safe (W : WORLD) (C : CmptName) (o : OType)
    (ws : gset LWord) (sb : Sealable) :
    let w := lword_of_word (WSealed o sb) in
    isGlobalSealable sb = true →
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ ws →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    sts_seals_std C o ws -∗
    interp_in_memC (W, C, w) ∗ future_priv_mono C interp_in_memC w.
  Proof.
    intros w Hglobal Hsub Hheap; subst w.
    iIntros "#Hseal".
    iSplit.
    - iApply interp_to_in_mem. by iApply interp_sealed_of_seals.
    - iIntros (W' W'') "!> %Hrelated Hinterp".
      iEval (cbn) in "Hinterp".
      iApply (interp_in_mem_monotone_nl with "Hinterp"); first done.
      by destruct sb as [ [] ? [] | [] ? [] ].
  Qed.

End adversary_imports.

(** ** Entry points exported by a service compartment *)
Section service_exports.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** The sealed words of a list of exported entries: each entry and its
      borrowed version. *)
  Definition exports_words (sbs : list Sealable) : gset LWord :=
    ⋃ ((λ sb, {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]}) <$> sbs).

  Lemma exports_words_elem_of (sbs : list Sealable) (sb : Sealable) :
    sb ∈ sbs →
    {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ⊆ exports_words sbs.
  Proof.
    intros Hsb w Hw. rewrite /exports_words elem_of_union_list.
    eexists; split; last done.
    apply list_elem_of_fmap. by exists sb.
  Qed.

  (** Seal the (global) exported entries [sbs] of a service compartment with
      [ot_switcher] in the world [W] of a compartment [C], given that they
      satisfy the sealing predicate of the switcher in the updated world. *)
  Lemma seal_service_exports (W : WORLD) (C : CmptName) (sbs : list Sealable) :
    let W' := <o[ switcher.ot_switcher := exports_words sbs ]o> W in
    Forall (λ sb, isGlobalSealable sb = true) sbs →
    switcher.ot_switcher ∉ dom (seal_std W) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    □ ([∗ list] sb ∈ sbs, ot_switcher_prop W' C (WSealable sb)) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗ sts_seals_std C switcher.ot_switcher (exports_words sbs).
  Proof.
    intros W' Hglobal Hfresh.
    iIntros "#Hseal_pred #Hprops Hworld".
    iMod (world_interp_salloc W C ot_switcher_propC switcher.ot_switcher (exports_words sbs)
           with "Hseal_pred [] [] Hworld") as "($ & $)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { iApply big_sepS_intro; iIntros "!>" (w Hw).
      rewrite /normalise_sealed_words elem_of_map in Hw.
      destruct Hw as (w' & -> & Hw').
      rewrite /exports_words elem_of_union_list in Hw'.
      destruct Hw' as (X & HX & Hw').
      apply list_elem_of_fmap in HX as (sb & -> & Hsb).
      assert (lforce_global w' = lword_of_word (WSealable sb)) as ->.
      { rewrite Forall_forall in Hglobal. specialize (Hglobal _ Hsb).
        apply elem_of_union in Hw' as [->%elem_of_singleton | ->%elem_of_singleton];
          destruct sb as [ [] ? [] | [] ? [] ]; by cbn in *. }
      iNext. iDestruct (big_sepL_elem_of with "Hprops") as "$"; done. }
    done.
  Qed.

End service_exports.

(** ** Initial heap *)
Section initial_heap.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP: MachineParameters}.

  (** The resources of the initial heap: its memory and its unpainted
      shadow entries, in the form taken by an allocator initialisation. *)
  Lemma initial_heap_resources :
    ([∗ map] a↦w ∈ initial_heap_memory, a ↦ₐ lword_of_word w) -∗
    ([∗ map] a↦s ∈ initial_heap_shadow, a ↦ₛ s) -∗
    [∗ map] a↦v ∈ lword_of_word <$> initial_heap_memory, a ↦ₐ v ∗ a ↦ₛ ShadowLive.
  Proof.
    iIntros "Hheap Hshadow".
    iEval (rewrite /initial_heap_shadow big_sepM_fmap) in "Hshadow".
    rewrite big_sepM_fmap.
    iApply big_sepM_sep; iFrame.
  Qed.

End initial_heap.

(** ** Exported entry points of the main compartment *)
Section main_exports.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}.

  (** Seal an exported entry [sb] of the main compartment with [ot_switcher]
      in the world [W], given that it satisfies the sealing predicate of the
      switcher in the updated world. *)
  Lemma seal_main_export (W : WORLD) (C : CmptName) (sb : Sealable) :
    let W' := <o[ switcher.ot_switcher :=
                 {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]} ]o> W in
    isGlobalSealable sb = true →
    (∀ p g b e a, sb = SCap true p g b e a → disjoint_from_heap b e) →
    switcher.ot_switcher ∉ dom (seal_std W) →
    seal_pred switcher.ot_switcher ot_switcher_propC -∗
    ot_switcher_prop W' C (WSealable sb) -∗
    world_interp W C
    ==∗
    world_interp W' C ∗
    interp W' C (WSealed switcher.ot_switcher sb).
  Proof.
    intros W' Hglobal Hheap Hfresh.
    iIntros "#Hseal_pred #Hprop Hworld".
    iMod (world_interp_salloc W C ot_switcher_propC switcher.ot_switcher
            {[ lword_of_word (WSealable sb); lword_of_word (borrow (WSealable sb)) ]}
           with "Hseal_pred [] [] Hworld")
      as "($ & #Hseal)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { rewrite (normalise_sealed_words_borrow (lword_of_word (WSealable sb))) big_sepS_singleton.
      replace (lforce_global (lword_of_word (WSealable sb))) with (lword_of_word (WSealable sb))
        by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
      iFrame "Hprop". }
    iModIntro.
    iEval (rewrite interp_unfold /= /interp_sb).
    replace (get_tag_sealable sb) with true
      by (destruct sb as [ [] ? [] | [] ? [] ]; by cbn in * ).
    iSplit; first done.
    iPureIntro.
    destruct sb as [ [] p g b e a | [] ? ? ? ]; cbn; try done.
    apply heap_cap_valid_disjoint; by eapply Hheap.
  Qed.

End main_exports.

(** ** Size obligations of the main compartment *)
Section main_sizes.
  Context `{MP: MachineParameters}.

  Lemma main_spec_size_obligations (main : cmpt) (imports code data : list Word) :
    cmpt_imports main = imports →
    cmpt_code main = code →
    cmpt_data main = data →
    SubBounds (cmpt_b_pcc main) (cmpt_e_pcc main)
      (cmpt_a_code main) (cmpt_a_code main ^+ length code)%a
    ∧ (cmpt_b_cgp main + length data)%a = Some (cmpt_e_cgp main)
    ∧ (cmpt_b_pcc main + length imports)%a = Some (cmpt_a_code main).
  Proof.
    intros <- <- <-.
    pose proof (cmpt_import_size main).
    pose proof (cmpt_code_size main).
    pose proof (cmpt_data_size main).
    rewrite /SubBounds.
    split; [solve_addr|split; done].
  Qed.

  (** Exported entries of disjoint compartments are distinct
      (for the [NoDup] premise of [cerise_flag_adequacy]). *)
  Lemma cmpt_export_disjoint (C1 C2 : cmpt) (a1 a2 : Addr) :
    C1 ## C2 → cmpt_export C1 a1 ≠ cmpt_export C2 a2.
  Proof.
    intros Hdis Heq.
    apply (exported_entry_point_disjoint C1 C2 true true RO RO Global Global a1 a2 Hdis).
    rewrite /cmpt_export in Heq; by rewrite Heq.
  Qed.

  Lemma cmpt_exp_tbl_cgp_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_cgp C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ 1)%a.
  Proof. pose proof (cmpt_exp_tbl_pcc_size C_cmpt); solve_addr. Qed.

  Lemma cmpt_exp_tbl_entries_start_eq (C_cmpt : cmpt) :
    cmpt_exp_tbl_entries_start C_cmpt = (cmpt_exp_tbl_pcc C_cmpt ^+ 2)%a.
  Proof.
    pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size C_cmpt).
    solve_addr.
  Qed.

  (** The main compartment's code region, as a [codefrag]. *)
  Lemma cmpt_code_codefrag `{Σ : gFunctors} {ceriseg : ceriseG Σ} (main : cmpt) :
    [[ cmpt_a_code main, cmpt_e_pcc main ]] ↦ₐ [[ lword_of_word <$> cmpt_code main ]] ⊣⊢
    codefrag (cmpt_a_code main) (cmpt_code main).
  Proof.
    rewrite /codefrag.
    replace (cmpt_a_code main ^+ length (cmpt_code main))%a with (cmpt_e_pcc main); first done.
    pose proof (cmpt_code_size main); solve_addr.
  Qed.

End main_sizes.
