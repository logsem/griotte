From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  deep_immutability deep_immutability_adequacy
  disjoint_regions_tactics.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition droe_main_pcc_b : Addr := A 9.
Definition droe_main_code_a : Addr := A 12.
Definition droe_main_pcc_e : Addr := A 64.
Definition droe_C_pcc_b : Addr := A 64.
Definition droe_C_code_a : Addr := A 65.
Definition droe_C_pcc_e : Addr := A 69.
Definition droe_main_cgp_b : Addr := A 69.
Definition droe_main_cgp_e : Addr := A 71.
Definition droe_C_cgp_b : Addr := A 71.
Definition droe_C_cgp_e : Addr := A 72.
Definition droe_main_exp_pcc : Addr := A 72.
Definition droe_main_exp_cgp : Addr := A 73.
Definition droe_main_exp_entries_b : Addr := A 74.
Definition droe_main_exp_entries_e : Addr := A 74.
Definition droe_C_exp_pcc : Addr := A 74.
Definition droe_C_exp_cgp : Addr := A 75.
Definition droe_C_exp_entries_b : Addr := A 76.
Definition droe_C_exp_entries_e : Addr := A 77.
Definition droe_assert_b : Addr := A 77.
Definition droe_assert_cap : Addr := A 89.
Definition droe_assert_e : Addr := A 90.
Definition droe_assert_flag : Addr := A 90.
Definition droe_switcher_b : Addr := A 91.
Definition droe_switcher_call : Addr := A 92.
Definition droe_switcher_return : Addr := A 180.
Definition droe_switcher_e : Addr := A 242.
Definition droe_stack_b : Addr := A 1024.
Definition droe_stack_e : Addr := A 1124.
Definition droe_trusted_stack_b : Addr := A 4096.
Definition droe_trusted_stack_e : Addr := A 4196.
Definition droe_switcher_otype : OType := OT 9.

Ltac unfold_droe_addresses :=
  unfold droe_main_pcc_b, droe_main_code_a, droe_main_pcc_e,
    droe_C_pcc_b, droe_C_code_a, droe_C_pcc_e,
    droe_main_cgp_b, droe_main_cgp_e, droe_C_cgp_b, droe_C_cgp_e,
    droe_main_exp_pcc, droe_main_exp_cgp, droe_main_exp_entries_b,
    droe_main_exp_entries_e, droe_C_exp_pcc, droe_C_exp_cgp,
    droe_C_exp_entries_b, droe_C_exp_entries_e, droe_assert_b,
    droe_assert_cap, droe_assert_e, droe_assert_flag, droe_switcher_b,
    droe_switcher_call, droe_switcher_return, droe_switcher_e,
    droe_stack_b, droe_stack_e, droe_trusted_stack_b,
    droe_trusted_stack_e, droe_switcher_otype.

Ltac unfold_droe_addresses_in H :=
  unfold droe_main_pcc_b, droe_main_code_a, droe_main_pcc_e,
    droe_C_pcc_b, droe_C_code_a, droe_C_pcc_e,
    droe_main_cgp_b, droe_main_cgp_e, droe_C_cgp_b, droe_C_cgp_e,
    droe_main_exp_pcc, droe_main_exp_cgp, droe_main_exp_entries_b,
    droe_main_exp_entries_e, droe_C_exp_pcc, droe_C_exp_cgp,
    droe_C_exp_entries_b, droe_C_exp_entries_e, droe_assert_b,
    droe_assert_cap, droe_assert_e, droe_assert_flag, droe_switcher_b,
    droe_switcher_call, droe_switcher_return, droe_switcher_e,
    droe_stack_b, droe_stack_e, droe_trusted_stack_b,
    droe_trusted_stack_e, droe_switcher_otype in H.

(** The concrete adversary follows the outer read-only capability in [ca0],
    reads through the nested capability, and stores the observed word in its
    own data cell before returning. It therefore directly tests whether the
    supposedly deeply immutable value can be observed through the nesting. *)
Definition droe_C_code : list Word :=
  encodeInstrsW [
    Load ct0 ca0;
    Load ct0 ct0;
    Store cgp ct0;
    Jalr cnull cra
  ].

Definition droe_C_data : list Word := [WInt 0].

Definition droe_C_imports : list Word :=
  [WSentry XSRW_ Local droe_switcher_b droe_switcher_e droe_switcher_call].

Definition droe_C_exports : list Word :=
  [WInt (encode_entry_point 1 1)].

Program Definition droe_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    droe_switcher_b droe_switcher_e
    droe_switcher_call droe_switcher_return droe_switcher_otype
    droe_trusted_stack_b droe_trusted_stack_e
    _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl
    droe_stack_b droe_stack_e (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_droe_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition droe_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance
    droe_assert_b droe_assert_e droe_assert_cap droe_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_droe_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance droe_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout droe_concrete_cmptSwitcher).
Defined.

Local Instance droe_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout droe_concrete_cmptAssert).
Defined.

Definition droe_C_f : Sealable :=
  SCap RO Global droe_C_exp_pcc droe_C_exp_entries_e droe_C_exp_entries_b.

Definition droe_main_imports_concrete : list Word :=
  droe_main_imports droe_C_f.

Program Definition droe_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    droe_main_pcc_b droe_main_code_a droe_main_pcc_e
    droe_main_cgp_b droe_main_cgp_e
    droe_main_exp_pcc droe_main_exp_cgp
    droe_main_exp_entries_b droe_main_exp_entries_e
    droe_main_imports_concrete droe_main_code droe_main_data []
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_droe_addresses; disj_regions.
Defined.

Program Definition droe_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    droe_C_pcc_b droe_C_code_a droe_C_pcc_e
    droe_C_cgp_b droe_C_cgp_e
    droe_C_exp_pcc droe_C_exp_cgp
    droe_C_exp_entries_b droe_C_exp_entries_e
    droe_C_imports droe_C_code droe_C_data droe_C_exports
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_droe_addresses; disj_regions.
Defined.

Ltac solve_droe_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, assert_cmpt_disjoint,
       assert_switcher_disjoint, cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
       cmpt_exp_tbl_region, cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmpt_assert_region, cmpt_assert_code_region, cmpt_assert_cap_region,
       cmpt_assert_flag_region, droe_concrete_cmptSwitcher,
       droe_concrete_cmptAssert, droe_concrete_main_cmpt, droe_concrete_C_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end
       b_switcher e_switcher b_trusted_stack e_trusted_stack
       b_stack e_stack b_assert cap_assert e_assert flag_assert];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_droe_addresses_in Hx;
  unfold_droe_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance droe_concrete_layout : memory_layout.
Proof.
  refine (@Build_memory_layout machine_parameters_instance
    droe_concrete_cmptSwitcher droe_concrete_cmptAssert
    droe_concrete_main_cmpt droe_concrete_C_cmpt _ _ _ _).
  - solve_droe_concrete_disjoint.
  - split; solve_droe_concrete_disjoint.
  - split; solve_droe_concrete_disjoint.
  - solve_droe_concrete_disjoint.
Defined.

Definition droe_initial_registers : Reg :=
  <[PC := WCap RX Global droe_main_pcc_b droe_main_pcc_e droe_main_code_a]>
  (<[cgp := WCap RW Global droe_main_cgp_b droe_main_cgp_e droe_main_cgp_b]>
  (<[csp := WCap RWL Local droe_stack_b droe_stack_e droe_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition droe_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local droe_trusted_stack_b droe_trusted_stack_e
      droe_trusted_stack_b]> ∅.

Definition droe_initial_memory : Mem := mk_initial_memory.

Lemma droe_initial_registers_correct :
  is_initial_registers droe_initial_registers.
Proof.
  rewrite /is_initial_registers /droe_initial_registers.
  cbn [droe_concrete_layout droe_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma droe_initial_sregisters_correct :
  is_initial_sregisters droe_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /droe_initial_sregisters.
  cbn [droe_concrete_layout droe_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma droe_initial_memory_correct :
  is_initial_memory droe_initial_memory.
Proof.
  rewrite /is_initial_memory /droe_initial_memory.
  repeat split; try reflexivity.
  - rewrite /droe_C_code /encodeInstrsW;
      repeat constructor; done.
  - rewrite /droe_C_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Lemma droe_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (droe_initial_registers, droe_initial_sregisters, droe_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! droe_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@droe_adequacy machine_parameters_instance droe_concrete_layout
      droe_initial_registers reg'
      droe_initial_sregisters sreg'
      droe_initial_memory mem' es
      droe_initial_registers_correct
      droe_initial_sregisters_correct
      droe_initial_memory_correct Hrun) as Hadequacy.
  cbn [droe_concrete_layout droe_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Fuel 2000 is insufficient for this concrete run; 3000 reaches [Halted]. *)
(** Combining the computed execution with [droe_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem droe_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (droe_initial_registers, droe_initial_sregisters, droe_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! droe_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof
    (machine_run_correct 3000 Executable
      (droe_initial_registers, droe_initial_sregisters, droe_initial_memory)
      Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply droe_concrete_adequacy; exact Hrun.
Qed.
