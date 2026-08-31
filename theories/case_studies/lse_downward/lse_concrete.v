From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  lse lse_adequacy disjoint_regions_tactics.

Existing Instance machine_parameters_instance.
Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition lse_main_pcc_begin : Addr := A 9.
Definition lse_main_code_start : Addr := A 12.
Definition lse_main_pcc_end : Addr := A 56.
Definition lse_C_pcc_begin : Addr := A 56.
Definition lse_C_code_start : Addr := A 58.
Definition lse_C_pcc_end : Addr := A 99.
Definition lse_main_data_begin : Addr := A 99.
Definition lse_main_data_end : Addr := A 100.
Definition lse_C_data_begin : Addr := A 100.
Definition lse_C_data_end : Addr := A 101.
Definition lse_main_exports_pcc : Addr := A 101.
Definition lse_main_exports_cgp : Addr := A 102.
Definition lse_main_exports_entries_begin : Addr := A 103.
Definition lse_main_exports_entries_end : Addr := A 104.
Definition lse_C_exports_pcc : Addr := A 104.
Definition lse_C_exports_cgp : Addr := A 105.
Definition lse_C_exports_entries_begin : Addr := A 106.
Definition lse_C_exports_entries_end : Addr := A 107.
Definition lse_assert_begin : Addr := A 107.
Definition lse_assert_cap : Addr := A 119.
Definition lse_assert_end : Addr := A 120.
Definition lse_assert_flag : Addr := A 120.
Definition lse_switcher_begin : Addr := A 121.
Definition lse_switcher_call : Addr := A 122.
Definition lse_switcher_return : Addr := A 210.
Definition lse_switcher_end : Addr := A 272.
Definition lse_switcher_sealing_type : OType := OT 9.
Definition lse_trusted_stack_begin : Addr := A 4096.
Definition lse_trusted_stack_end : Addr := A 4196.
Definition lse_stack_begin : Addr := A 1024.
Definition lse_stack_end : Addr := A 1124.

Ltac unfold_lse_addresses :=
  unfold lse_main_pcc_begin, lse_main_code_start, lse_main_pcc_end,
    lse_C_pcc_begin, lse_C_code_start, lse_C_pcc_end,
    lse_main_data_begin, lse_main_data_end, lse_C_data_begin, lse_C_data_end,
    lse_main_exports_pcc, lse_main_exports_cgp,
    lse_main_exports_entries_begin, lse_main_exports_entries_end,
    lse_C_exports_pcc, lse_C_exports_cgp,
    lse_C_exports_entries_begin, lse_C_exports_entries_end,
    lse_assert_begin, lse_assert_cap, lse_assert_end, lse_assert_flag,
    lse_switcher_begin, lse_switcher_call, lse_switcher_return,
    lse_switcher_end, lse_switcher_sealing_type,
    lse_trusted_stack_begin, lse_trusted_stack_end,
    lse_stack_begin, lse_stack_end.

Ltac unfold_lse_addresses_in H :=
  unfold lse_main_pcc_begin, lse_main_code_start, lse_main_pcc_end,
    lse_C_pcc_begin, lse_C_code_start, lse_C_pcc_end,
    lse_main_data_begin, lse_main_data_end, lse_C_data_begin, lse_C_data_end,
    lse_main_exports_pcc, lse_main_exports_cgp,
    lse_main_exports_entries_begin, lse_main_exports_entries_end,
    lse_C_exports_pcc, lse_C_exports_cgp,
    lse_C_exports_entries_begin, lse_C_exports_entries_end,
    lse_assert_begin, lse_assert_cap, lse_assert_end, lse_assert_flag,
    lse_switcher_begin, lse_switcher_call, lse_switcher_return,
    lse_switcher_end, lse_switcher_sealing_type,
    lse_trusted_stack_begin, lse_trusted_stack_end,
    lse_stack_begin, lse_stack_end in H.

Definition lse_C_load (dst src : RegName) : instr.
Proof.
  constructor 5.
  - exact dst.
  - exact src.
Defined.

(** The concrete adversary saves its outer return capability, fetches the
    switcher and the exported main function, and calls the function twice. It
    deliberately fetches both imports again before the second call, then
    restores its return capability and returns to the caller. *)
Definition lse_C_code : list Word :=
  encodeInstrsW [
    Store csp cra; Lea csp 1%Z;

    Mov ct0 PC; GetB cs0 ct0; GetA cs1 ct0; Sub cs0 cs0 cs1;
    Lea ct0 cs0; Lea ct0 0%Z; lse_C_load ct0 ct0; Mov cs0 0%Z;
    Mov ct1 PC; GetB cs0 ct1; GetA cs1 ct1; Sub cs0 cs0 cs1;
    Lea ct1 cs0; Lea ct1 1%Z; lse_C_load ct1 ct1; Mov cs0 0%Z;
    Jalr cra ct0;

    Mov ct0 PC; GetB cs0 ct0; GetA cs1 ct0; Sub cs0 cs0 cs1;
    Lea ct0 cs0; Lea ct0 0%Z; lse_C_load ct0 ct0; Mov cs0 0%Z;
    Mov ct1 PC; GetB cs0 ct1; GetA cs1 ct1; Sub cs0 cs0 cs1;
    Lea ct1 cs0; Lea ct1 1%Z; lse_C_load ct1 ct1; Mov cs0 0%Z;
    Jalr cra ct0;

    Lea csp (-1)%Z; lse_C_load cra csp;
    Mov ca0 0%Z; Mov ca1 0%Z; Jalr cnull cra
  ].

Definition lse_C_data : list Word := [WInt 0].

Program Definition lse_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    lse_switcher_begin lse_switcher_end
    lse_switcher_call lse_switcher_return lse_switcher_sealing_type
    lse_trusted_stack_begin lse_trusted_stack_end
    _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl
    lse_stack_begin lse_stack_end (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_lse_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition lse_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance
    lse_assert_begin lse_assert_end lse_assert_cap lse_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_lse_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance lse_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout lse_concrete_cmptSwitcher).
Defined.

Local Instance lse_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout lse_concrete_cmptAssert).
Defined.

Definition lse_C_f : Sealable :=
  SCap RO Global lse_C_exports_pcc lse_C_exports_entries_end
    lse_C_exports_entries_begin.

Definition lse_main_imports_concrete : list Word := lse_main_imports lse_C_f.

Definition lse_C_imports : list Word :=
  [ WSentry XSRW_ Local lse_switcher_begin lse_switcher_end lse_switcher_call
  ; WSealed lse_switcher_sealing_type
      (lse_entry_f_sb lse_main_exports_pcc lse_main_exports_entries_end)
  ].

Definition lse_C_exports : list Word := [WInt (encode_entry_point 0 2)].

Program Definition lse_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    lse_main_pcc_begin lse_main_code_start lse_main_pcc_end
    lse_main_data_begin lse_main_data_end
    lse_main_exports_pcc lse_main_exports_cgp
    lse_main_exports_entries_begin lse_main_exports_entries_end
    lse_main_imports_concrete lse_main_code lse_main_data lse_export_table_entries
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_lse_addresses; disj_regions.
Defined.

Program Definition lse_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    lse_C_pcc_begin lse_C_code_start lse_C_pcc_end
    lse_C_data_begin lse_C_data_end
    lse_C_exports_pcc lse_C_exports_cgp
    lse_C_exports_entries_begin lse_C_exports_entries_end
    lse_C_imports lse_C_code lse_C_data lse_C_exports
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_lse_addresses; disj_regions.
Defined.

Ltac solve_lse_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, assert_cmpt_disjoint,
       assert_switcher_disjoint, cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
       cmpt_exp_tbl_region, cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmpt_assert_region, cmpt_assert_code_region, cmpt_assert_cap_region,
       cmpt_assert_flag_region, lse_concrete_cmptSwitcher,
       lse_concrete_cmptAssert, lse_concrete_main_cmpt, lse_concrete_C_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end
       b_switcher e_switcher b_trusted_stack e_trusted_stack
       b_stack e_stack b_assert cap_assert e_assert flag_assert];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_lse_addresses_in Hx;
  unfold_lse_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance lse_concrete_layout : memory_layout.
Proof.
  refine (@Build_memory_layout machine_parameters_instance
    lse_concrete_cmptSwitcher lse_concrete_cmptAssert
    lse_concrete_main_cmpt lse_concrete_C_cmpt 2 _ _ _ _).
  - solve_lse_concrete_disjoint.
  - split; solve_lse_concrete_disjoint.
  - split; solve_lse_concrete_disjoint.
  - solve_lse_concrete_disjoint.
Defined.

Definition lse_initial_registers : Reg :=
  <[PC := WCap RX Global lse_main_pcc_begin lse_main_pcc_end lse_main_code_start]>
  (<[cgp := WCap RW Global lse_main_data_begin lse_main_data_end
      lse_main_data_begin]>
  (<[csp := WCap RWL Local lse_stack_begin lse_stack_end lse_stack_begin]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition lse_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local lse_trusted_stack_begin lse_trusted_stack_end
      lse_trusted_stack_begin]> ∅.

Definition lse_initial_memory : Mem := mk_initial_memory.

Lemma lse_initial_registers_correct :
  is_initial_registers lse_initial_registers.
Proof.
  rewrite /is_initial_registers /lse_initial_registers.
  cbn [lse_concrete_layout lse_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma lse_initial_sregisters_correct :
  is_initial_sregisters lse_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /lse_initial_sregisters.
  cbn [lse_concrete_layout lse_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma lse_initial_memory_correct : is_initial_memory lse_initial_memory.
Proof.
  rewrite /is_initial_memory /lse_initial_memory.
  repeat split; try reflexivity.
  - rewrite /lse_C_code /encodeInstrsW; repeat constructor; done.
  - rewrite /lse_C_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Theorem lse_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (lse_initial_registers, lse_initial_sregisters, lse_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! lse_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@lse_adequacy machine_parameters_instance lse_concrete_layout
      lse_initial_registers reg' lse_initial_sregisters sreg'
      lse_initial_memory mem' es
      lse_initial_registers_correct lse_initial_sregisters_correct
      lse_initial_memory_correct Hrun) as Hadequacy.
  cbn [lse_concrete_layout lse_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Combining the computed execution with [lse_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem lse_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (lse_initial_registers, lse_initial_sregisters, lse_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! lse_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof
    (machine_run_correct 7500 Executable
      (lse_initial_registers, lse_initial_sregisters, lse_initial_memory)
      Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply lse_concrete_adequacy; exact Hrun.
Qed.
