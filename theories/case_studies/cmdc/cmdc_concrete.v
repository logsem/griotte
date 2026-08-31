From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  cmdc cmdc_adequacy disjoint_regions_tactics.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition cmdc_main_pcc_begin : Addr := A 9.
Definition cmdc_main_code_start : Addr := A 13.
Definition cmdc_main_pcc_end : Addr := A 98.
Definition cmdc_B_pcc_begin : Addr := A 98.
Definition cmdc_B_code_start : Addr := A 99.
Definition cmdc_B_pcc_end : Addr := A 102.
Definition cmdc_C_pcc_begin : Addr := A 102.
Definition cmdc_C_code_start : Addr := A 103.
Definition cmdc_C_pcc_end : Addr := A 105.
Definition cmdc_main_data_begin : Addr := A 105.
Definition cmdc_main_data_end : Addr := A 107.
Definition cmdc_B_data_begin : Addr := A 107.
Definition cmdc_B_data_end : Addr := A 108.
Definition cmdc_C_data_begin : Addr := A 108.
Definition cmdc_C_data_end : Addr := A 109.
Definition cmdc_main_exports_pcc : Addr := A 109.
Definition cmdc_main_exports_cgp : Addr := A 110.
Definition cmdc_main_exports_entries_begin : Addr := A 111.
Definition cmdc_main_exports_entries_end : Addr := A 111.
Definition cmdc_B_exports_pcc : Addr := A 111.
Definition cmdc_B_exports_cgp : Addr := A 112.
Definition cmdc_B_exports_entries_begin : Addr := A 113.
Definition cmdc_B_exports_entries_end : Addr := A 114.
Definition cmdc_C_exports_pcc : Addr := A 114.
Definition cmdc_C_exports_cgp : Addr := A 115.
Definition cmdc_C_exports_entries_begin : Addr := A 116.
Definition cmdc_C_exports_entries_end : Addr := A 117.
Definition cmdc_assert_begin : Addr := A 117.
Definition cmdc_assert_cap : Addr := A 129.
Definition cmdc_assert_end : Addr := A 130.
Definition cmdc_assert_flag : Addr := A 130.
Definition cmdc_switcher_begin : Addr := A 131.
Definition cmdc_switcher_call : Addr := A 132.
Definition cmdc_switcher_return : Addr := A 220.
Definition cmdc_switcher_end : Addr := A 282.
Definition cmdc_switcher_sealing_type : OType := OT 9.
Definition cmdc_trusted_stack_begin : Addr := A 4096.
Definition cmdc_trusted_stack_end : Addr := A 4196.
Definition cmdc_stack_begin : Addr := A 1024.
Definition cmdc_stack_end : Addr := A 1124.

Ltac unfold_cmdc_addresses :=
  unfold cmdc_main_pcc_begin, cmdc_main_code_start, cmdc_main_pcc_end,
    cmdc_B_pcc_begin, cmdc_B_code_start, cmdc_B_pcc_end,
    cmdc_C_pcc_begin, cmdc_C_code_start, cmdc_C_pcc_end,
    cmdc_main_data_begin, cmdc_main_data_end, cmdc_B_data_begin,
    cmdc_B_data_end, cmdc_C_data_begin, cmdc_C_data_end,
    cmdc_main_exports_pcc, cmdc_main_exports_cgp,
    cmdc_main_exports_entries_begin, cmdc_main_exports_entries_end,
    cmdc_B_exports_pcc, cmdc_B_exports_cgp, cmdc_B_exports_entries_begin,
    cmdc_B_exports_entries_end, cmdc_C_exports_pcc, cmdc_C_exports_cgp,
    cmdc_C_exports_entries_begin, cmdc_C_exports_entries_end,
    cmdc_assert_begin, cmdc_assert_cap, cmdc_assert_end, cmdc_assert_flag,
    cmdc_switcher_begin, cmdc_switcher_call, cmdc_switcher_return,
    cmdc_switcher_end, cmdc_switcher_sealing_type,
    cmdc_trusted_stack_begin, cmdc_trusted_stack_end,
    cmdc_stack_begin, cmdc_stack_end.

Ltac unfold_cmdc_addresses_in H :=
  unfold cmdc_main_pcc_begin, cmdc_main_code_start, cmdc_main_pcc_end,
    cmdc_B_pcc_begin, cmdc_B_code_start, cmdc_B_pcc_end,
    cmdc_C_pcc_begin, cmdc_C_code_start, cmdc_C_pcc_end,
    cmdc_main_data_begin, cmdc_main_data_end, cmdc_B_data_begin,
    cmdc_B_data_end, cmdc_C_data_begin, cmdc_C_data_end,
    cmdc_main_exports_pcc, cmdc_main_exports_cgp,
    cmdc_main_exports_entries_begin, cmdc_main_exports_entries_end,
    cmdc_B_exports_pcc, cmdc_B_exports_cgp, cmdc_B_exports_entries_begin,
    cmdc_B_exports_entries_end, cmdc_C_exports_pcc, cmdc_C_exports_cgp,
    cmdc_C_exports_entries_begin, cmdc_C_exports_entries_end,
    cmdc_assert_begin, cmdc_assert_cap, cmdc_assert_end, cmdc_assert_flag,
    cmdc_switcher_begin, cmdc_switcher_call, cmdc_switcher_return,
    cmdc_switcher_end, cmdc_switcher_sealing_type,
    cmdc_trusted_stack_begin, cmdc_trusted_stack_end,
    cmdc_stack_begin, cmdc_stack_end in H.

(** The concrete adversary consists of two unknown compartments. Compartment
    [B] writes [7] through the capability it receives and also saves that
    capability on its stack; compartment [C] writes [9] through its received
    capability. Together they exercise the main program's cross-compartment
    capability discipline. *)
Definition cmdc_B_code : list Word :=
  encodeInstrsW [Store ca0 7%Z; Store csp ca0; Jalr cnull cra].
Definition cmdc_C_code : list Word :=
  encodeInstrsW [Store ca0 9%Z; Jalr cnull cra].
Definition cmdc_B_data : list Word := [WInt 0].
Definition cmdc_C_data : list Word := [WInt 0].
Definition cmdc_B_imports : list Word :=
  [WSentry XSRW_ Local cmdc_switcher_begin cmdc_switcher_end cmdc_switcher_call].
Definition cmdc_C_imports : list Word :=
  [WSentry XSRW_ Local cmdc_switcher_begin cmdc_switcher_end cmdc_switcher_call].
Definition cmdc_B_exports : list Word := [WInt (encode_entry_point 1 1)].
Definition cmdc_C_exports : list Word := [WInt (encode_entry_point 1 1)].

Program Definition cmdc_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    cmdc_switcher_begin cmdc_switcher_end cmdc_switcher_call
    cmdc_switcher_return cmdc_switcher_sealing_type
    cmdc_trusted_stack_begin cmdc_trusted_stack_end _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl cmdc_stack_begin cmdc_stack_end
    (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition cmdc_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance cmdc_assert_begin
    cmdc_assert_end cmdc_assert_cap cmdc_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance cmdc_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout cmdc_concrete_cmptSwitcher).
Defined.

Local Instance cmdc_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout cmdc_concrete_cmptAssert).
Defined.

Definition cmdc_B_f : Sealable :=
  SCap RO Global cmdc_B_exports_pcc cmdc_B_exports_entries_end
    cmdc_B_exports_entries_begin.
Definition cmdc_C_g : Sealable :=
  SCap RO Global cmdc_C_exports_pcc cmdc_C_exports_entries_end
    cmdc_C_exports_entries_begin.
Definition cmdc_main_imports_concrete : list Word :=
  cmdc_main_imports cmdc_B_f cmdc_C_g.

Program Definition cmdc_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt cmdc_main_pcc_begin cmdc_main_code_start cmdc_main_pcc_end
    cmdc_main_data_begin cmdc_main_data_end cmdc_main_exports_pcc
    cmdc_main_exports_cgp cmdc_main_exports_entries_begin
    cmdc_main_exports_entries_end cmdc_main_imports_concrete cmdc_main_code
    cmdc_main_data [] _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_addresses; disj_regions.
Defined.

Program Definition cmdc_concrete_B_cmpt : cmpt.
Proof.
  refine (@mkCmpt cmdc_B_pcc_begin cmdc_B_code_start cmdc_B_pcc_end
    cmdc_B_data_begin cmdc_B_data_end cmdc_B_exports_pcc cmdc_B_exports_cgp
    cmdc_B_exports_entries_begin cmdc_B_exports_entries_end cmdc_B_imports
    cmdc_B_code cmdc_B_data cmdc_B_exports _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_addresses; disj_regions.
Defined.

Program Definition cmdc_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt cmdc_C_pcc_begin cmdc_C_code_start cmdc_C_pcc_end
    cmdc_C_data_begin cmdc_C_data_end cmdc_C_exports_pcc cmdc_C_exports_cgp
    cmdc_C_exports_entries_begin cmdc_C_exports_entries_end cmdc_C_imports
    cmdc_C_code cmdc_C_data cmdc_C_exports _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_addresses; disj_regions.
Defined.

Ltac solve_cmdc_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, assert_cmpt_disjoint,
       assert_switcher_disjoint, cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
       cmpt_exp_tbl_region, cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmpt_assert_region, cmpt_assert_code_region, cmpt_assert_cap_region,
       cmpt_assert_flag_region, cmdc_concrete_cmptSwitcher,
       cmdc_concrete_cmptAssert, cmdc_concrete_main_cmpt,
       cmdc_concrete_B_cmpt, cmdc_concrete_C_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end b_switcher e_switcher
       b_trusted_stack e_trusted_stack b_stack e_stack b_assert cap_assert
       e_assert flag_assert];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_cmdc_addresses_in Hx;
  unfold_cmdc_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance cmdc_concrete_layout : memory_layout.
Proof.
  refine (@Build_memory_layout machine_parameters_instance
    cmdc_concrete_cmptSwitcher cmdc_concrete_cmptAssert
    cmdc_concrete_main_cmpt cmdc_concrete_B_cmpt 1
    cmdc_concrete_C_cmpt 1 _ _ _ _).
  - repeat split; solve_cmdc_concrete_disjoint.
  - repeat split; solve_cmdc_concrete_disjoint.
  - repeat split; solve_cmdc_concrete_disjoint.
  - solve_cmdc_concrete_disjoint.
Defined.

Definition cmdc_initial_registers : Reg :=
  <[PC := WCap RX Global cmdc_main_pcc_begin cmdc_main_pcc_end
      cmdc_main_code_start]>
  (<[cgp := WCap RW Global cmdc_main_data_begin cmdc_main_data_end
      cmdc_main_data_begin]>
  (<[csp := WCap RWL Local cmdc_stack_begin cmdc_stack_end cmdc_stack_begin]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition cmdc_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local cmdc_trusted_stack_begin cmdc_trusted_stack_end
      cmdc_trusted_stack_begin]> ∅.

Definition cmdc_initial_memory : Mem := mk_initial_memory.

Lemma cmdc_initial_registers_correct :
  is_initial_registers cmdc_initial_registers.
Proof.
  rewrite /is_initial_registers /cmdc_initial_registers.
  cbn [cmdc_concrete_layout cmdc_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma cmdc_initial_sregisters_correct :
  is_initial_sregisters cmdc_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /cmdc_initial_sregisters.
  cbn [cmdc_concrete_layout cmdc_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma cmdc_initial_memory_correct :
  is_initial_memory cmdc_initial_memory.
Proof.
  rewrite /is_initial_memory /cmdc_initial_memory.
  repeat split; try reflexivity.
  - rewrite /cmdc_B_code /encodeInstrsW; repeat constructor; done.
  - rewrite /cmdc_B_data; repeat constructor; done.
  - rewrite /cmdc_C_code /encodeInstrsW; repeat constructor; done.
  - rewrite /cmdc_C_data; repeat constructor; done.
Qed.

Theorem cmdc_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (cmdc_initial_registers, cmdc_initial_sregisters, cmdc_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! cmdc_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@cmdc_adequacy machine_parameters_instance cmdc_concrete_layout
      cmdc_initial_registers reg' cmdc_initial_sregisters sreg'
      cmdc_initial_memory mem' es cmdc_initial_registers_correct
      cmdc_initial_sregisters_correct cmdc_initial_memory_correct Hrun)
    as Hadequacy.
  cbn [cmdc_concrete_layout cmdc_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Combining the computed execution with [cmdc_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem cmdc_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (cmdc_initial_registers, cmdc_initial_sregisters,
         cmdc_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! cmdc_assert_flag = Some (WInt 0%Z).
Proof.
  edestruct (
    machine_run_correct 10000 Executable
      (cmdc_initial_registers, cmdc_initial_sregisters,
       cmdc_initial_memory)
      Halted
  ) as [[[reg' sreg'] mem'] Hsteps].
  { vm_compute; reflexivity. }
  exists reg', sreg', mem'. split.
  - exact Hsteps.
  - eapply cmdc_concrete_adequacy. exact Hsteps.
Qed.
