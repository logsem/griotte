From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  vae vae_adequacy disjoint_regions_tactics.

Existing Instance machine_parameters_instance.
Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition vae_main_pcc_begin : Addr := A 9.
Definition vae_main_code_start : Addr := A 12.
Definition vae_main_pcc_end : Addr := A 84.
Definition vae_C_pcc_begin : Addr := A 84.
Definition vae_C_code_start : Addr := A 87.
Definition vae_C_pcc_end : Addr := A 152.
Definition vae_main_data_begin : Addr := A 152.
Definition vae_main_data_end : Addr := A 153.
Definition vae_C_data_begin : Addr := A 153.
Definition vae_C_data_end : Addr := A 154.
Definition vae_main_exports_pcc : Addr := A 154.
Definition vae_main_exports_cgp : Addr := A 155.
Definition vae_main_exports_entries_begin : Addr := A 156.
Definition vae_main_exports_entries_end : Addr := A 157.
Definition vae_C_exports_pcc : Addr := A 157.
Definition vae_C_exports_cgp : Addr := A 158.
Definition vae_C_exports_entries_begin : Addr := A 159.
Definition vae_C_exports_entries_end : Addr := A 161.
Definition vae_assert_begin : Addr := A 161.
Definition vae_assert_cap : Addr := A 173.
Definition vae_assert_end : Addr := A 174.
Definition vae_assert_flag : Addr := A 174.
Definition vae_switcher_begin : Addr := A 175.
Definition vae_switcher_call : Addr := A 176.
Definition vae_switcher_return : Addr := A 264.
Definition vae_switcher_end : Addr := A 326.
Definition vae_switcher_sealing_type : OType := OT 9.
Definition vae_trusted_stack_begin : Addr := A 4096.
Definition vae_trusted_stack_end : Addr := A 4196.
Definition vae_stack_begin : Addr := A 1024.
Definition vae_stack_end : Addr := A 1124.

Ltac unfold_vae_addresses :=
  unfold vae_main_pcc_begin, vae_main_code_start, vae_main_pcc_end,
    vae_C_pcc_begin, vae_C_code_start, vae_C_pcc_end,
    vae_main_data_begin, vae_main_data_end, vae_C_data_begin, vae_C_data_end,
    vae_main_exports_pcc, vae_main_exports_cgp,
    vae_main_exports_entries_begin, vae_main_exports_entries_end,
    vae_C_exports_pcc, vae_C_exports_cgp,
    vae_C_exports_entries_begin, vae_C_exports_entries_end,
    vae_assert_begin, vae_assert_cap, vae_assert_end, vae_assert_flag,
    vae_switcher_begin, vae_switcher_call, vae_switcher_return,
    vae_switcher_end, vae_switcher_sealing_type,
    vae_trusted_stack_begin, vae_trusted_stack_end,
    vae_stack_begin, vae_stack_end.

Ltac unfold_vae_addresses_in H :=
  unfold vae_main_pcc_begin, vae_main_code_start, vae_main_pcc_end,
    vae_C_pcc_begin, vae_C_code_start, vae_C_pcc_end,
    vae_main_data_begin, vae_main_data_end, vae_C_data_begin, vae_C_data_end,
    vae_main_exports_pcc, vae_main_exports_cgp,
    vae_main_exports_entries_begin, vae_main_exports_entries_end,
    vae_C_exports_pcc, vae_C_exports_cgp,
    vae_C_exports_entries_begin, vae_C_exports_entries_end,
    vae_assert_begin, vae_assert_cap, vae_assert_end, vae_assert_flag,
    vae_switcher_begin, vae_switcher_call, vae_switcher_return,
    vae_switcher_end, vae_switcher_sealing_type,
    vae_trusted_stack_begin, vae_trusted_stack_end,
    vae_stack_begin, vae_stack_end in H.

Definition vae_C_load (dst src : RegName) : instr.
Proof.
  constructor 5.
  - exact dst.
  - exact src.
Defined.

(** The concrete adversary's first entry calls [awkward] with its second entry
    [g]. The callback [g] uses the adversary data cell as a one-shot flag: on
    its first invocation it sets the flag and makes one nested call to
    [awkward], while later invocations return immediately. Both entries save
    and restore their outer return capabilities around nested calls. *)
Definition vae_C_code : list Word :=
  encodeInstrsW [
    Store csp cra; Lea csp 1%Z;
    Mov ct0 PC; GetB cs0 ct0; GetA cs1 ct0; Sub cs0 cs0 cs1;
    Lea ct0 cs0; Lea ct0 0%Z; vae_C_load ct0 ct0; Mov cs0 0%Z;
    Mov ct1 PC; GetB cs0 ct1; GetA cs1 ct1; Sub cs0 cs0 cs1;
    Lea ct1 cs0; Lea ct1 1%Z; vae_C_load ct1 ct1; Mov cs0 0%Z;
    Mov ca0 PC; GetB cs0 ca0; GetA cs1 ca0; Sub cs0 cs0 cs1;
    Lea ca0 cs0; Lea ca0 2%Z; vae_C_load ca0 ca0; Mov cs0 0%Z;
    Jalr cra ct0;
    Lea csp (-1)%Z; vae_C_load cra csp; Mov ca0 0%Z; Jalr cnull cra;

    vae_C_load ct0 cgp; Jnz 31%Z ct0; Store cgp 1%Z;
    Store csp cra; Lea csp 1%Z;
    Mov ct0 PC; GetB cs0 ct0; GetA cs1 ct0; Sub cs0 cs0 cs1;
    Lea ct0 cs0; Lea ct0 0%Z; vae_C_load ct0 ct0; Mov cs0 0%Z;
    Mov ct1 PC; GetB cs0 ct1; GetA cs1 ct1; Sub cs0 cs0 cs1;
    Lea ct1 cs0; Lea ct1 1%Z; vae_C_load ct1 ct1; Mov cs0 0%Z;
    Mov ca0 PC; GetB cs0 ca0; GetA cs1 ca0; Sub cs0 cs0 cs1;
    Lea ca0 cs0; Lea ca0 2%Z; vae_C_load ca0 ca0; Mov cs0 0%Z;
    Jalr cra ct0;
    Lea csp (-1)%Z; vae_C_load cra csp;
    Mov ca0 0%Z; Jalr cnull cra
  ].

Definition vae_C_data : list Word := [WInt 0].

Program Definition vae_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    vae_switcher_begin vae_switcher_end
    vae_switcher_call vae_switcher_return vae_switcher_sealing_type
    vae_trusted_stack_begin vae_trusted_stack_end
    _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl
    vae_stack_begin vae_stack_end (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_vae_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition vae_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance
    vae_assert_begin vae_assert_end vae_assert_cap vae_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_vae_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance vae_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout vae_concrete_cmptSwitcher).
Defined.

Local Instance vae_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout vae_concrete_cmptAssert).
Defined.

Definition vae_C_f : Sealable :=
  SCap RO Global vae_C_exports_pcc vae_C_exports_entries_end
    vae_C_exports_entries_begin.

Definition vae_C_g : Sealable :=
  SCap RO Global vae_C_exports_pcc vae_C_exports_entries_end
    (vae_C_exports_entries_begin ^+ 1)%a.

Definition vae_main_imports_concrete : list Word := vae_main_imports vae_C_f.

Definition vae_C_imports : list Word :=
  [ WSentry XSRW_ Local vae_switcher_begin vae_switcher_end vae_switcher_call
  ; WSealed vae_switcher_sealing_type
      (vae_entry_awkward_sb vae_main_exports_pcc vae_main_exports_entries_end)
  ; WSealed vae_switcher_sealing_type vae_C_g
  ].

Definition vae_C_exports : list Word :=
  [WInt (encode_entry_point 0 3); WInt (encode_entry_point 0 34)].

Program Definition vae_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    vae_main_pcc_begin vae_main_code_start vae_main_pcc_end
    vae_main_data_begin vae_main_data_end
    vae_main_exports_pcc vae_main_exports_cgp
    vae_main_exports_entries_begin vae_main_exports_entries_end
    vae_main_imports_concrete vae_main_code vae_main_data vae_export_table_entries
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_vae_addresses; disj_regions.
Defined.

Program Definition vae_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    vae_C_pcc_begin vae_C_code_start vae_C_pcc_end
    vae_C_data_begin vae_C_data_end
    vae_C_exports_pcc vae_C_exports_cgp
    vae_C_exports_entries_begin vae_C_exports_entries_end
    vae_C_imports vae_C_code vae_C_data vae_C_exports
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_vae_addresses; disj_regions.
Defined.

Ltac solve_vae_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, assert_cmpt_disjoint,
       assert_switcher_disjoint, cmpt_region, cmpt_pcc_region, cmpt_cgp_region,
       cmpt_exp_tbl_region, cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmpt_assert_region, cmpt_assert_code_region, cmpt_assert_cap_region,
       cmpt_assert_flag_region, vae_concrete_cmptSwitcher,
       vae_concrete_cmptAssert, vae_concrete_main_cmpt, vae_concrete_C_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end
       b_switcher e_switcher b_trusted_stack e_trusted_stack
       b_stack e_stack b_assert cap_assert e_assert flag_assert];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_vae_addresses_in Hx;
  unfold_vae_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance vae_concrete_layout : memory_layout.
Proof.
  refine (@Build_memory_layout machine_parameters_instance
    vae_concrete_cmptSwitcher vae_concrete_cmptAssert
    vae_concrete_main_cmpt vae_concrete_C_cmpt 3 34 _ _ _ _).
  - solve_vae_concrete_disjoint.
  - split; solve_vae_concrete_disjoint.
  - split; solve_vae_concrete_disjoint.
  - solve_vae_concrete_disjoint.
Defined.

Definition vae_initial_registers : Reg :=
  <[PC := WCap RX Global vae_main_pcc_begin vae_main_pcc_end vae_main_code_start]>
  (<[cgp := WCap RW Global vae_main_data_begin vae_main_data_end
      vae_main_data_begin]>
  (<[csp := WCap RWL Local vae_stack_begin vae_stack_end vae_stack_begin]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition vae_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local vae_trusted_stack_begin vae_trusted_stack_end
      vae_trusted_stack_begin]> ∅.

Definition vae_initial_memory : Mem := mk_initial_memory.

Lemma vae_initial_registers_correct :
  is_initial_registers vae_initial_registers.
Proof.
  rewrite /is_initial_registers /vae_initial_registers.
  cbn [vae_concrete_layout vae_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma vae_initial_sregisters_correct :
  is_initial_sregisters vae_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /vae_initial_sregisters.
  cbn [vae_concrete_layout vae_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma vae_initial_memory_correct : is_initial_memory vae_initial_memory.
Proof.
  rewrite /is_initial_memory /vae_initial_memory.
  repeat split; try reflexivity.
  - rewrite /vae_C_code /encodeInstrsW; repeat constructor; done.
  - rewrite /vae_C_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Theorem vae_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (vae_initial_registers, vae_initial_sregisters, vae_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! vae_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@vae_adequacy machine_parameters_instance vae_concrete_layout
      vae_initial_registers reg' vae_initial_sregisters sreg'
      vae_initial_memory mem' es
      vae_initial_registers_correct vae_initial_sregisters_correct
      vae_initial_memory_correct Hrun) as Hadequacy.
  cbn [vae_concrete_layout vae_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Combining the computed execution with [vae_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem vae_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (vae_initial_registers, vae_initial_sregisters, vae_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! vae_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof
    (machine_run_correct 15000 Executable
      (vae_initial_registers, vae_initial_sregisters, vae_initial_memory)
      Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply vae_concrete_adequacy; exact Hrun.
Qed.
