From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  stack_object stack_object_adequacy disjoint_regions_tactics.

Existing Instance machine_parameters_instance.
Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition so_main_pcc_b : Addr := A 9.
Definition so_main_code_start : Addr := A 12.
Definition so_main_pcc_e : Addr := A 160.
Definition so_C_pcc_b : Addr := A 160.
Definition so_C_code_start : Addr := A 163.
Definition so_C_pcc_e : Addr := A 204.
Definition so_main_data_b : Addr := A 204.
Definition so_main_data_e : Addr := A 204.
Definition so_C_data_b : Addr := A 204.
Definition so_C_data_e : Addr := A 205.
Definition so_main_exports_pcc : Addr := A 205.
Definition so_main_exports_cgp : Addr := A 206.
Definition so_main_exports_entries_b : Addr := A 207.
Definition so_main_exports_entries_e : Addr := A 208.
Definition so_C_exports_pcc : Addr := A 208.
Definition so_C_exports_cgp : Addr := A 209.
Definition so_C_exports_entries_b : Addr := A 210.
Definition so_C_exports_entries_e : Addr := A 212.
Definition so_assert_b : Addr := A 212.
Definition so_assert_cap : Addr := A 224.
Definition so_assert_e : Addr := A 225.
Definition so_assert_flag : Addr := A 225.
Definition so_switcher_b : Addr := A 226.
Definition so_switcher_call : Addr := A 227.
Definition so_switcher_return : Addr := A 315.
Definition so_switcher_e : Addr := A 377.
Definition so_switcher_sealing_type : OType := OT 9.
Definition so_trusted_stack_b : Addr := A 4096.
Definition so_trusted_stack_e : Addr := A 4196.
Definition so_stack_b : Addr := A 1024.
Definition so_stack_e : Addr := A 1124.

Ltac unfold_so_addresses :=
  unfold so_main_pcc_b, so_main_code_start, so_main_pcc_e,
    so_C_pcc_b, so_C_code_start, so_C_pcc_e,
    so_main_data_b, so_main_data_e, so_C_data_b, so_C_data_e,
    so_main_exports_pcc, so_main_exports_cgp,
    so_main_exports_entries_b, so_main_exports_entries_e,
    so_C_exports_pcc, so_C_exports_cgp,
    so_C_exports_entries_b, so_C_exports_entries_e,
    so_assert_b, so_assert_cap, so_assert_e, so_assert_flag,
    so_switcher_b, so_switcher_call, so_switcher_return,
    so_switcher_e, so_switcher_sealing_type,
    so_trusted_stack_b, so_trusted_stack_e,
    so_stack_b, so_stack_e.

Ltac unfold_so_addresses_in H :=
  unfold so_main_pcc_b, so_main_code_start, so_main_pcc_e,
    so_C_pcc_b, so_C_code_start, so_C_pcc_e,
    so_main_data_b, so_main_data_e, so_C_data_b, so_C_data_e,
    so_main_exports_pcc, so_main_exports_cgp,
    so_main_exports_entries_b, so_main_exports_entries_e,
    so_C_exports_pcc, so_C_exports_cgp,
    so_C_exports_entries_b, so_C_exports_entries_e,
    so_assert_b, so_assert_cap, so_assert_e, so_assert_flag,
    so_switcher_b, so_switcher_call, so_switcher_return,
    so_switcher_e, so_switcher_sealing_type,
    so_trusted_stack_b, so_trusted_stack_e,
    so_stack_b, so_stack_e in H.

(** The concrete adversary allocates and initializes a one-word public object
    on its stack, then calls the main function with that object and callback
    [g]. The main function allocates a second public stack object and passes
    both capabilities to [g], which attempts to overwrite them with [7] and
    [9]. After the call, the adversary restores its stack and return capability
    before returning to the main program. *)
Definition so_C_code : list Word :=
  encodeInstrsW [
    Store csp cra;
    Lea csp 1%Z;
    Mov ca0 csp;
    GetA cs0 ca0;
    machine_instructions.Add cs1 cs0 1%Z;
    Subseg ca0 cs0 cs1;
    Store ca0 0%Z;
    Lea csp 1%Z;
    Mov ctp PC;
    GetB cs0 ctp;
    GetA cs1 ctp;
    Sub cs0 cs0 cs1;
    Lea ctp cs0;
    Mov ct0 ctp;
    Lea ct0 0%Z;
    Load ct0 ct0;
    Mov ct1 ctp;
    Lea ct1 1%Z;
    Load ct1 ct1;
    Mov ca1 ctp;
    Lea ca1 2%Z;
    Load ca1 ca1;
    Mov cs0 0%Z;
    Mov cs1 0%Z;
    Mov cs0 cra;
    Mov cs1 ct1;
    Jalr cra ct0;
    Lea csp (-1)%Z;
    Lea csp (-1)%Z;
    Load cra csp;
    Mov ca0 0%Z;
    Mov ca1 0%Z;
    Mov ct0 0%Z;
    Mov ct1 0%Z;
    Mov cs0 0%Z;
    Mov cs1 0%Z;
    Jalr cnull cra;
    Lea ca0 (-1)%Z;
    Store ca0 7%Z;
    Store ca1 9%Z;
    Jalr cnull cra
  ].

Definition so_C_data : list Word := [WInt 0].

Program Definition so_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    so_switcher_b so_switcher_e so_switcher_call so_switcher_return
    so_switcher_sealing_type so_trusted_stack_b so_trusted_stack_e
    _ _ _ _ (replicate 100 (WInt 0)) _ eq_refl
    so_stack_b so_stack_e (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_so_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx'; solve_addr.
Defined.

Program Definition so_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance
    so_assert_b so_assert_e so_assert_cap so_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_so_addresses; unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'. rewrite !elem_of_finz_seq_between in Hx, Hx'. solve_addr.
Defined.

Local Instance so_concrete_switcherLayout : switcherLayout.
Proof. exact (cmptSwitcher_switcherLayout so_concrete_cmptSwitcher). Defined.

Local Instance so_concrete_assertLayout : assertLayout.
Proof. exact (cmptAssert_assertLayout so_concrete_cmptAssert). Defined.

Definition so_C_f : Sealable :=
  SCap RO Global so_C_exports_pcc so_C_exports_entries_e
    so_C_exports_entries_b.
Definition so_C_g : Sealable :=
  SCap RO Global so_C_exports_pcc so_C_exports_entries_e
    (so_C_exports_entries_b ^+ 1)%a.
Definition so_main_imports_concrete : list Word := so_main_imports so_C_f.
Definition so_C_imports : list Word :=
  [ WSentry XSRW_ Local so_switcher_b so_switcher_e so_switcher_call
  ; WSealed so_switcher_sealing_type
      (so_entry_f_sb so_main_exports_pcc so_main_exports_entries_e)
  ; WSealed so_switcher_sealing_type so_C_g
  ].
Definition so_C_exports : list Word :=
  [WInt (encode_entry_point 0 3); WInt (encode_entry_point 2 40)].

Program Definition so_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt so_main_pcc_b so_main_code_start so_main_pcc_e
    so_main_data_b so_main_data_e so_main_data_e so_main_data_e
    so_main_exports_pcc so_main_exports_cgp
    so_main_exports_entries_b so_main_exports_entries_e
    so_main_imports_concrete so_main_code so_main_data [] so_export_table_entries
    _ _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_so_addresses; disj_regions.
Defined.

Program Definition so_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt so_C_pcc_b so_C_code_start so_C_pcc_e
    so_C_data_b so_C_data_e so_C_data_e so_C_data_e
    so_C_exports_pcc so_C_exports_cgp
    so_C_exports_entries_b so_C_exports_entries_e
    so_C_imports so_C_code so_C_data [] so_C_exports _ _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_so_addresses; disj_regions.
Defined.

(** All nonempty concrete regions, in increasing address order. The empty
    main data region and both empty static-sealed ranges are omitted. *)
Definition so_concrete_region_partition : list (list Addr) :=
  [ finz.seq_between so_main_pcc_b so_main_pcc_e;
    finz.seq_between so_C_pcc_b so_C_pcc_e;
    finz.seq_between so_C_data_b so_C_data_e;
    finz.seq_between so_main_exports_pcc so_main_exports_entries_e;
    finz.seq_between so_C_exports_pcc so_C_exports_entries_e;
    finz.seq_between so_assert_b so_assert_cap;
    finz.seq_between so_assert_cap so_assert_e;
    finz.seq_between so_assert_flag (so_assert_flag ^+ 1)%a;
    finz.seq_between so_switcher_b so_switcher_e;
    finz.seq_between so_stack_b so_stack_e;
    finz.seq_between so_trusted_stack_b so_trusted_stack_e
  ].

Lemma so_concrete_region_partition_disjoint :
  ## so_concrete_region_partition.
Proof.
  rewrite /so_concrete_region_partition.
  unfold_so_addresses.
  disj_regions.
Qed.

Local Lemma so_main_data_region_empty :
  finz.seq_between so_main_data_b so_main_data_e = [].
Proof.
  apply finz_seq_between_empty.
  unfold_so_addresses; solve_addr.
Qed.

Local Lemma so_C_static_region_empty :
  finz.seq_between so_C_data_e so_C_data_e = [].
Proof.
  apply finz_seq_between_empty.
  unfold_so_addresses; solve_addr.
Qed.

Local Lemma so_concrete_cmpts_disjoints :
  so_concrete_main_cmpt ## so_concrete_C_cmpt.
Proof.
  change
    ((finz.seq_between so_main_pcc_b so_main_pcc_e ∪
      finz.seq_between so_main_data_b so_main_data_e ∪
      finz.seq_between so_main_data_e so_main_data_e ∪
      finz.seq_between so_main_exports_pcc so_main_exports_entries_e) ##
     (finz.seq_between so_C_pcc_b so_C_pcc_e ∪
      finz.seq_between so_C_data_b so_C_data_e ∪
      finz.seq_between so_C_data_e so_C_data_e ∪
      finz.seq_between so_C_exports_pcc so_C_exports_entries_e)).
  pose proof so_concrete_region_partition_disjoint as Hpartition.
  rewrite so_main_data_region_empty so_C_static_region_empty.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint so_concrete_region_partition Hpartition.
Qed.

Local Lemma so_concrete_switcher_cmpt_disjoints :
  switcher_cmpt_disjoint so_concrete_main_cmpt so_concrete_cmptSwitcher
  ∧ switcher_cmpt_disjoint so_concrete_C_cmpt so_concrete_cmptSwitcher.
Proof.
  change
    ((finz.seq_between so_switcher_b so_switcher_e ∪
      finz.seq_between so_trusted_stack_b so_trusted_stack_e ∪
      finz.seq_between so_stack_b so_stack_e) ##
     (finz.seq_between so_main_pcc_b so_main_pcc_e ∪
      finz.seq_between so_main_data_b so_main_data_e ∪
      finz.seq_between so_main_data_e so_main_data_e ∪
      finz.seq_between so_main_exports_pcc so_main_exports_entries_e) /\
     (finz.seq_between so_switcher_b so_switcher_e ∪
      finz.seq_between so_trusted_stack_b so_trusted_stack_e ∪
      finz.seq_between so_stack_b so_stack_e) ##
     (finz.seq_between so_C_pcc_b so_C_pcc_e ∪
      finz.seq_between so_C_data_b so_C_data_e ∪
      finz.seq_between so_C_data_e so_C_data_e ∪
      finz.seq_between so_C_exports_pcc so_C_exports_entries_e)).
  pose proof so_concrete_region_partition_disjoint as Hpartition.
  rewrite so_main_data_region_empty so_C_static_region_empty.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint so_concrete_region_partition Hpartition.
Qed.

Local Lemma so_concrete_assert_cmpt_disjoints :
  assert_cmpt_disjoint so_concrete_main_cmpt so_concrete_cmptAssert
  ∧ assert_cmpt_disjoint so_concrete_C_cmpt so_concrete_cmptAssert.
Proof.
  change
    ((finz.seq_between so_assert_b so_assert_cap ∪
      finz.seq_between so_assert_cap so_assert_e ∪
      finz.seq_between so_assert_flag (so_assert_flag ^+ 1)%a) ##
     (finz.seq_between so_main_pcc_b so_main_pcc_e ∪
      finz.seq_between so_main_data_b so_main_data_e ∪
      finz.seq_between so_main_data_e so_main_data_e ∪
      finz.seq_between so_main_exports_pcc so_main_exports_entries_e) /\
     (finz.seq_between so_assert_b so_assert_cap ∪
      finz.seq_between so_assert_cap so_assert_e ∪
      finz.seq_between so_assert_flag (so_assert_flag ^+ 1)%a) ##
     (finz.seq_between so_C_pcc_b so_C_pcc_e ∪
      finz.seq_between so_C_data_b so_C_data_e ∪
      finz.seq_between so_C_data_e so_C_data_e ∪
      finz.seq_between so_C_exports_pcc so_C_exports_entries_e)).
  pose proof so_concrete_region_partition_disjoint as Hpartition.
  rewrite so_main_data_region_empty so_C_static_region_empty.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint so_concrete_region_partition Hpartition.
Qed.

Local Lemma so_concrete_assert_switcher_disjoints :
  assert_switcher_disjoint so_concrete_cmptAssert so_concrete_cmptSwitcher.
Proof.
  change
    ((finz.seq_between so_assert_b so_assert_cap ∪
      finz.seq_between so_assert_cap so_assert_e ∪
      finz.seq_between so_assert_flag (so_assert_flag ^+ 1)%a) ##
     (finz.seq_between so_switcher_b so_switcher_e ∪
      finz.seq_between so_trusted_stack_b so_trusted_stack_e ∪
      finz.seq_between so_stack_b so_stack_e)).
  pose proof so_concrete_region_partition_disjoint as Hpartition.
  solve_addr_partition_disjoint so_concrete_region_partition Hpartition.
Qed.

Global Instance so_concrete_layout : memory_layout.
Proof.
  exact
    (@Build_memory_layout machine_parameters_instance
       so_concrete_cmptSwitcher so_concrete_cmptAssert
       so_concrete_main_cmpt so_concrete_C_cmpt 3 40
       so_concrete_cmpts_disjoints
       so_concrete_switcher_cmpt_disjoints
       so_concrete_assert_cmpt_disjoints
       so_concrete_assert_switcher_disjoints).
Defined.

Definition so_initial_registers : Reg :=
  <[PC := WCap RX Global so_main_pcc_b so_main_pcc_e so_main_code_start]>
  (<[cgp := WCap RW Global so_main_data_b so_main_data_e so_main_data_b]>
  (<[csp := WCap RWL Local so_stack_b so_stack_e so_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).
Definition so_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local so_trusted_stack_b so_trusted_stack_e
      so_trusted_stack_b]> ∅.
Definition so_initial_memory : Mem := mk_initial_memory.

Lemma so_initial_registers_correct : is_initial_registers so_initial_registers.
Proof.
  rewrite /is_initial_registers /so_initial_registers.
  cbn [so_concrete_layout so_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma so_initial_sregisters_correct :
  is_initial_sregisters so_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /so_initial_sregisters.
  cbn [so_concrete_layout so_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma so_initial_memory_correct : is_initial_memory so_initial_memory.
Proof.
  rewrite /is_initial_memory /so_initial_memory.
  repeat split; try reflexivity.
  - rewrite /so_C_code /encodeInstrsW; repeat constructor; done.
  - rewrite /so_C_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Lemma so_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (so_initial_registers, so_initial_sregisters, so_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! so_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof (@so_adequacy machine_parameters_instance so_concrete_layout
    so_initial_registers reg' so_initial_sregisters sreg'
    so_initial_memory mem' es so_initial_registers_correct
    so_initial_sregisters_correct so_initial_memory_correct Hrun) as Hadequacy.
  cbn [so_concrete_layout so_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Combining the computed execution with [so_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem so_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (so_initial_registers, so_initial_sregisters, so_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! so_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_correct 7000 Executable
    (so_initial_registers, so_initial_sregisters, so_initial_memory)
    Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply so_concrete_adequacy; exact Hrun.
Qed.
