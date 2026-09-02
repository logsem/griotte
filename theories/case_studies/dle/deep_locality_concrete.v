From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher assert compartment_layout
  deep_locality deep_locality_adequacy
  disjoint_regions_tactics.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).
Local Notation "'OT' z" :=
  (@finz.FinZ ONum z%Z eq_refl eq_refl) (at level 10).

Definition dle_main_pcc_b : Addr := A 9.
Definition dle_main_code_start : Addr := A 12.
Definition dle_main_pcc_e : Addr := A 67.
Definition dle_main_data_b : Addr := A 74.
Definition dle_main_data_e : Addr := A 76.
Definition dle_main_exports_pcc : Addr := A 77.
Definition dle_main_exports_cgp : Addr := A 78.
Definition dle_main_exports_entries_b : Addr := A 79.
Definition dle_main_exports_entries_e : Addr := A 79.

Definition dle_C_pcc_b : Addr := A 67.
Definition dle_C_code_start : Addr := A 68.
Definition dle_C_pcc_e : Addr := A 74.
Definition dle_C_data_b : Addr := A 76.
Definition dle_C_data_e : Addr := A 77.
Definition dle_C_exports_pcc : Addr := A 79.
Definition dle_C_exports_cgp : Addr := A 80.
Definition dle_C_exports_entries_b : Addr := A 81.
Definition dle_C_exports_entries_e : Addr := A 82.

Definition dle_assert_b : Addr := A 82.
Definition dle_assert_cap : Addr := A 94.
Definition dle_assert_e : Addr := A 95.
Definition dle_assert_flag : Addr := A 95.

Definition dle_switcher_b : Addr := A 96.
Definition dle_switcher_call : Addr := A 97.
Definition dle_switcher_return : Addr := A 185.
Definition dle_switcher_e : Addr := A 247.
Definition dle_switcher_sealing_type : OType := OT 9.

Definition dle_trusted_stack_b : Addr := A 4096.
Definition dle_trusted_stack_e : Addr := A 4196.
Definition dle_stack_b : Addr := A 1024.
Definition dle_stack_e : Addr := A 1124.

Ltac unfold_dle_addresses :=
  unfold dle_main_pcc_b, dle_main_code_start, dle_main_pcc_e,
    dle_main_data_b, dle_main_data_e, dle_main_exports_pcc,
    dle_main_exports_cgp, dle_main_exports_entries_b,
    dle_main_exports_entries_e, dle_C_pcc_b, dle_C_code_start,
    dle_C_pcc_e, dle_C_data_b, dle_C_data_e, dle_C_exports_pcc,
    dle_C_exports_cgp, dle_C_exports_entries_b,
    dle_C_exports_entries_e, dle_assert_b, dle_assert_cap,
    dle_assert_e, dle_assert_flag, dle_switcher_b, dle_switcher_call,
    dle_switcher_return, dle_switcher_e, dle_switcher_sealing_type,
    dle_trusted_stack_b, dle_trusted_stack_e, dle_stack_b,
    dle_stack_e.

Ltac unfold_dle_addresses_in H :=
  unfold dle_main_pcc_b, dle_main_code_start, dle_main_pcc_e,
    dle_main_data_b, dle_main_data_e, dle_main_exports_pcc,
    dle_main_exports_cgp, dle_main_exports_entries_b,
    dle_main_exports_entries_e, dle_C_pcc_b, dle_C_code_start,
    dle_C_pcc_e, dle_C_data_b, dle_C_data_e, dle_C_exports_pcc,
    dle_C_exports_cgp, dle_C_exports_entries_b,
    dle_C_exports_entries_e, dle_assert_b, dle_assert_cap,
    dle_assert_e, dle_assert_flag, dle_switcher_b, dle_switcher_call,
    dle_switcher_return, dle_switcher_e, dle_switcher_sealing_type,
    dle_trusted_stack_b, dle_trusted_stack_e, dle_stack_b,
    dle_stack_e in H.

(** The concrete adversary examines the argument passed in [ca0]. If it is a
    capability, the adversary follows it to the nested capability and attempts
    to overwrite the nested cell with [7]; otherwise it simply returns. This
    instantiates the unknown compartment with a direct attack on deep locality. *)
Definition dle_C_code : list Word :=
  encodeInstrsW [
    GetWType ct0 ca0;
    Sub ct0 ct0 (encodeWordType wt_cap);
    Jnz 3%Z ct0;
    Load ct0 ca0;
    Store ct0 7%Z;
    Jalr cnull cra
  ].

Definition dle_C_data : list Word := [WInt 0].

Definition dle_C_imports : list Word :=
  [WSentry XSRW_ Local dle_switcher_b dle_switcher_e dle_switcher_call].

Definition dle_C_exports : list Word :=
  [WInt (encode_entry_point 1 1)].

Program Definition dle_concrete_cmptSwitcher : cmptSwitcher.
Proof.
  refine (@mkCmptSwitcher machine_parameters_instance
    dle_switcher_b dle_switcher_e
    dle_switcher_call dle_switcher_return dle_switcher_sealing_type
    dle_trusted_stack_b dle_trusted_stack_e
    _ _ _ _
    (replicate 100 (WInt 0)) _ eq_refl
    dle_stack_b dle_stack_e (replicate 100 (WInt 0)) _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_dle_addresses.
    repeat split; unfold disjoint, set_disjoint_instance;
      intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
      solve_addr.
Defined.

Program Definition dle_concrete_cmptAssert : cmptAssert.
Proof.
  refine (@mkCmptAssert machine_parameters_instance
    dle_assert_b dle_assert_e dle_assert_cap dle_assert_flag _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_dle_addresses.
    unfold disjoint, set_disjoint_instance.
    intros x Hx Hx'.
    rewrite !elem_of_finz_seq_between in Hx, Hx'.
    solve_addr.
Defined.

Local Instance dle_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout dle_concrete_cmptSwitcher).
Defined.

Local Instance dle_concrete_assertLayout : assertLayout.
Proof.
  exact (cmptAssert_assertLayout dle_concrete_cmptAssert).
Defined.

Definition dle_C_f : Sealable :=
  SCap RO Global dle_C_exports_pcc dle_C_exports_entries_e
    dle_C_exports_entries_b.

Definition dle_main_imports_concrete : list Word :=
  dle_main_imports dle_C_f.

Program Definition dle_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    dle_main_pcc_b dle_main_code_start dle_main_pcc_e
    dle_main_data_b dle_main_data_e
    dle_main_exports_pcc dle_main_exports_cgp
    dle_main_exports_entries_b dle_main_exports_entries_e
    dle_main_imports_concrete dle_main_code dle_main_data []
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_dle_addresses; disj_regions.
Defined.

Program Definition dle_concrete_C_cmpt : cmpt.
Proof.
  refine (@mkCmpt
    dle_C_pcc_b dle_C_code_start dle_C_pcc_e
    dle_C_data_b dle_C_data_e
    dle_C_exports_pcc dle_C_exports_cgp
    dle_C_exports_entries_b dle_C_exports_entries_e
    dle_C_imports dle_C_code dle_C_data dle_C_exports
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_dle_addresses; disj_regions.
Defined.

(** All nonempty concrete regions, in increasing address order. The two
    compartment static-sealed ranges are empty and deliberately omitted. *)
Definition dle_concrete_region_partition : list (list Addr) :=
  [ finz.seq_between dle_main_pcc_b dle_main_pcc_e;
    finz.seq_between dle_C_pcc_b dle_C_pcc_e;
    finz.seq_between dle_main_data_b dle_main_data_e;
    finz.seq_between dle_C_data_b dle_C_data_e;
    finz.seq_between dle_main_exports_pcc dle_main_exports_entries_e;
    finz.seq_between dle_C_exports_pcc dle_C_exports_entries_e;
    finz.seq_between dle_assert_b dle_assert_cap;
    finz.seq_between dle_assert_cap dle_assert_e;
    finz.seq_between dle_assert_flag (dle_assert_flag ^+ 1)%a;
    finz.seq_between dle_switcher_b dle_switcher_e;
    finz.seq_between dle_stack_b dle_stack_e;
    finz.seq_between dle_trusted_stack_b dle_trusted_stack_e
  ].

Lemma dle_concrete_region_partition_disjoint :
  ## dle_concrete_region_partition.
Proof.
  rewrite /dle_concrete_region_partition.
  unfold_dle_addresses.
  disj_regions.
Qed.

Local Lemma dle_concrete_cmpts_disjoints :
  dle_concrete_main_cmpt ## dle_concrete_C_cmpt.
Proof.
  change
    ((finz.seq_between dle_main_pcc_b dle_main_pcc_e ∪
      finz.seq_between dle_main_data_b dle_main_data_e ∪
      finz.seq_between dle_main_data_e dle_main_data_e ∪
      finz.seq_between dle_main_exports_pcc dle_main_exports_entries_e)
       ##
     (finz.seq_between dle_C_pcc_b dle_C_pcc_e ∪
      finz.seq_between dle_C_data_b dle_C_data_e ∪
      finz.seq_between dle_C_data_e dle_C_data_e ∪
      finz.seq_between dle_C_exports_pcc dle_C_exports_entries_e)).
  pose proof dle_concrete_region_partition_disjoint as Hpartition.
  rewrite (finz_seq_between_empty dle_main_data_e dle_main_data_e);
    last solve_addr.
  rewrite (finz_seq_between_empty dle_C_data_e dle_C_data_e);
    last solve_addr.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint dle_concrete_region_partition Hpartition.
Qed.

Local Lemma dle_concrete_switcher_cmpt_disjoints :
  switcher_cmpt_disjoint
    dle_concrete_main_cmpt dle_concrete_cmptSwitcher
  ∧ switcher_cmpt_disjoint
      dle_concrete_C_cmpt dle_concrete_cmptSwitcher.
Proof.
  change
    ((finz.seq_between dle_switcher_b dle_switcher_e ∪
      finz.seq_between dle_trusted_stack_b dle_trusted_stack_e ∪
      finz.seq_between dle_stack_b dle_stack_e)
       ##
     (finz.seq_between dle_main_pcc_b dle_main_pcc_e ∪
      finz.seq_between dle_main_data_b dle_main_data_e ∪
      finz.seq_between dle_main_data_e dle_main_data_e ∪
      finz.seq_between dle_main_exports_pcc dle_main_exports_entries_e)
     /\
     (finz.seq_between dle_switcher_b dle_switcher_e ∪
      finz.seq_between dle_trusted_stack_b dle_trusted_stack_e ∪
      finz.seq_between dle_stack_b dle_stack_e)
       ##
     (finz.seq_between dle_C_pcc_b dle_C_pcc_e ∪
      finz.seq_between dle_C_data_b dle_C_data_e ∪
      finz.seq_between dle_C_data_e dle_C_data_e ∪
      finz.seq_between dle_C_exports_pcc dle_C_exports_entries_e)).
  pose proof dle_concrete_region_partition_disjoint as Hpartition.
  rewrite (finz_seq_between_empty dle_main_data_e dle_main_data_e);
    last solve_addr.
  rewrite (finz_seq_between_empty dle_C_data_e dle_C_data_e);
    last solve_addr.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint dle_concrete_region_partition Hpartition.
Qed.

Local Lemma dle_concrete_assert_cmpt_disjoints :
  assert_cmpt_disjoint dle_concrete_main_cmpt dle_concrete_cmptAssert
  ∧ assert_cmpt_disjoint dle_concrete_C_cmpt dle_concrete_cmptAssert.
Proof.
  change
    ((finz.seq_between dle_assert_b dle_assert_cap ∪
      finz.seq_between dle_assert_cap dle_assert_e ∪
      finz.seq_between dle_assert_flag (dle_assert_flag ^+ 1)%a)
       ##
     (finz.seq_between dle_main_pcc_b dle_main_pcc_e ∪
      finz.seq_between dle_main_data_b dle_main_data_e ∪
      finz.seq_between dle_main_data_e dle_main_data_e ∪
      finz.seq_between dle_main_exports_pcc dle_main_exports_entries_e)
     /\
     (finz.seq_between dle_assert_b dle_assert_cap ∪
      finz.seq_between dle_assert_cap dle_assert_e ∪
      finz.seq_between dle_assert_flag (dle_assert_flag ^+ 1)%a)
       ##
     (finz.seq_between dle_C_pcc_b dle_C_pcc_e ∪
      finz.seq_between dle_C_data_b dle_C_data_e ∪
      finz.seq_between dle_C_data_e dle_C_data_e ∪
      finz.seq_between dle_C_exports_pcc dle_C_exports_entries_e)).
  pose proof dle_concrete_region_partition_disjoint as Hpartition.
  rewrite (finz_seq_between_empty dle_main_data_e dle_main_data_e);
    last solve_addr.
  rewrite (finz_seq_between_empty dle_C_data_e dle_C_data_e);
    last solve_addr.
  rewrite !(@union_empty_r Addr (list Addr) _ _ _ _ _).
  solve_addr_partition_disjoint dle_concrete_region_partition Hpartition.
Qed.

Local Lemma dle_concrete_assert_switcher_disjoints :
  assert_switcher_disjoint
    dle_concrete_cmptAssert dle_concrete_cmptSwitcher.
Proof.
  change
    ((finz.seq_between dle_assert_b dle_assert_cap ∪
      finz.seq_between dle_assert_cap dle_assert_e ∪
      finz.seq_between dle_assert_flag (dle_assert_flag ^+ 1)%a)
       ##
     (finz.seq_between dle_switcher_b dle_switcher_e ∪
      finz.seq_between dle_trusted_stack_b dle_trusted_stack_e ∪
      finz.seq_between dle_stack_b dle_stack_e)).
  pose proof dle_concrete_region_partition_disjoint as Hpartition.
  solve_addr_partition_disjoint dle_concrete_region_partition Hpartition.
Qed.

Global Instance dle_concrete_layout : memory_layout.
Proof.
  exact
    (@Build_memory_layout
       machine_parameters_instance
       dle_concrete_cmptSwitcher
       dle_concrete_cmptAssert
       dle_concrete_main_cmpt
       dle_concrete_C_cmpt
       dle_concrete_cmpts_disjoints
       dle_concrete_switcher_cmpt_disjoints
       dle_concrete_assert_cmpt_disjoints
       dle_concrete_assert_switcher_disjoints).
Defined.

Definition dle_initial_registers : Reg :=
  <[PC := WCap RX Global dle_main_pcc_b dle_main_pcc_e dle_main_code_start]>
  (<[cgp := WCap RW Global dle_main_data_b dle_main_data_e
      dle_main_data_b]>
  (<[csp := WCap RWL Local dle_stack_b dle_stack_e dle_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

Definition dle_initial_sregisters : SReg :=
  <[MTDC := WCap RWL Local dle_trusted_stack_b dle_trusted_stack_e
      dle_trusted_stack_b]> ∅.

Definition dle_initial_memory : Mem := mk_initial_memory.

Lemma dle_initial_registers_correct :
  is_initial_registers dle_initial_registers.
Proof.
  rewrite /is_initial_registers /dle_initial_registers.
  cbn [dle_concrete_layout dle_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma dle_initial_sregisters_correct :
  is_initial_sregisters dle_initial_sregisters.
Proof.
  rewrite /is_initial_sregisters /dle_initial_sregisters.
  cbn [dle_concrete_layout dle_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma dle_initial_memory_correct :
  is_initial_memory dle_initial_memory.
Proof.
  rewrite /is_initial_memory /dle_initial_memory.
  repeat split; try reflexivity.
  - rewrite /dle_C_code /encodeInstrsW;
      repeat constructor; done.
  - rewrite /dle_C_data; repeat constructor; done.
  - apply Forall_replicate; done.
Qed.

Lemma dle_concrete_adequacy reg' sreg' mem' es :
  rtc erased_step
    ([Seq (Instr Executable)],
      (dle_initial_registers, dle_initial_sregisters, dle_initial_memory))
    (es, (reg', sreg', mem')) ->
  mem' !! dle_assert_flag = Some (WInt 0%Z).
Proof.
  intro Hrun.
  pose proof
    (@dle_adequacy machine_parameters_instance dle_concrete_layout
      dle_initial_registers reg'
      dle_initial_sregisters sreg'
      dle_initial_memory mem' es
      dle_initial_registers_correct
      dle_initial_sregisters_correct
      dle_initial_memory_correct Hrun) as Hadequacy.
  cbn [dle_concrete_layout dle_concrete_cmptAssert] in Hadequacy.
  exact Hadequacy.
Qed.

(** Fuel 3000 is insufficient for this concrete run; 5000 reaches [Halted]. *)
(** Combining the computed execution with [dle_concrete_adequacy] shows that
    there is a final machine state such that the exact initial configuration:
    - executes to [Halted], rather than failing or exhausting the chosen fuel;
    - finishes with the assertion flag still set to zero.
    Thus this particular adversarial execution terminates normally without
    violating the case study's assertion. *)
Theorem dle_runs_and_gracefully_halts :
  ∃ reg' sreg' mem',
    rtc erased_step
      ([Seq (Instr Executable)],
        (dle_initial_registers, dle_initial_sregisters, dle_initial_memory))
      ([Instr Halted], (reg', sreg', mem'))
    ∧ mem' !! dle_assert_flag = Some (WInt 0%Z).
Proof.
  pose proof
    (machine_run_correct 5000 Executable
      (dle_initial_registers, dle_initial_sregisters, dle_initial_memory)
      Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [[[reg' sreg'] mem'] Hrun].
  exists reg', sreg', mem'. split.
  - exact Hrun.
  - eapply dle_concrete_adequacy; exact Hrun.
Qed.
