From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher compartment_layout
  disjoint_regions_tactics cmdc_concrete.
From griotte Require Import
  adequacy_helpers_binary fetch stack_callee_secret_binary
  stack_callee_secret_adequacy_binary.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).

(** The switcher is the concrete switcher of the CMDC example: code at
    [131, 282), trusted stack at [4096, 4196), stack at [1024, 1124). *)
Definition scs_T_pcc_b : Addr := A 9.
Definition scs_T_code_start : Addr := A 11.
Definition scs_T_pcc_e : Addr := A 36.
Definition scs_T_data_b : Addr := A 36.
Definition scs_T_data_e : Addr := A 37.
Definition scs_T_exports_pcc : Addr := A 37.
Definition scs_T_exports_cgp : Addr := A 38.
Definition scs_T_exports_entries_b : Addr := A 39.
Definition scs_T_exports_entries_e : Addr := A 40.
Definition scs_B_pcc_b : Addr := A 40.
Definition scs_B_code_start : Addr := A 42.
Definition scs_B_pcc_e : Addr := A 68.
Definition scs_B_data_b : Addr := A 68.
Definition scs_B_data_e : Addr := A 69.
Definition scs_B_exports_pcc : Addr := A 69.
Definition scs_B_exports_cgp : Addr := A 70.
Definition scs_B_exports_entries_b : Addr := A 71.
Definition scs_B_exports_entries_e : Addr := A 72.

Ltac unfold_scs_addresses :=
  unfold scs_T_pcc_b, scs_T_code_start, scs_T_pcc_e,
    scs_T_data_b, scs_T_data_e, scs_T_exports_pcc,
    scs_T_exports_cgp, scs_T_exports_entries_b,
    scs_T_exports_entries_e, scs_B_pcc_b, scs_B_code_start, scs_B_pcc_e,
    scs_B_data_b, scs_B_data_e, scs_B_exports_pcc, scs_B_exports_cgp,
    scs_B_exports_entries_b, scs_B_exports_entries_e.

Ltac unfold_scs_addresses_in H :=
  unfold scs_T_pcc_b, scs_T_code_start, scs_T_pcc_e,
    scs_T_data_b, scs_T_data_e, scs_T_exports_pcc,
    scs_T_exports_cgp, scs_T_exports_entries_b,
    scs_T_exports_entries_e, scs_B_pcc_b, scs_B_code_start, scs_B_pcc_e,
    scs_B_data_b, scs_B_data_e, scs_B_exports_pcc, scs_B_exports_cgp,
    scs_B_exports_entries_b, scs_B_exports_entries_e in H.

(** The concrete adversary [B] saves its return capability on its stack,
    calls [T.f] through the switcher, and then reads the first word of the
    stack frame that was given to [T.f], where [T.f] wrote the secret. It
    returns that word to [T]. *)
Definition scs_B_code : list Word :=
  encodeInstrsW [
    Store csp cra;
    Lea csp 1%Z
  ]
  ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
  ++ fetch_instrs 1 ct1 ct0 cs0 (* ct1 -> {T.f}_(ot_switcher) *)
  ++
  encodeInstrsW [
    Jalr cra ctp;
    (* the stack frame of T.f starts 4 words above the stack pointer *)
    Lea csp 4%Z;
    Load ca0 csp;
    Lea csp (-5)%Z;
    Load cra csp;
    Jalr cnull cra
  ].
Definition scs_B_data : list Word := [WInt 0].
Definition scs_T_f : Sealable :=
  SCap RO Global scs_T_exports_pcc scs_T_exports_entries_e
    scs_T_exports_entries_b.
Definition scs_B_imports : list Word :=
  [WSentry XSRW_ Local cmdc_switcher_b cmdc_switcher_e cmdc_switcher_call;
   WSealed cmdc_switcher_sealing_type scs_T_f].
Definition scs_B_exports : list Word :=
  [WInt (encode_entry_point stack_callee_secret_B_adv_args 2)].

Local Instance scs_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout cmdc_concrete_cmptSwitcher).
Defined.

Definition scs_B_adv : Sealable :=
  SCap RO Global scs_B_exports_pcc scs_B_exports_entries_e
    scs_B_exports_entries_b.
Definition scs_T_imports_concrete : list Word :=
  stack_callee_secret_imports scs_B_adv.

Program Definition scs_concrete_T_cmpt : cmpt.
Proof.
  refine (@mkCmpt scs_T_pcc_b scs_T_code_start scs_T_pcc_e
    scs_T_data_b scs_T_data_e scs_T_exports_pcc
    scs_T_exports_cgp scs_T_exports_entries_b
    scs_T_exports_entries_e scs_T_imports_concrete
    stack_callee_secret_code (stack_callee_secret_data 0)
    stack_callee_secret_export_table_entries _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_scs_addresses; disj_regions.
Defined.

Program Definition scs_concrete_B_cmpt : cmpt.
Proof.
  refine (@mkCmpt scs_B_pcc_b scs_B_code_start scs_B_pcc_e
    scs_B_data_b scs_B_data_e scs_B_exports_pcc scs_B_exports_cgp
    scs_B_exports_entries_b scs_B_exports_entries_e scs_B_imports
    scs_B_code scs_B_data scs_B_exports _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_scs_addresses; disj_regions.
Defined.

Ltac solve_scs_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, cmpt_region,
       cmpt_pcc_region, cmpt_cgp_region, cmpt_exp_tbl_region,
       cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmdc_concrete_cmptSwitcher, scs_concrete_T_cmpt, scs_concrete_B_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end b_switcher e_switcher
       b_trusted_stack e_trusted_stack b_stack e_stack];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_scs_addresses_in Hx; unfold_scs_addresses_in Hx';
  unfold_cmdc_addresses_in Hx; unfold_cmdc_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance scs_concrete_layout : stack_callee_secret_memory_layout.
Proof.
  refine (@Build_stack_callee_secret_memory_layout
    machine_parameters_instance
    cmdc_concrete_cmptSwitcher scs_concrete_T_cmpt _
    scs_concrete_B_cmpt 2 _ _).
  - vm_compute; solve_addr.
  - (* The regions are concrete: their disjointness is decided by computation. *)
    apply list_to_set_disj_2; apply (bool_decide_unpack _); vm_compute; reflexivity.
  - split; solve_scs_concrete_disjoint.
Defined.

Definition scs_initial_registers : Reg :=
  <[PC := WCap RX Global scs_T_pcc_b scs_T_pcc_e scs_T_code_start]>
  (<[cgp := WCap RW Global scs_T_data_b scs_T_data_e scs_T_data_b]>
  (<[csp := WCap RWL Local cmdc_stack_b cmdc_stack_e cmdc_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

(** The initial memory, holding [secret] in the data region of [T]. *)
Definition scs_initial_memory (secret : Z) : Mem :=
  stack_callee_secret_adequacy_binary.mk_initial_memory secret.

Lemma scs_initial_registers_correct :
  stack_callee_secret_adequacy_binary.is_initial_registers
    scs_initial_registers.
Proof.
  rewrite /stack_callee_secret_adequacy_binary.is_initial_registers
    /scs_initial_registers.
  cbn [scs_concrete_layout scs_concrete_T_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma scs_initial_sregisters_correct :
  stack_callee_secret_adequacy_binary.is_initial_sregisters
    cmdc_initial_sregisters.
Proof.
  rewrite /stack_callee_secret_adequacy_binary.is_initial_sregisters
    /cmdc_initial_sregisters.
  cbn [scs_concrete_layout cmdc_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma scs_initial_memory_correct (secret : Z) :
  stack_callee_secret_adequacy_binary.is_initial_memory secret
    (scs_initial_memory secret).
Proof.
  rewrite /stack_callee_secret_adequacy_binary.is_initial_memory
    /scs_initial_memory.
  do 5 (split; first reflexivity).
  split; last split; last reflexivity.
  - rewrite /= /scs_B_code /fetch_instrs /encodeInstrsW; repeat constructor.
  - rewrite /= /scs_B_data; repeat constructor.
Qed.

(** The two runs from the concrete initial state, with the secrets
    [secret1] and [secret2], either both halt or both do not halt. *)
Theorem scs_concrete_adequacy (secret1 secret2 : Z) :
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (scs_initial_registers, cmdc_initial_sregisters,
           scs_initial_memory secret1))
        (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (scs_initial_registers, cmdc_initial_sregisters,
           scs_initial_memory secret2))
        (Seq (Instr Halted) :: es, c)).
Proof.
  exact (@stack_callee_secret_adequacy machine_parameters_instance
           scs_concrete_layout
           scs_initial_registers cmdc_initial_sregisters
           (scs_initial_memory secret1) (scs_initial_memory secret2)
           secret1 secret2 scs_initial_registers_correct
           scs_initial_sregisters_correct (scs_initial_memory_correct secret1)
           (scs_initial_memory_correct secret2)).
Qed.

(** Running the machine with the secret [0] shows that this execution halts.
    Combined with [scs_concrete_adequacy], the execution halts for every
    secret: the adversary cannot learn anything about the secret through
    termination. *)
Theorem scs_runs_and_halts_for_all_secrets (secret : Z) :
  ∃ es c,
    rtc erased_step
      ([Seq (Instr Executable)],
        (scs_initial_registers, cmdc_initial_sregisters,
         scs_initial_memory secret))
      (Seq (Instr Halted) :: es, c).
Proof.
  apply (proj1 (scs_concrete_adequacy 0 secret)).
  edestruct (
    machine_run_halts 10000 Executable
      (scs_initial_registers, cmdc_initial_sregisters, scs_initial_memory 0)
  ) as [φ Hsteps].
  { vm_compute; reflexivity. }
  by exists [], φ.
Qed.
