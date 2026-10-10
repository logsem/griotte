From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher compartment_layout
  disjoint_regions_tactics cmdc_concrete.
From griotte Require Import
  adequacy_helpers_binary stack_secret_binary stack_secret_adequacy_binary.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).

(** The switcher is the concrete switcher of the CMDC example: code at
    [131, 282), trusted stack at [4096, 4196), stack at [1024, 1124). *)
Definition ss_main_pcc_b : Addr := A 9.
Definition ss_main_code_start : Addr := A 11.
Definition ss_main_pcc_e : Addr := A 37.
Definition ss_main_data_b : Addr := A 37.
Definition ss_main_data_e : Addr := A 38.
Definition ss_main_exports_pcc : Addr := A 38.
Definition ss_main_exports_cgp : Addr := A 39.
Definition ss_main_exports_entries_b : Addr := A 40.
Definition ss_main_exports_entries_e : Addr := A 40.
Definition ss_B_pcc_b : Addr := A 40.
Definition ss_B_code_start : Addr := A 41.
Definition ss_B_pcc_e : Addr := A 43.
Definition ss_B_data_b : Addr := A 43.
Definition ss_B_data_e : Addr := A 44.
Definition ss_B_exports_pcc : Addr := A 44.
Definition ss_B_exports_cgp : Addr := A 45.
Definition ss_B_exports_entries_b : Addr := A 46.
Definition ss_B_exports_entries_e : Addr := A 47.

Ltac unfold_ss_addresses :=
  unfold ss_main_pcc_b, ss_main_code_start, ss_main_pcc_e,
    ss_main_data_b, ss_main_data_e, ss_main_exports_pcc,
    ss_main_exports_cgp, ss_main_exports_entries_b,
    ss_main_exports_entries_e, ss_B_pcc_b, ss_B_code_start, ss_B_pcc_e,
    ss_B_data_b, ss_B_data_e, ss_B_exports_pcc, ss_B_exports_cgp,
    ss_B_exports_entries_b, ss_B_exports_entries_e.

Ltac unfold_ss_addresses_in H :=
  unfold ss_main_pcc_b, ss_main_code_start, ss_main_pcc_e,
    ss_main_data_b, ss_main_data_e, ss_main_exports_pcc,
    ss_main_exports_cgp, ss_main_exports_entries_b,
    ss_main_exports_entries_e, ss_B_pcc_b, ss_B_code_start, ss_B_pcc_e,
    ss_B_data_b, ss_B_data_e, ss_B_exports_pcc, ss_B_exports_cgp,
    ss_B_exports_entries_b, ss_B_exports_entries_e in H.

(** The concrete adversary [B] reads the first word of the stack frame it
    receives, where [main] left a stale copy of the secret, and returns it
    to [main]. *)
Definition ss_B_code : list Word :=
  encodeInstrsW [
    Load ca0 csp;
    Jalr cnull cra
  ].
Definition ss_B_data : list Word := [WInt 0].
Definition ss_B_imports : list Word :=
  [WSentry XSRW_ Local cmdc_switcher_b cmdc_switcher_e cmdc_switcher_call].
Definition ss_B_exports : list Word :=
  [WInt (encode_entry_point stack_secret_B_f_args 1)].

Local Instance ss_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout cmdc_concrete_cmptSwitcher).
Defined.

Definition ss_B_f : Sealable :=
  SCap RO Global ss_B_exports_pcc ss_B_exports_entries_e
    ss_B_exports_entries_b.
Definition ss_main_imports_concrete : list Word :=
  stack_secret_main_imports ss_B_f.

Program Definition ss_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt ss_main_pcc_b ss_main_code_start ss_main_pcc_e
    ss_main_data_b ss_main_data_e ss_main_exports_pcc
    ss_main_exports_cgp ss_main_exports_entries_b
    ss_main_exports_entries_e ss_main_imports_concrete
    stack_secret_main_code (stack_secret_main_data 0) [] _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_ss_addresses; disj_regions.
Defined.

Program Definition ss_concrete_B_cmpt : cmpt.
Proof.
  refine (@mkCmpt ss_B_pcc_b ss_B_code_start ss_B_pcc_e
    ss_B_data_b ss_B_data_e ss_B_exports_pcc ss_B_exports_cgp
    ss_B_exports_entries_b ss_B_exports_entries_e ss_B_imports
    ss_B_code ss_B_data ss_B_exports _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_ss_addresses; disj_regions.
Defined.

Ltac solve_ss_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, cmpt_region,
       cmpt_pcc_region, cmpt_cgp_region, cmpt_exp_tbl_region,
       cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmdc_concrete_cmptSwitcher, ss_concrete_main_cmpt, ss_concrete_B_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end b_switcher e_switcher
       b_trusted_stack e_trusted_stack b_stack e_stack];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_ss_addresses_in Hx; unfold_ss_addresses_in Hx';
  unfold_cmdc_addresses_in Hx; unfold_cmdc_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance ss_concrete_layout : stack_secret_memory_layout.
Proof.
  refine (@Build_stack_secret_memory_layout machine_parameters_instance
    cmdc_concrete_cmptSwitcher ss_concrete_main_cmpt _
    ss_concrete_B_cmpt 1 _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - solve_ss_concrete_disjoint.
  - split; solve_ss_concrete_disjoint.
Defined.

Definition ss_initial_registers : Reg :=
  <[PC := WCap RX Global ss_main_pcc_b ss_main_pcc_e ss_main_code_start]>
  (<[cgp := WCap RW Global ss_main_data_b ss_main_data_e ss_main_data_b]>
  (<[csp := WCap RWL Local cmdc_stack_b cmdc_stack_e cmdc_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

(** The initial memory, holding [secret] in the data region of [main]. *)
Definition ss_initial_memory (secret : Z) : Mem :=
  stack_secret_adequacy_binary.mk_initial_memory secret.

Lemma ss_initial_registers_correct :
  stack_secret_adequacy_binary.is_initial_registers ss_initial_registers.
Proof.
  rewrite /stack_secret_adequacy_binary.is_initial_registers
    /ss_initial_registers.
  cbn [ss_concrete_layout ss_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma ss_initial_sregisters_correct :
  stack_secret_adequacy_binary.is_initial_sregisters cmdc_initial_sregisters.
Proof.
  rewrite /stack_secret_adequacy_binary.is_initial_sregisters
    /cmdc_initial_sregisters.
  cbn [ss_concrete_layout cmdc_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma ss_initial_memory_correct (secret : Z) :
  stack_secret_adequacy_binary.is_initial_memory secret
    (ss_initial_memory secret).
Proof.
  rewrite /stack_secret_adequacy_binary.is_initial_memory /ss_initial_memory.
  do 5 (split; first reflexivity).
  split; last split; last reflexivity.
  - rewrite /= /ss_B_code /encodeInstrsW; repeat constructor.
  - rewrite /= /ss_B_data; repeat constructor.
Qed.

(** The two runs from the concrete initial state, with the secrets
    [secret1] and [secret2], either both halt or both do not halt. *)
Theorem ss_concrete_adequacy (secret1 secret2 : Z) :
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (ss_initial_registers, cmdc_initial_sregisters,
           ss_initial_memory secret1))
        (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (ss_initial_registers, cmdc_initial_sregisters,
           ss_initial_memory secret2))
        (Seq (Instr Halted) :: es, c)).
Proof.
  exact (@stack_secret_adequacy machine_parameters_instance ss_concrete_layout
           ss_initial_registers cmdc_initial_sregisters
           (ss_initial_memory secret1) (ss_initial_memory secret2)
           secret1 secret2 ss_initial_registers_correct
           ss_initial_sregisters_correct (ss_initial_memory_correct secret1)
           (ss_initial_memory_correct secret2)).
Qed.

(** Running the machine with the secret [0] shows that this execution halts.
    Combined with [ss_concrete_adequacy], the execution halts for every
    secret: the adversary cannot learn anything about the secret through
    termination. *)
Theorem ss_runs_and_halts_for_all_secrets (secret : Z) :
  ∃ es c,
    rtc erased_step
      ([Seq (Instr Executable)],
        (ss_initial_registers, cmdc_initial_sregisters,
         ss_initial_memory secret))
      (Seq (Instr Halted) :: es, c).
Proof.
  apply (proj1 (ss_concrete_adequacy 0 secret)).
  edestruct (
    machine_run_halts 10000 Executable
      (ss_initial_registers, cmdc_initial_sregisters, ss_initial_memory 0)
  ) as [φ Hsteps].
  { vm_compute; reflexivity. }
  by exists [], φ.
Qed.
