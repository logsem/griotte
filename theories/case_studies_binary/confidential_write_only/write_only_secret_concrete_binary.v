From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher compartment_layout
  disjoint_regions_tactics cmdc_concrete.
From griotte Require Import
  adequacy_helpers_binary write_only_secret_binary
  write_only_secret_adequacy_binary.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).

(** The switcher and the adversary [B] are the concrete switcher and
    compartment [B] of the CMDC example: the switcher code is at
    [131, 282), the trusted stack at [4096, 4196), the stack at
    [1024, 1124); [B] occupies [98, 102), [107, 108) and [111, 114). *)
Definition wo_main_pcc_b : Addr := A 9.
Definition wo_main_code_start : Addr := A 11.
Definition wo_main_pcc_e : Addr := A 33.
Definition wo_main_data_b : Addr := A 33.
Definition wo_main_data_e : Addr := A 34.
Definition wo_main_exports_pcc : Addr := A 34.
Definition wo_main_exports_cgp : Addr := A 35.
Definition wo_main_exports_entries_b : Addr := A 36.
Definition wo_main_exports_entries_e : Addr := A 36.

Ltac unfold_wo_addresses :=
  unfold wo_main_pcc_b, wo_main_code_start, wo_main_pcc_e,
    wo_main_data_b, wo_main_data_e, wo_main_exports_pcc,
    wo_main_exports_cgp, wo_main_exports_entries_b,
    wo_main_exports_entries_e.

Ltac unfold_wo_addresses_in H :=
  unfold wo_main_pcc_b, wo_main_code_start, wo_main_pcc_e,
    wo_main_data_b, wo_main_data_e, wo_main_exports_pcc,
    wo_main_exports_cgp, wo_main_exports_entries_b,
    wo_main_exports_entries_e in H.

(** The concrete adversary is the compartment [B] of the CMDC example. It
    writes [7] through the write-only capability it receives, overwriting
    the secret, and saves that capability on its stack. *)

Local Instance wo_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout cmdc_concrete_cmptSwitcher).
Defined.

Definition wo_main_imports_concrete : list Word :=
  write_only_secret_main_imports cmdc_B_f.

Program Definition wo_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt wo_main_pcc_b wo_main_code_start wo_main_pcc_e
    wo_main_data_b wo_main_data_e wo_main_exports_pcc
    wo_main_exports_cgp wo_main_exports_entries_b
    wo_main_exports_entries_e wo_main_imports_concrete
    write_only_secret_main_code (write_only_secret_main_data 0) []
    _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_wo_addresses; disj_regions.
Defined.

Ltac solve_wo_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, cmpt_region,
       cmpt_pcc_region, cmpt_cgp_region, cmpt_exp_tbl_region,
       cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmdc_concrete_cmptSwitcher, wo_concrete_main_cmpt,
       cmdc_concrete_B_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end b_switcher e_switcher
       b_trusted_stack e_trusted_stack b_stack e_stack];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_wo_addresses_in Hx; unfold_wo_addresses_in Hx';
  unfold_cmdc_addresses_in Hx; unfold_cmdc_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance wo_concrete_layout : write_only_secret_memory_layout.
Proof.
  refine (@Build_write_only_secret_memory_layout machine_parameters_instance
    cmdc_concrete_cmptSwitcher wo_concrete_main_cmpt _
    cmdc_concrete_B_cmpt 1 _ _).
  - vm_compute; solve_addr.
  - solve_wo_concrete_disjoint.
  - split; solve_wo_concrete_disjoint.
Defined.

Definition wo_initial_registers : Reg :=
  <[PC := WCap RX Global wo_main_pcc_b wo_main_pcc_e wo_main_code_start]>
  (<[cgp := WCap RW Global wo_main_data_b wo_main_data_e wo_main_data_b]>
  (<[csp := WCap RWL Local cmdc_stack_b cmdc_stack_e cmdc_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

(** The initial memory, holding [secret] in the data region of [main]. *)
Definition wo_initial_memory (secret : Z) : Mem :=
  write_only_secret_adequacy_binary.mk_initial_memory secret.

Lemma wo_initial_registers_correct :
  write_only_secret_adequacy_binary.is_initial_registers wo_initial_registers.
Proof.
  rewrite /write_only_secret_adequacy_binary.is_initial_registers
    /wo_initial_registers.
  cbn [wo_concrete_layout wo_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma wo_initial_sregisters_correct :
  write_only_secret_adequacy_binary.is_initial_sregisters
    cmdc_initial_sregisters.
Proof.
  rewrite /write_only_secret_adequacy_binary.is_initial_sregisters
    /cmdc_initial_sregisters.
  cbn [wo_concrete_layout cmdc_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma wo_initial_memory_correct (secret : Z) :
  write_only_secret_adequacy_binary.is_initial_memory secret
    (wo_initial_memory secret).
Proof.
  rewrite /write_only_secret_adequacy_binary.is_initial_memory
    /wo_initial_memory.
  do 5 (split; first reflexivity).
  split; last split; last reflexivity.
  - rewrite /= /cmdc_B_code /encodeInstrsW; repeat constructor.
  - rewrite /= /cmdc_B_data; repeat constructor.
Qed.

(** The two runs from the concrete initial state, with the secrets
    [secret1] and [secret2], either both halt or both do not halt. *)
Theorem wo_concrete_adequacy (secret1 secret2 : Z) :
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (wo_initial_registers, cmdc_initial_sregisters,
           wo_initial_memory secret1))
        (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (wo_initial_registers, cmdc_initial_sregisters,
           wo_initial_memory secret2))
        (Seq (Instr Halted) :: es, c)).
Proof.
  exact (@write_only_secret_adequacy machine_parameters_instance
           wo_concrete_layout wo_initial_registers cmdc_initial_sregisters
           (wo_initial_memory secret1) (wo_initial_memory secret2)
           secret1 secret2 wo_initial_registers_correct
           wo_initial_sregisters_correct (wo_initial_memory_correct secret1)
           (wo_initial_memory_correct secret2)).
Qed.

(** Running the machine with the secret [0] shows that this execution halts.
    Combined with [wo_concrete_adequacy], the execution halts for every
    secret: the adversary cannot learn anything about the secret through
    termination. *)
Theorem wo_runs_and_halts_for_all_secrets (secret : Z) :
  ∃ es c,
    rtc erased_step
      ([Seq (Instr Executable)],
        (wo_initial_registers, cmdc_initial_sregisters,
         wo_initial_memory secret))
      (Seq (Instr Halted) :: es, c).
Proof.
  apply (proj1 (wo_concrete_adequacy 0 secret)).
  edestruct (
    machine_run_halts 10000 Executable
      (wo_initial_registers, cmdc_initial_sregisters, wo_initial_memory 0)
  ) as [φ Hsteps].
  { vm_compute; reflexivity. }
  by exists [], φ.
Qed.
