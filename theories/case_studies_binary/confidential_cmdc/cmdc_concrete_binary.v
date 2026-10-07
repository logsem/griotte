From iris.program_logic Require Import adequacy.
From griotte Require Import
  machine_instructions machine_parameters machine_parameters_instance
  registers griotte_lang machine_run switcher compartment_layout
  disjoint_regions_tactics cmdc_concrete.
From griotte Require Import
  adequacy_helpers_binary cmdc_binary cmdc_adequacy_binary.

Existing Instance machine_parameters_instance.

Local Transparent MemNum ONum.

Local Notation "'A' z" :=
  (@finz.FinZ MemNum z%Z eq_refl eq_refl) (at level 10).

(** The switcher and the adversaries [B] and [C] are the concrete switcher
    and compartments [B] and [C] of the CMDC example: the switcher code is at
    [131, 282), the trusted stack at [4096, 4196), the stack at
    [1024, 1124); [B] occupies [98, 102), [107, 108) and [111, 114); [C]
    occupies [102, 105), [108, 109) and [114, 117). *)
Definition cmdc_conf_main_pcc_b : Addr := A 9.
Definition cmdc_conf_main_code_start : Addr := A 12.
Definition cmdc_conf_main_pcc_e : Addr := A 71.
Definition cmdc_conf_main_data_b : Addr := A 71.
Definition cmdc_conf_main_data_e : Addr := A 75.
Definition cmdc_conf_main_exports_pcc : Addr := A 75.
Definition cmdc_conf_main_exports_cgp : Addr := A 76.
Definition cmdc_conf_main_exports_entries_b : Addr := A 77.
Definition cmdc_conf_main_exports_entries_e : Addr := A 77.

Ltac unfold_cmdc_conf_addresses :=
  unfold cmdc_conf_main_pcc_b, cmdc_conf_main_code_start,
    cmdc_conf_main_pcc_e, cmdc_conf_main_data_b, cmdc_conf_main_data_e,
    cmdc_conf_main_exports_pcc, cmdc_conf_main_exports_cgp,
    cmdc_conf_main_exports_entries_b, cmdc_conf_main_exports_entries_e.

Ltac unfold_cmdc_conf_addresses_in H :=
  unfold cmdc_conf_main_pcc_b, cmdc_conf_main_code_start,
    cmdc_conf_main_pcc_e, cmdc_conf_main_data_b, cmdc_conf_main_data_e,
    cmdc_conf_main_exports_pcc, cmdc_conf_main_exports_cgp,
    cmdc_conf_main_exports_entries_b, cmdc_conf_main_exports_entries_e in H.

(** The concrete adversaries are the compartments [B] and [C] of the CMDC
    example. [B] writes [7] through the capability it receives and saves
    that capability on its stack; [C] writes [9] through its received
    capability. *)

Local Instance cmdc_conf_concrete_switcherLayout : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout cmdc_concrete_cmptSwitcher).
Defined.

Definition cmdc_conf_main_imports_concrete : list Word :=
  cmdc_conf_main_imports cmdc_B_f cmdc_C_g.

Program Definition cmdc_conf_concrete_main_cmpt : cmpt.
Proof.
  refine (@mkCmpt cmdc_conf_main_pcc_b cmdc_conf_main_code_start
    cmdc_conf_main_pcc_e cmdc_conf_main_data_b cmdc_conf_main_data_e
    cmdc_conf_main_exports_pcc cmdc_conf_main_exports_cgp
    cmdc_conf_main_exports_entries_b cmdc_conf_main_exports_entries_e
    cmdc_conf_main_imports_concrete cmdc_conf_main_code
    (cmdc_conf_main_data 0 0) [] _ _ _ _ _ _ _).
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - vm_compute; solve_addr.
  - unfold_cmdc_conf_addresses; disj_regions.
Defined.

Ltac solve_cmdc_conf_concrete_disjoint :=
  unfold disjoint_cmpt, switcher_cmpt_disjoint, cmpt_region,
       cmpt_pcc_region, cmpt_cgp_region, cmpt_exp_tbl_region,
       cmpt_switcher_region, cmpt_switcher_code_region,
       cmpt_switcher_trusted_stack_region, cmpt_switcher_stack_region,
       cmdc_concrete_cmptSwitcher, cmdc_conf_concrete_main_cmpt,
       cmdc_concrete_B_cmpt, cmdc_concrete_C_cmpt;
  cbn [cmpt_b_pcc cmpt_e_pcc cmpt_b_cgp cmpt_e_cgp
       cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end b_switcher e_switcher
       b_trusted_stack e_trusted_stack b_stack e_stack];
  intros x Hx Hx';
  repeat (rewrite elem_of_app in Hx || rewrite elem_of_app in Hx');
  repeat (rewrite elem_of_finz_seq_between in Hx ||
          rewrite elem_of_finz_seq_between in Hx');
  unfold_cmdc_conf_addresses_in Hx; unfold_cmdc_conf_addresses_in Hx';
  unfold_cmdc_addresses_in Hx; unfold_cmdc_addresses_in Hx';
  naive_solver (solve_addr).

Global Instance cmdc_conf_concrete_layout : cmdc_conf_memory_layout.
Proof.
  refine (@Build_cmdc_conf_memory_layout machine_parameters_instance
    cmdc_concrete_cmptSwitcher cmdc_conf_concrete_main_cmpt _
    cmdc_concrete_B_cmpt 1 cmdc_concrete_C_cmpt 1 _ _).
  - vm_compute; solve_addr.
  - repeat split; solve_cmdc_conf_concrete_disjoint.
  - repeat split; solve_cmdc_conf_concrete_disjoint.
Defined.

Definition cmdc_conf_initial_registers : Reg :=
  <[PC := WCap RX Global cmdc_conf_main_pcc_b cmdc_conf_main_pcc_e
      cmdc_conf_main_code_start]>
  (<[cgp := WCap RW Global cmdc_conf_main_data_b cmdc_conf_main_data_e
      cmdc_conf_main_data_b]>
  (<[csp := WCap RWL Local cmdc_stack_b cmdc_stack_e cmdc_stack_b]>
    (gset_to_gmap (WInt 0) all_registers_s))).

(** The initial memory, holding [secrets] [(secret_b, secret_c)] in the data
    region of [main]. *)
Definition cmdc_conf_initial_memory (secrets : Z * Z) : Mem :=
  cmdc_adequacy_binary.mk_initial_memory secrets.

Lemma cmdc_conf_initial_registers_correct :
  cmdc_adequacy_binary.is_initial_registers cmdc_conf_initial_registers.
Proof.
  rewrite /cmdc_adequacy_binary.is_initial_registers
    /cmdc_conf_initial_registers.
  cbn [cmdc_conf_concrete_layout cmdc_conf_concrete_main_cmpt].
  split; [|split; [|split]].
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - vm_compute; reflexivity.
  - intros r Hr; rewrite !lookup_insert_ne; try set_solver.
    apply lookup_gset_to_gmap_Some; split.
    + apply all_registers_s_correct.
    + done.
Qed.

Lemma cmdc_conf_initial_sregisters_correct :
  cmdc_adequacy_binary.is_initial_sregisters
    cmdc_initial_sregisters.
Proof.
  rewrite /cmdc_adequacy_binary.is_initial_sregisters
    /cmdc_initial_sregisters.
  cbn [cmdc_conf_concrete_layout cmdc_concrete_cmptSwitcher].
  simplify_map_eq; vm_compute; reflexivity.
Qed.

Lemma cmdc_conf_initial_memory_correct (secrets : Z * Z) :
  cmdc_adequacy_binary.is_initial_memory secrets
    (cmdc_conf_initial_memory secrets).
Proof.
  rewrite /cmdc_adequacy_binary.is_initial_memory
    /cmdc_conf_initial_memory.
  do 5 (split; first reflexivity).
  split; first (rewrite /= /cmdc_B_code /encodeInstrsW; repeat constructor).
  split; first (rewrite /= /cmdc_B_data; repeat constructor).
  do 2 (split; first reflexivity).
  split; first (rewrite /= /cmdc_C_code /encodeInstrsW; repeat constructor).
  split; first (rewrite /= /cmdc_C_data; repeat constructor).
  reflexivity.
Qed.

(** The two runs from the concrete initial state, with the secrets
    [secrets1] and [secrets2], either both halt or both do not halt. *)
Theorem cmdc_conf_concrete_adequacy (secrets1 secrets2 : Z * Z) :
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (cmdc_conf_initial_registers, cmdc_initial_sregisters,
           cmdc_conf_initial_memory secrets1))
        (Seq (Instr Halted) :: es, c)) ↔
  (∃ es c,
      rtc erased_step
        ([Seq (Instr Executable)],
          (cmdc_conf_initial_registers, cmdc_initial_sregisters,
           cmdc_conf_initial_memory secrets2))
        (Seq (Instr Halted) :: es, c)).
Proof.
  exact (@cmdc_conf_adequacy machine_parameters_instance
           cmdc_conf_concrete_layout cmdc_conf_initial_registers
           cmdc_initial_sregisters
           (cmdc_conf_initial_memory secrets1)
           (cmdc_conf_initial_memory secrets2)
           secrets1 secrets2 cmdc_conf_initial_registers_correct
           cmdc_conf_initial_sregisters_correct
           (cmdc_conf_initial_memory_correct secrets1)
           (cmdc_conf_initial_memory_correct secrets2)).
Qed.

(** Running the machine with the secrets [(0, 0)] shows that this execution
    halts. Combined with [cmdc_conf_concrete_adequacy], the execution halts
    for all secrets: the adversaries cannot learn anything about the secrets
    through termination. *)
Theorem cmdc_conf_runs_and_halts_for_all_secrets (secrets : Z * Z) :
  ∃ es c,
    rtc erased_step
      ([Seq (Instr Executable)],
        (cmdc_conf_initial_registers, cmdc_initial_sregisters,
         cmdc_conf_initial_memory secrets))
      (Seq (Instr Halted) :: es, c).
Proof.
  apply (proj1 (cmdc_conf_concrete_adequacy (0%Z, 0%Z) secrets)).
  edestruct (
    machine_run_halts 10000 Executable
      (cmdc_conf_initial_registers, cmdc_initial_sregisters,
       cmdc_conf_initial_memory (0%Z, 0%Z))
  ) as [φ Hsteps].
  { vm_compute; reflexivity. }
  by exists [], φ.
Qed.
