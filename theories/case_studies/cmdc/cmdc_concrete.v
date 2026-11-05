From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang machine_run
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  cmdc cmdc_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link cmdc_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the CMDC case study

    The CMDC firmware with two concrete adversaries [B] and [C] and the
    round-robin scheduler, laid out by the linker. Its initial state
    satisfies [cmdc_initial_state_ok] by computation; from it the thread
    runs, through the scheduler, to its exit, where the scheduler halts the
    machine; [cmdc_adequacy] applies to the run. *)

Definition cmdc_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary consists of two unknown compartments. Compartment
    [B] writes [7] through the capability it receives, saves that
    capability on its stack, then yields once; compartment [C] writes [9]
    through its received capability. Together they exercise the main
    program's cross-compartment capability discipline. Each has one zeroed
    global, and its entry point right after its import. *)
Definition cmdc_B_code : list Word :=
  encodeInstrsW [
    Store ca0 7%Z 0;
    Store csp ca0 (-1)%Z;
    Ecall;
    Jalr cnull cra
  ].
Definition cmdc_C_code : list Word :=
  encodeInstrsW [
    Store ca0 9%Z 0;
    Jalr cnull cra
  ].
Definition cmdc_B_data : list Word := [WInt 0].
Definition cmdc_C_data : list Word := [WInt 0].

Definition cmdc_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 cmdc_switcher_sealing_type [
    ("B", {| la_code    := cmdc_B_code;
             la_data    := cmdc_B_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |});
    ("C", {| la_code    := cmdc_C_code;
             la_data    := cmdc_C_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 cmdc_firmware.

(** ** The linked image and its initial state *)

Definition cmdc_demo_image : fw_image :=
  Eval vm_compute in
    default (place cmdc_demo_link_cfg cmdc_firmware).1
      (link cmdc_demo_link_cfg cmdc_firmware).

Lemma cmdc_demo_linked :
  link cmdc_demo_link_cfg cmdc_firmware = Some cmdc_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition cmdc_demo_state : ExecConf := img_state cmdc_firmware cmdc_demo_image.

Lemma cmdc_demo_ok :
  cmdc_initial_state_ok (flag_assert (img_asrt cmdc_demo_image)) cmdc_demo_state.
Proof.
  rewrite /cmdc_initial_state_ok.
  exists (img_sw cmdc_demo_image), (img_asrt cmdc_demo_image), (thread_of cmdc_demo_image 0),
    (img_idle cmdc_demo_image), (img_boot cmdc_demo_image),
    (cmpt_of cmdc_demo_image "main"), (cmpt_of cmdc_demo_image "B"),
    (cmpt_of cmdc_demo_image "C"), (cmpt_of cmdc_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers cmdc_demo_link_cfg.
  all: try (exists 1%nat, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /cmdc_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [cmdc_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread. In [B] the thread yields once by an [ecall]: the
    switcher parks it and calls the scheduler, which resumes it after the
    [ecall]. The thread then runs to its exit, and the scheduler halts the
    machine. [cmdc_adequacy] applies to the run: the flag of the assert
    library is still zero. *)
Theorem cmdc_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! flag_assert (img_asrt cmdc_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 12000%N) cmdc_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (cmdc_adequacy _ _ _ _ cmdc_demo_ok Hrun).
Qed.

(** The round trip: thread 0 yields by its [ecall] in [B]. When the
    scheduler is about to return from the call this [ecall] causes, thread 0
    is parked in its save area with the cause of an [ecall], and the
    scheduler hands its handle back to the switcher, which resumes it. *)
Remark cmdc_demo_yields :
  ∃ σ1,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_demo_state)
      ([griotte_lang.Exec], σ1)
    ∧ rr_returning cmdc_demo_image MCAUSE_ECALL_MACHINE σ1 = true
    ∧ reg σ1 !! ca0 = Some (thread_handle cmdc_firmware cmdc_demo_image 0)
    ∧ mem σ1 !! (b_trusted_stack (thread_of cmdc_demo_image 0) ^+ TrustedStack_offset_mcause)%a
        = Some (WInt MCAUSE_ECALL_MACHINE).
Proof.
  pose proof (machine_run_until_correct (rr_returning cmdc_demo_image MCAUSE_ECALL_MACHINE)
    (N.to_nat 12000%N) Executable cmdc_demo_state) as Hrun.
  assert (match machine_run_until (rr_returning cmdc_demo_image MCAUSE_ECALL_MACHINE)
            (N.to_nat 12000%N) (Executable, cmdc_demo_state) with
          | Some σ1 =>
              rr_returning cmdc_demo_image MCAUSE_ECALL_MACHINE σ1 = true ∧
              bool_decide (reg σ1 !! ca0 = Some (thread_handle cmdc_firmware cmdc_demo_image 0))
                = true ∧
              bool_decide (mem σ1 !! (b_trusted_stack (thread_of cmdc_demo_image 0)
                                        ^+ TrustedStack_offset_mcause)%a
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true
          | None => False
          end) as Hσ1 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ1|]; [|done].
  destruct Hσ1 as (Hstop & Hca0 & Hmcause).
  exists σ1. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmcause.
Qed.
