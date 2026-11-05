From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  cmdc cmdc_isolated_adequacy.
From griotte Require assembler.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link cmdc_isolated_firmware
  round_robin_scheduler_concrete cmdc_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the CMDC firmware with an isolated thread

    The CMDC firmware's concrete adversaries [B] and [C], a concrete
    adversary [D] for the thread 1, and the round-robin scheduler, laid out
    by the linker. Its initial state satisfies
    [cmdc_isolated_initial_state_ok] by computation. From it the threads
    interleave both ways, once by an interrupt and three times by the
    threads' own [ecall]s and exits; the scheduler halts the machine when
    the last thread exits. [cmdc_isolated_adequacy] applies to the run. *)

(** The isolated adversary: it yields once by an [ecall], then returns,
    which exits its thread. One zeroed global, and its entry point right
    after its import. *)
Definition cmdc_isolated_D_code : list Word :=
  encodeInstrsW [
    Ecall;
    Jalr cnull cra
  ].
Definition cmdc_isolated_D_data : list Word := [WInt 0].

(** [B] and [C] are the CMDC demo's adversaries ([cmdc_concrete]). *)
Definition cmdc_isolated_demo_link_cfg : link_cfg :=
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
             la_handler_stackless := ExportTable_no_handler |});
    ("D", {| la_code    := cmdc_isolated_D_code;
             la_data    := cmdc_isolated_D_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 cmdc_isolated_firmware.

(** ** The linked image and its initial state *)

Definition cmdc_isolated_demo_image : fw_image :=
  Eval vm_compute in
    default (place cmdc_isolated_demo_link_cfg cmdc_isolated_firmware).1
      (link cmdc_isolated_demo_link_cfg cmdc_isolated_firmware).

Lemma cmdc_isolated_demo_linked :
  link cmdc_isolated_demo_link_cfg cmdc_isolated_firmware = Some cmdc_isolated_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition cmdc_isolated_demo_state : ExecConf :=
  img_state cmdc_isolated_firmware cmdc_isolated_demo_image.

(** The entry word of [adv], as the linker writes it: no argument, no
    minimum stack, right after the import. *)
Definition cmdc_isolated_D_adv_word : Z :=
  encode_entry_point InterruptEnabled 0 0 1.

Lemma cmdc_isolated_demo_ok :
  cmdc_isolated_initial_state_ok (flag_assert (img_asrt cmdc_isolated_demo_image))
    cmdc_isolated_demo_state.
Proof.
  rewrite /cmdc_isolated_initial_state_ok.
  exists (img_sw cmdc_isolated_demo_image), (img_asrt cmdc_isolated_demo_image),
    (thread_of cmdc_isolated_demo_image 0), (thread_of cmdc_isolated_demo_image 1),
    (img_idle cmdc_isolated_demo_image), (img_boot cmdc_isolated_demo_image),
    (cmpt_of cmdc_isolated_demo_image "main"), (cmpt_of cmdc_isolated_demo_image "B"),
    (cmpt_of cmdc_isolated_demo_image "C"), (cmpt_of cmdc_isolated_demo_image "D"),
    (cmpt_of cmdc_isolated_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers cmdc_isolated_demo_link_cfg.
  all: try (exists 1%nat, 0%nat; split_and!).
  (* The entry word of [adv]: the minimum stack of the thread 1 *)
  all: try (lazymatch goal with
            | |- ∃ z : Z, cmpt_exp_tbl_entries _ !! _ = Some (WInt z) ∧ _ =>
                exists cmdc_isolated_D_adv_word; split
            end).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /cmdc_isolated_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run *)

(** The interrupt of the run: the machine timer's. The hardware takes an
    interrupt whenever interrupts are enabled, whatever the timer devices
    hold; in this run [mtime] stays [0], below the threshold the scheduler
    programs. *)
Definition cmdc_isolated_irq_cause : Z := (MCAUSE_INTR + MCAUSE_MTIME)%Z.

(** Where the interrupt hits the thread 0: [main]'s jump to the switcher
    for its call of [B], with interrupts enabled. *)
Definition cmdc_isolated_irq_addr (img : fw_image) : Addr :=
  (cmpt_b_pcc (cmpt_of img "main")
     ^+ Z.of_nat (assembler.Asm_Griotte.label_offset (concat cmdc_main_asm) ".Lcmdc_jump_B"))%a.

(** [cmdc_isolated_demo_state] starts at the switcher's call of the
    scheduler, which resumes the thread 0. The run stops in [main] at its
    jump to the switcher for its call of [B], where interrupts are enabled,
    and takes an interrupt there: the switcher parks the thread 0 and calls
    the scheduler, which resumes the thread 1 in [D]. [D] yields by an
    [ecall], and the thread 0 resumes at its jump; in [B] it yields by an
    [ecall], and the thread 1 resumes after its [ecall] and exits; the
    thread 0 resumes after its [ecall], runs to its exit, and the scheduler
    halts the machine. The first conjunct is the run with the interrupt:
    [machine_run_irq] gives a result only if the run reaches [main]'s jump
    with interrupts enabled and takes the interrupt there.
    [cmdc_isolated_adequacy] applies to the run: the flag of the assert
    library is still zero. *)
Theorem cmdc_isolated_runs_and_gracefully_halts :
  machine_run_irq (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image)) (N.to_nat 12000%N)
    cmdc_isolated_irq_cause (N.to_nat 20000%N) cmdc_isolated_demo_state = Some Halted
  ∧ ∃ σ',
      rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_isolated_demo_state)
        ([Instr Halted], σ')
      ∧ mem σ' !! flag_assert (img_asrt cmdc_isolated_demo_image) = Some (WInt 0%Z).
Proof.
  assert (machine_run_irq (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image))
            (N.to_nat 12000%N) cmdc_isolated_irq_cause (N.to_nat 20000%N)
            cmdc_isolated_demo_state = Some Halted) as Hirq by (vm_compute; reflexivity).
  split; first exact Hirq.
  assert (cmdc_isolated_irq_cause ∈ irq_causes) as Hcause.
  { rewrite /cmdc_isolated_irq_cause /irq_causes. apply list_elem_of_here. }
  destruct (machine_run_irq_hw_correct _ _ _ _ _ _ Hcause Hirq) as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (cmdc_isolated_adequacy _ _ _ _ cmdc_isolated_demo_ok Hrun).
Qed.

(** ** The hand-overs *)

(* TODO: move to program_logic/hw_machine_run.v *)
(** The interpreter with one interrupt of cause [c], taken at the first
    state that [stop1] accepts if interrupts are enabled there, stopped
    at the next state that [stop2] accepts. *)
Definition machine_run_irq_until `{MP : MachineParameters} (stop1 : ExecConf → bool)
    (fuel1 : nat) (c : Z) (stop2 : ExecConf → bool) (fuel2 : nat) (σ : ExecConf) :
    option ExecConf :=
  match machine_run_until stop1 fuel1 (Executable, σ) with
  | Some σ1 =>
      if decide (mie_of (get_a (sreg_word σ1 mstatus)) = InterruptEnabled)
      then machine_run_until stop2 fuel2 (Executable, enter_irq c σ1)
      else None
  | None => None
  end.

(* TODO: move to program_logic/hw_machine_run.v *)
Lemma machine_run_irq_until_hw_correct `{MP : MachineParameters} stop1 fuel1 c stop2 fuel2
    (σ σ2 : ExecConf) :
  c ∈ irq_causes →
  machine_run_irq_until stop1 fuel1 c stop2 fuel2 σ = Some σ2 →
  rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], σ) ([griotte_lang.Exec], σ2).
Proof.
  intros Hcause. rewrite /machine_run_irq_until.
  destruct (machine_run_until stop1 fuel1 (Executable, σ)) as [σ1|] eqn:Hu; [|done].
  case_decide as Hen; [|done].
  intros Hrun.
  eapply rtc_trans; [by apply rtc_erased_step_hw, (machine_run_until_correct _ _ _ _ _ Hu)|].
  eapply rtc_l; [|by apply rtc_erased_step_hw, (machine_run_until_correct _ _ _ _ _ Hrun)].
  exists []. eapply (step_atomic (Λ := griotte_hw_lang) _ _ _ _ _ [] []); [done|done|].
  by apply hw_irq_step.
Qed.

(** Where the switcher saves the cause of the thread [i]'s last trap. *)
Definition cmdc_isolated_saved_mcause (i : nat) : Addr :=
  (b_trusted_stack (thread_of cmdc_isolated_demo_image i) ^+ TrustedStack_offset_mcause)%a.

(** The interrupt (thread 0 to thread 1). When the scheduler is about to
    return from the call the interrupt causes, the thread 0 is parked in
    its save area with the interrupt's cause, and the scheduler hands the
    thread 1's handle to the switcher, which starts the thread 1 in [D]. *)
Remark cmdc_isolated_demo_preempts :
  ∃ σ1,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_isolated_demo_state)
      ([griotte_lang.Exec], σ1)
    ∧ rr_returning cmdc_isolated_demo_image cmdc_isolated_irq_cause σ1 = true
    ∧ reg σ1 !! ca0 = Some (thread_handle cmdc_isolated_firmware cmdc_isolated_demo_image 1)
    ∧ mem σ1 !! cmdc_isolated_saved_mcause 0 = Some (WInt cmdc_isolated_irq_cause).
Proof.
  assert (cmdc_isolated_irq_cause ∈ irq_causes) as Hcause.
  { rewrite /cmdc_isolated_irq_cause /irq_causes. apply list_elem_of_here. }
  pose proof (machine_run_irq_until_hw_correct
    (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image)) (N.to_nat 12000%N)
    cmdc_isolated_irq_cause
    (rr_returning cmdc_isolated_demo_image cmdc_isolated_irq_cause) (N.to_nat 20000%N)
    cmdc_isolated_demo_state) as Hrun.
  assert (match machine_run_irq_until (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image))
            (N.to_nat 12000%N) cmdc_isolated_irq_cause
            (rr_returning cmdc_isolated_demo_image cmdc_isolated_irq_cause)
            (N.to_nat 20000%N) cmdc_isolated_demo_state with
          | Some σ1 =>
              rr_returning cmdc_isolated_demo_image cmdc_isolated_irq_cause σ1 = true ∧
              bool_decide (reg σ1 !! ca0
                           = Some (thread_handle cmdc_isolated_firmware
                                                 cmdc_isolated_demo_image 1)) = true ∧
              bool_decide (mem σ1 !! cmdc_isolated_saved_mcause 0
                           = Some (WInt cmdc_isolated_irq_cause)) = true
          | None => False
          end) as Hσ1 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_irq_until _ _ _ _ _ _) as [σ1|]; [|done].
  destruct Hσ1 as (Hstop & Hca0 & Hmc0).
  exists σ1. split_and!.
  - by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc0.
Qed.

(** [D]'s [ecall] (thread 1 to thread 0). The thread 1 is parked with the
    cause of an [ecall]; the scheduler hands the thread 0's handle back.
    The thread 0's saved cause is the interrupt's, not an [ecall]'s: the
    switcher resumes it at the instruction the interrupt hit. *)
Remark cmdc_isolated_demo_D_yields :
  ∃ σ2,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_isolated_demo_state)
      ([griotte_lang.Exec], σ2)
    ∧ rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE σ2 = true
    ∧ reg σ2 !! ca0 = Some (thread_handle cmdc_isolated_firmware cmdc_isolated_demo_image 0)
    ∧ mem σ2 !! cmdc_isolated_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ2 !! cmdc_isolated_saved_mcause 0 = Some (WInt cmdc_isolated_irq_cause).
Proof.
  assert (cmdc_isolated_irq_cause ∈ irq_causes) as Hcause.
  { rewrite /cmdc_isolated_irq_cause /irq_causes. apply list_elem_of_here. }
  pose proof (machine_run_irq_until_hw_correct
    (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image)) (N.to_nat 12000%N)
    cmdc_isolated_irq_cause
    (rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE) (N.to_nat 20000%N)
    cmdc_isolated_demo_state) as Hrun.
  assert (match machine_run_irq_until (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image))
            (N.to_nat 12000%N) cmdc_isolated_irq_cause
            (rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE)
            (N.to_nat 20000%N) cmdc_isolated_demo_state with
          | Some σ2 =>
              rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE σ2 = true ∧
              bool_decide (reg σ2 !! ca0
                           = Some (thread_handle cmdc_isolated_firmware
                                                 cmdc_isolated_demo_image 0)) = true ∧
              bool_decide (mem σ2 !! cmdc_isolated_saved_mcause 1
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ2 !! cmdc_isolated_saved_mcause 0
                           = Some (WInt cmdc_isolated_irq_cause)) = true
          | None => False
          end) as Hσ2 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_irq_until _ _ _ _ _ _) as [σ2|]; [|done].
  destruct Hσ2 as (Hstop & Hca0 & Hmc1 & Hmc0).
  exists σ2. split_and!.
  - by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hmc0.
Qed.

(** [B]'s [ecall] (thread 0 to thread 1). The thread 0 is parked with the
    cause of an [ecall]; the scheduler hands the thread 1's handle to the
    switcher, which resumes it after its own [ecall]. *)
Remark cmdc_isolated_demo_B_yields :
  ∃ σ3,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_isolated_demo_state)
      ([griotte_lang.Exec], σ3)
    ∧ rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE σ3 = true
    ∧ reg σ3 !! ca0 = Some (thread_handle cmdc_isolated_firmware cmdc_isolated_demo_image 1)
    ∧ mem σ3 !! cmdc_isolated_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ3 !! cmdc_isolated_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE).
Proof.
  assert (cmdc_isolated_irq_cause ∈ irq_causes) as Hcause.
  { rewrite /cmdc_isolated_irq_cause /irq_causes. apply list_elem_of_here. }
  pose proof (machine_run_irq_until_hw_correct
    (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image)) (N.to_nat 12000%N)
    cmdc_isolated_irq_cause
    (λ φ, rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE φ
          && bool_decide (reg φ !! ca0
                          = Some (thread_handle cmdc_isolated_firmware cmdc_isolated_demo_image 1)))
    (N.to_nat 20000%N)
    cmdc_isolated_demo_state) as Hrun.
  assert (match machine_run_irq_until (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image))
            (N.to_nat 12000%N) cmdc_isolated_irq_cause
            (λ φ, rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE φ
                  && bool_decide (reg φ !! ca0
                                  = Some (thread_handle cmdc_isolated_firmware
                                                        cmdc_isolated_demo_image 1)))
            (N.to_nat 20000%N) cmdc_isolated_demo_state with
          | Some σ3 =>
              rr_returning cmdc_isolated_demo_image MCAUSE_ECALL_MACHINE σ3 = true ∧
              bool_decide (reg σ3 !! ca0
                           = Some (thread_handle cmdc_isolated_firmware
                                                 cmdc_isolated_demo_image 1)) = true ∧
              bool_decide (mem σ3 !! cmdc_isolated_saved_mcause 0
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ3 !! cmdc_isolated_saved_mcause 1
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true
          | None => False
          end) as Hσ3 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_irq_until _ _ _ _ _ _) as [σ3|]; [|done].
  destruct Hσ3 as (Hstop & Hca0 & Hmc0 & Hmc1).
  exists σ3. split_and!.
  - by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hmc1.
Qed.

(** [D]'s exit (thread 1 to thread 0). The thread 1 is parked at the loop
    of an exited thread with the cause of a thread exit; one thread is
    still live, so the scheduler hands the thread 0's handle back, and the
    switcher resumes it after its [ecall]. *)
Remark cmdc_isolated_demo_D_exits :
  ∃ σ4,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_isolated_demo_state)
      ([griotte_lang.Exec], σ4)
    ∧ rr_returning cmdc_isolated_demo_image MCAUSE_THREAD_EXIT σ4 = true
    ∧ reg σ4 !! ca0 = Some (thread_handle cmdc_isolated_firmware cmdc_isolated_demo_image 0)
    ∧ mem σ4 !! cmdc_isolated_saved_mcause 1 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ4 !! cmdc_isolated_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE).
Proof.
  assert (cmdc_isolated_irq_cause ∈ irq_causes) as Hcause.
  { rewrite /cmdc_isolated_irq_cause /irq_causes. apply list_elem_of_here. }
  pose proof (machine_run_irq_until_hw_correct
    (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image)) (N.to_nat 12000%N)
    cmdc_isolated_irq_cause
    (rr_returning cmdc_isolated_demo_image MCAUSE_THREAD_EXIT) (N.to_nat 20000%N)
    cmdc_isolated_demo_state) as Hrun.
  assert (match machine_run_irq_until (pc_at (cmdc_isolated_irq_addr cmdc_isolated_demo_image))
            (N.to_nat 12000%N) cmdc_isolated_irq_cause
            (rr_returning cmdc_isolated_demo_image MCAUSE_THREAD_EXIT)
            (N.to_nat 20000%N) cmdc_isolated_demo_state with
          | Some σ4 =>
              rr_returning cmdc_isolated_demo_image MCAUSE_THREAD_EXIT σ4 = true ∧
              bool_decide (reg σ4 !! ca0
                           = Some (thread_handle cmdc_isolated_firmware
                                                 cmdc_isolated_demo_image 0)) = true ∧
              bool_decide (mem σ4 !! cmdc_isolated_saved_mcause 1
                           = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ4 !! cmdc_isolated_saved_mcause 0
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true
          | None => False
          end) as Hσ4 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_irq_until _ _ _ _ _ _) as [σ4|]; [|done].
  destruct Hσ4 as (Hstop & Hca0 & Hmc1 & Hmc0).
  exists σ4. split_and!.
  - by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hmc0.
Qed.
