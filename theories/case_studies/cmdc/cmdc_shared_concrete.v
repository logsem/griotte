From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  cmdc_shared_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link cmdc_shared_firmware
  round_robin_scheduler_concrete cmdc_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the CMDC firmware with a second thread in [C]

    The CMDC demo's adversary [B], a concrete adversary [C] with two
    exports, and the round-robin scheduler, laid out by the linker. Its
    initial state satisfies [cmdc_shared_initial_state_ok] by computation.
    The thread 0 yields in [B]; the thread 1 yields at its start in [C];
    the thread 0 calls [C.g], which keeps the capability to [c] in the
    global of [C], and exits; the thread 1 writes [c] through that
    capability and exits; the scheduler halts the machine.
    [cmdc_shared_adequacy] applies to the run. *)

(** The adversary [C]. Its export [g] keeps the capability it receives in
    its global and writes [9] through it; its export [adv], the entry of
    the thread 1, yields once, then writes [13] through the capability in
    its global and exits. One zeroed global; [g] right after the import,
    [adv] after [g]. *)
Definition cmdc_shared_C_code : list Word :=
  encodeInstrsW [
    (* g *)
    Store cgp ca0 0;
    Store ca0 9%Z 0;
    Jalr cnull cra;
    (* adv *)
    Ecall;
    CLoad ct0 cgp 0%Z;
    Store ct0 13%Z 0;
    Jalr cnull cra
  ].

(** The offsets of [g] and [adv] in the PCC range of [C]. *)
Definition cmdc_shared_C_g_offset : nat := 1.
Definition cmdc_shared_C_adv_offset : nat := 4.

(** [B] is the CMDC demo's adversary ([cmdc_concrete]). *)
Definition cmdc_shared_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 cmdc_switcher_sealing_type [
    ("B", {| la_code    := cmdc_B_code;
             la_data    := cmdc_B_data;
             la_exports := [
               1  (* after the import *)
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |});
    ("C", {| la_code    := cmdc_shared_C_code;
             la_data    := cmdc_C_data;
             la_exports := [
               cmdc_shared_C_g_offset;
               cmdc_shared_C_adv_offset
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 cmdc_shared_firmware.

(** ** The linked image and its initial state *)

Definition cmdc_shared_demo_image : fw_image :=
  Eval vm_compute in
    default (place cmdc_shared_demo_link_cfg cmdc_shared_firmware).1
      (link cmdc_shared_demo_link_cfg cmdc_shared_firmware).

Lemma cmdc_shared_demo_linked :
  link cmdc_shared_demo_link_cfg cmdc_shared_firmware = Some cmdc_shared_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition cmdc_shared_demo_state : ExecConf :=
  img_state cmdc_shared_firmware cmdc_shared_demo_image.

(** The entry word of [adv], as the linker writes it: no argument, no
    minimum stack, at [adv]'s offset. *)
Definition cmdc_shared_C_adv_word : Z :=
  encode_entry_point InterruptEnabled 0 0 (Z.of_nat cmdc_shared_C_adv_offset).

Lemma cmdc_shared_demo_ok :
  cmdc_shared_initial_state_ok (flag_assert (img_asrt cmdc_shared_demo_image))
    cmdc_shared_demo_state.
Proof.
  rewrite /cmdc_shared_initial_state_ok.
  exists (img_sw cmdc_shared_demo_image), (img_asrt cmdc_shared_demo_image),
    (thread_of cmdc_shared_demo_image 0), (thread_of cmdc_shared_demo_image 1),
    (img_idle cmdc_shared_demo_image), (img_boot cmdc_shared_demo_image),
    (cmpt_of cmdc_shared_demo_image "main"), (cmpt_of cmdc_shared_demo_image "B"),
    (cmpt_of cmdc_shared_demo_image "C"), (cmpt_of cmdc_shared_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers cmdc_shared_demo_link_cfg.
  (* The two exports of [C], then the one of [B] *)
  all: try (exists cmdc_shared_C_g_offset, 0%nat; split;
            [|exists cmdc_shared_C_adv_offset, 0%nat; split_and!]).
  all: try (exists 1%nat, 0%nat; split_and!).
  (* The entry word of [adv]: the PC and the minimum stack of the thread 1 *)
  all: try (lazymatch goal with
            | |- ∃ z : Z, cmpt_exp_tbl_entries _ !! _ = Some (WInt z) ∧ _ =>
                exists cmdc_shared_C_adv_word; split
            end).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /cmdc_shared_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [cmdc_shared_demo_state] starts at the switcher's call of the
    scheduler, which resumes the thread 0 in [main]. In [B] it yields; the
    thread 1 starts in [C] at [adv] and yields; the thread 0 resumes in
    [B], returns to [main], calls [C.g] and exits; the thread 1 resumes,
    writes [c] and exits; the scheduler halts the machine.
    [cmdc_shared_adequacy] applies to the run: the flag of the assert
    library is still zero. *)
Theorem cmdc_shared_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_shared_demo_state)
      ([Instr Halted], σ')
    ∧ mem σ' !! flag_assert (img_asrt cmdc_shared_demo_image) = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 20000%N) cmdc_shared_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (cmdc_shared_adequacy _ _ _ _ cmdc_shared_demo_ok Hrun).
Qed.

(** Where the switcher saves the cause of the thread [i]'s last trap. *)
Definition cmdc_shared_saved_mcause (i : nat) : Addr :=
  (b_trusted_stack (thread_of cmdc_shared_demo_image i) ^+ TrustedStack_offset_mcause)%a.

(** The globals [b] and [c] of [main]. *)
Definition cmdc_shared_b_addr : Addr := cmpt_b_cgp (cmpt_of cmdc_shared_demo_image "main").
Definition cmdc_shared_c_addr : Addr :=
  (cmpt_b_cgp (cmpt_of cmdc_shared_demo_image "main") ^+ 1)%a.

(** The last instruction of [C.adv], the exit of the thread 1. *)
Definition cmdc_shared_adv_exit_addr : Addr :=
  (cmpt_b_pcc (cmpt_of cmdc_shared_demo_image "C") ^+ 7)%a.

(** The scheduler is about to return from a call with cause [c], handing
    the thread [i] back. *)
Definition cmdc_shared_returning (c : Z) (i : nat) (φ : ExecConf) : bool :=
  rr_returning cmdc_shared_demo_image c φ &&
  bool_decide (reg φ !! ca0 = Some (thread_handle cmdc_shared_firmware cmdc_shared_demo_image i)).

(** The yield in [B.f] (thread 0 to thread 1): [B] has written [7] into
    [b]; the thread 0 is parked with the cause of an [ecall]. *)
Remark cmdc_shared_demo_B_yields :
  ∃ σ1,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_shared_demo_state)
      ([griotte_lang.Exec], σ1)
    ∧ cmdc_shared_returning MCAUSE_ECALL_MACHINE 1 σ1 = true
    ∧ mem σ1 !! cmdc_shared_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ1 !! cmdc_shared_b_addr = Some (WInt 7%Z).
Proof.
  pose proof (machine_run_until_correct (cmdc_shared_returning MCAUSE_ECALL_MACHINE 1)
    (N.to_nat 20000%N) Executable cmdc_shared_demo_state) as Hrun.
  assert (match machine_run_until (cmdc_shared_returning MCAUSE_ECALL_MACHINE 1)
            (N.to_nat 20000%N) (Executable, cmdc_shared_demo_state) with
          | Some σ1 =>
              cmdc_shared_returning MCAUSE_ECALL_MACHINE 1 σ1 = true ∧
              bool_decide (mem σ1 !! cmdc_shared_saved_mcause 0
                             = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ1 !! cmdc_shared_b_addr = Some (WInt 7%Z)) = true
          | None => False
          end) as Hσ1 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ1|]; [|done].
  destruct Hσ1 as (Hstop & Hmc0 & Hb).
  exists σ1. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hb.
Qed.

(** The yield of the thread 1 at its start in [C] (thread 1 to thread 0):
    the ring wraps around to the thread 0, parked in [B.f]. *)
Remark cmdc_shared_demo_C_yields :
  ∃ σ2,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_shared_demo_state)
      ([griotte_lang.Exec], σ2)
    ∧ cmdc_shared_returning MCAUSE_ECALL_MACHINE 0 σ2 = true
    ∧ mem σ2 !! cmdc_shared_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ2 !! cmdc_shared_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE).
Proof.
  pose proof (machine_run_until_correct (cmdc_shared_returning MCAUSE_ECALL_MACHINE 0)
    (N.to_nat 20000%N) Executable cmdc_shared_demo_state) as Hrun.
  assert (match machine_run_until (cmdc_shared_returning MCAUSE_ECALL_MACHINE 0)
            (N.to_nat 20000%N) (Executable, cmdc_shared_demo_state) with
          | Some σ2 =>
              cmdc_shared_returning MCAUSE_ECALL_MACHINE 0 σ2 = true ∧
              bool_decide (mem σ2 !! cmdc_shared_saved_mcause 1
                             = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ2 !! cmdc_shared_saved_mcause 0
                             = Some (WInt MCAUSE_ECALL_MACHINE)) = true
          | None => False
          end) as Hσ2 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ2|]; [|done].
  destruct Hσ2 as (Hstop & Hmc1 & Hmc0).
  exists σ2. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hmc0.
Qed.

(** The exit of the thread 0 (thread 0 to thread 1): one thread is still
    live; [main] has written [42] into [b] and [C.g] has written [9] into
    [c]. *)
Remark cmdc_shared_demo_main_exits :
  ∃ σ3,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_shared_demo_state)
      ([griotte_lang.Exec], σ3)
    ∧ cmdc_shared_returning MCAUSE_THREAD_EXIT 1 σ3 = true
    ∧ mem σ3 !! cmdc_shared_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ3 !! cmdc_shared_b_addr = Some (WInt 42%Z)
    ∧ mem σ3 !! cmdc_shared_c_addr = Some (WInt 9%Z).
Proof.
  pose proof (machine_run_until_correct (cmdc_shared_returning MCAUSE_THREAD_EXIT 1)
    (N.to_nat 20000%N) Executable cmdc_shared_demo_state) as Hrun.
  assert (match machine_run_until (cmdc_shared_returning MCAUSE_THREAD_EXIT 1)
            (N.to_nat 20000%N) (Executable, cmdc_shared_demo_state) with
          | Some σ3 =>
              cmdc_shared_returning MCAUSE_THREAD_EXIT 1 σ3 = true ∧
              bool_decide (mem σ3 !! cmdc_shared_saved_mcause 0
                             = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ3 !! cmdc_shared_b_addr = Some (WInt 42%Z)) = true ∧
              bool_decide (mem σ3 !! cmdc_shared_c_addr = Some (WInt 9%Z)) = true
          | None => False
          end) as Hσ3 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ3|]; [|done].
  destruct Hσ3 as (Hstop & Hmc0 & Hb & Hc).
  exists σ3. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hb.
  - by apply bool_decide_eq_true_1 in Hc.
Qed.

(** The exit of the thread 1: through what [C.g] kept, [C] has written [13]
    into [c]; [b] still holds [42]. The thread 0 has exited by then, and
    [c] held [9] at its exit ([cmdc_shared_demo_main_exits]): the write
    comes after it. *)
Remark cmdc_shared_demo_C_writes_c :
  ∃ σ4,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], cmdc_shared_demo_state)
      ([griotte_lang.Exec], σ4)
    ∧ pc_at cmdc_shared_adv_exit_addr σ4 = true
    ∧ mem σ4 !! cmdc_shared_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ4 !! cmdc_shared_c_addr = Some (WInt 13%Z)
    ∧ mem σ4 !! cmdc_shared_b_addr = Some (WInt 42%Z).
Proof.
  pose proof (machine_run_until_correct (pc_at cmdc_shared_adv_exit_addr)
    (N.to_nat 20000%N) Executable cmdc_shared_demo_state) as Hrun.
  assert (match machine_run_until (pc_at cmdc_shared_adv_exit_addr)
            (N.to_nat 20000%N) (Executable, cmdc_shared_demo_state) with
          | Some σ4 =>
              pc_at cmdc_shared_adv_exit_addr σ4 = true ∧
              bool_decide (mem σ4 !! cmdc_shared_saved_mcause 0
                           = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ4 !! cmdc_shared_c_addr = Some (WInt 13%Z)) = true ∧
              bool_decide (mem σ4 !! cmdc_shared_b_addr = Some (WInt 42%Z)) = true
          | None => False
          end) as Hσ4 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ4|]; [|done].
  destruct Hσ4 as (Hstop & Hmc0 & Hc & Hb).
  exists σ4. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hc.
  - by apply bool_decide_eq_true_1 in Hb.
Qed.
