From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  thread_synchronisation_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link tsy_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the thread-synchronisation case study

    The thread-synchronisation firmware with a concrete adversary [B] and
    the round-robin scheduler, laid out by the linker. Its initial state
    satisfies [tsy_initial_state_ok] by computation. From it the thread 0
    calls [B.f]; [B.f] writes [7] into [b] and yields; the thread 1 reads
    [flag = 0] and yields; the thread 0 resumes in [B.f], returns to [K],
    sets [flag] and exits; the thread 1 resumes, reads [flag = 1], writes
    [42] into [b], asserts and exits, and the scheduler halts the machine.
    [tsy_adequacy] applies to the run. *)

Definition tsy_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary. Its export [f] writes [7] through the
    capability it receives, yields once and returns. One zeroed global;
    [f] right after the import. *)
Definition tsy_B_code : list Word :=
  encodeInstrsW [
    Store ca0 7%Z 0%Z;
    Ecall;
    Jalr cnull cra
  ].
Definition tsy_B_data : list Word := [WInt 0].

(** The offset of [f] in the PCC range of [B]. *)
Definition tsy_B_f_offset : nat := 1.

Definition tsy_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 tsy_switcher_sealing_type [
    ("B", {| la_code    := tsy_B_code;
             la_data    := tsy_B_data;
             la_exports := [
               tsy_B_f_offset
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 tsy_firmware.

(** ** The linked image and its initial state *)

Definition tsy_demo_image : fw_image :=
  Eval vm_compute in
    default (place tsy_demo_link_cfg tsy_firmware).1
      (link tsy_demo_link_cfg tsy_firmware).

Lemma tsy_demo_linked :
  link tsy_demo_link_cfg tsy_firmware = Some tsy_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition tsy_demo_state : ExecConf := img_state tsy_firmware tsy_demo_image.

Lemma tsy_demo_ok :
  tsy_initial_state_ok (img_flag tsy_demo_image) tsy_demo_state.
Proof.
  rewrite /tsy_initial_state_ok.
  exists (img_sw tsy_demo_image), (lib_of tsy_demo_image "assert"),
    (shared_of tsy_demo_image "assert_flag"),
    (thread_of tsy_demo_image 0), (thread_of tsy_demo_image 1),
    (img_idle tsy_demo_image), (img_boot tsy_demo_image),
    (cmpt_of tsy_demo_image "K"), (cmpt_of tsy_demo_image "B"),
    (cmpt_of tsy_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversary, as the configuration gives them. *)
  all: try exists_adv_handlers tsy_demo_link_cfg.
  all: try (exists tsy_B_f_offset, 0%nat; split_and!).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /tsy_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [tsy_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread 0 in [K.run1]. In [B.f] the thread 0 yields; the
    scheduler starts the thread 1 in [K.run2], which reads [flag = 0] and
    yields; the thread 0 resumes in [B.f], returns to [K], sets [flag] and
    exits; the scheduler resumes the thread 1, which reads [flag = 1],
    writes and asserts [b], and exits; the scheduler halts the machine.
    [tsy_adequacy] applies to the run: the flag of the assert library is
    still zero. *)
Theorem tsy_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], tsy_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! img_flag tsy_demo_image = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 20000%N) tsy_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (tsy_adequacy _ _ _ _ tsy_demo_ok Hrun).
Qed.

(** Where the switcher saves the cause of the thread [i]'s last trap. *)
Definition tsy_saved_mcause (i : nat) : Addr :=
  (b_trusted_stack (thread_of tsy_demo_image i) ^+ TrustedStack_offset_mcause)%a.

(** The globals [b] and [flag] of [K]. *)
Definition tsy_b_addr : Addr := cmpt_b_cgp (cmpt_of tsy_demo_image "K").
Definition tsy_flag_addr : Addr := (cmpt_b_cgp (cmpt_of tsy_demo_image "K") ^+ 1)%a.

(** Where the thread 1 writes [42]. *)
Definition tsy_go_addr : Addr :=
  (cmpt_b_pcc (cmpt_of tsy_demo_image "K")
     ^+ Z.of_nat (assembler.Asm_Griotte.label_offset (concat tsy_K_asm) ".Lsync_go"))%a.

(** The scheduler is about to return from a yield, handing the thread [i]
    back. *)
Definition tsy_yield_returning (i : nat) (φ : ExecConf) : bool :=
  rr_returning tsy_demo_image MCAUSE_ECALL_MACHINE φ &&
  bool_decide (reg φ !! ca0 = Some (thread_handle tsy_firmware tsy_demo_image i)).

(** The yield in [B.f] (thread 0 to thread 1). [B] has written [7] into
    [b]; the thread 0 is parked with the cause of an [ecall]; the scheduler
    hands the thread 1's handle to the switcher, which starts it in
    [K.run2]. *)
Remark tsy_demo_f_yields :
  ∃ σ1,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], tsy_demo_state)
      ([griotte_lang.Exec], σ1)
    ∧ tsy_yield_returning 1 σ1 = true
    ∧ mem σ1 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ1 !! tsy_b_addr = Some (WInt 7%Z).
Proof.
  pose proof (machine_run_until_correct (tsy_yield_returning 1)
    (N.to_nat 20000%N) Executable tsy_demo_state) as Hrun.
  assert (match machine_run_until (tsy_yield_returning 1)
            (N.to_nat 20000%N) (Executable, tsy_demo_state) with
          | Some σ1 =>
              tsy_yield_returning 1 σ1 = true ∧
              bool_decide (mem σ1 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ1 !! tsy_b_addr = Some (WInt 7%Z)) = true
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

(** The yield of the thread 1 (thread 1 to thread 0). The thread 1 has
    read [flag = 0] and is parked with the cause of an [ecall]; the
    scheduler hands the thread 0's handle back. *)
Remark tsy_demo_run2_yields :
  ∃ σ2,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], tsy_demo_state)
      ([griotte_lang.Exec], σ2)
    ∧ tsy_yield_returning 0 σ2 = true
    ∧ mem σ2 !! tsy_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ2 !! tsy_flag_addr = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_until_correct (tsy_yield_returning 0)
    (N.to_nat 20000%N) Executable tsy_demo_state) as Hrun.
  assert (match machine_run_until (tsy_yield_returning 0)
            (N.to_nat 20000%N) (Executable, tsy_demo_state) with
          | Some σ2 =>
              tsy_yield_returning 0 σ2 = true ∧
              bool_decide (mem σ2 !! tsy_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ2 !! tsy_flag_addr = Some (WInt 0%Z)) = true
          | None => False
          end) as Hσ2 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ2|]; [|done].
  destruct Hσ2 as (Hstop & Hmc1 & Hflag).
  exists σ2. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hflag.
Qed.

(** The exit of the thread 0 (thread 0 to thread 1). The thread 0 has set
    [flag] and is parked with the cause of a thread exit; one thread is
    still live, so the scheduler hands the thread 1's handle back. *)
Remark tsy_demo_run1_exits :
  ∃ σ3,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], tsy_demo_state)
      ([griotte_lang.Exec], σ3)
    ∧ rr_returning tsy_demo_image MCAUSE_THREAD_EXIT σ3 = true
    ∧ reg σ3 !! ca0 = Some (thread_handle tsy_firmware tsy_demo_image 1)
    ∧ mem σ3 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ3 !! tsy_flag_addr = Some (WInt 1%Z).
Proof.
  pose proof (machine_run_until_correct (rr_returning tsy_demo_image MCAUSE_THREAD_EXIT)
    (N.to_nat 20000%N) Executable tsy_demo_state) as Hrun.
  assert (match machine_run_until (rr_returning tsy_demo_image MCAUSE_THREAD_EXIT)
            (N.to_nat 20000%N) (Executable, tsy_demo_state) with
          | Some σ3 =>
              rr_returning tsy_demo_image MCAUSE_THREAD_EXIT σ3 = true ∧
              bool_decide (reg σ3 !! ca0 = Some (thread_handle tsy_firmware tsy_demo_image 1)) = true ∧
              bool_decide (mem σ3 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ3 !! tsy_flag_addr = Some (WInt 1%Z)) = true
          | None => False
          end) as Hσ3 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ3|]; [|done].
  destruct Hσ3 as (Hstop & Hca0 & Hmc0 & Hflag).
  exists σ3. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hflag.
Qed.

(** The thread 1's write of [42]. When the PC first reaches it, [flag] is
    [1], the thread 0 has exited, and [b] still holds [B]'s [7]. *)
Remark tsy_demo_go :
  ∃ σ4,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], tsy_demo_state)
      ([griotte_lang.Exec], σ4)
    ∧ pc_at tsy_go_addr σ4 = true
    ∧ mem σ4 !! tsy_flag_addr = Some (WInt 1%Z)
    ∧ mem σ4 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ4 !! tsy_b_addr = Some (WInt 7%Z).
Proof.
  pose proof (machine_run_until_correct (pc_at tsy_go_addr)
    (N.to_nat 20000%N) Executable tsy_demo_state) as Hrun.
  assert (match machine_run_until (pc_at tsy_go_addr)
            (N.to_nat 20000%N) (Executable, tsy_demo_state) with
          | Some σ4 =>
              pc_at tsy_go_addr σ4 = true ∧
              bool_decide (mem σ4 !! tsy_flag_addr = Some (WInt 1%Z)) = true ∧
              bool_decide (mem σ4 !! tsy_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ4 !! tsy_b_addr = Some (WInt 7%Z)) = true
          | None => False
          end) as Hσ4 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ4|]; [|done].
  destruct Hσ4 as (Hstop & Hflag & Hmc0 & Hb).
  exists σ4. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hflag.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hb.
Qed.
