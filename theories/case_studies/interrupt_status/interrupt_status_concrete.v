From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  interrupt_status interrupt_status_adequacy.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link ist_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the interrupt-status case study

    The interrupt-status firmware with a concrete adversary [B] and the
    round-robin scheduler, laid out by the linker. Its initial state
    satisfies [ist_initial_state_ok] by computation. From it the thread 0
    calls [B.f] with interrupts disabled; [B.f] keeps the capability to [b]
    and yields; the thread 1 writes [13] into [b] through it and exits; the
    thread 0 resumes, returns to [K] with interrupts disabled, writes [42],
    asserts and exits, and the scheduler halts the machine. [ist_adequacy]
    applies to the run. *)

Definition ist_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.

(** The concrete adversary. Its export [f] keeps the capability it receives
    in its global, then yields once and returns. Its export [adv], the
    entry of the thread 1, takes that capability from the global, writes
    [13] through it, and returns, which exits the thread. One zeroed
    global; [f] right after the import, [adv] after [f]. *)
Definition ist_B_code : list Word :=
  encodeInstrsW [
    Store cgp ca0 0%Z;
    Ecall;
    Jalr cnull cra;
    CLoad ct0 cgp 0%Z;
    Store ct0 13%Z 0%Z;
    Jalr cnull cra
  ].
Definition ist_B_data : list Word := [WInt 0].

(** The offsets of [f] and [adv] in the PCC range of [B]. *)
Definition ist_B_f_offset : nat := 1.
Definition ist_B_adv_offset : nat := 4.

Definition ist_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 ist_switcher_sealing_type [
    ("B", {| la_code    := ist_B_code;
             la_data    := ist_B_data;
             la_exports := [
               ist_B_f_offset;
               ist_B_adv_offset
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 ist_firmware.

(** ** The linked image and its initial state *)

Definition ist_demo_image : fw_image :=
  Eval vm_compute in
    default (place ist_demo_link_cfg ist_firmware).1
      (link ist_demo_link_cfg ist_firmware).

Lemma ist_demo_linked :
  link ist_demo_link_cfg ist_firmware = Some ist_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition ist_demo_state : ExecConf := img_state ist_firmware ist_demo_image.

(** The entry word of [adv], as the linker writes it: no argument, no
    minimum stack, at [adv]'s offset. *)
Definition ist_B_adv_word : Z :=
  encode_entry_point InterruptEnabled 0 0 (Z.of_nat ist_B_adv_offset).

Lemma ist_demo_ok :
  ist_initial_state_ok (img_flag ist_demo_image) ist_demo_state.
Proof.
  rewrite /ist_initial_state_ok.
  exists (img_sw ist_demo_image), (lib_of ist_demo_image "assert"),
    (shared_of ist_demo_image "assert_flag"),
    (thread_of ist_demo_image 0), (thread_of ist_demo_image 1),
    (img_idle ist_demo_image), (img_boot ist_demo_image),
    (cmpt_of ist_demo_image "K"), (cmpt_of ist_demo_image "B"),
    (cmpt_of ist_demo_image "sched").
  split; first done.
  split_and!.
  (* The error handler offsets of the adversary, as the configuration gives them. *)
  all: try exists_adv_handlers ist_demo_link_cfg.
  all: try (exists ist_B_f_offset, 0%nat; split; [|exists ist_B_adv_offset, 0%nat; split_and!]).
  (* The entry word of [adv]: the PC and the minimum stack of the thread 1 *)
  all: try (lazymatch goal with
            | |- ∃ z : Z, cmpt_exp_tbl_entries _ !! _ = Some (WInt z) ∧ _ =>
                exists ist_B_adv_word; split
            end).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /ist_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run

    [ist_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread 0 in [K], with interrupts disabled. In [B.f] the
    thread 0 yields by an [ecall]: the switcher parks it and calls the
    scheduler, which starts the thread 1 in [B]. The thread 1 writes [13]
    into [b] and exits; the scheduler resumes the thread 0 after its
    [ecall]; [B.f] returns, and [K], with interrupts disabled again, writes
    [42], asserts, and returns, which exits the thread; the scheduler halts
    the machine. [ist_adequacy] applies to the run: the flag of the assert
    library is still zero. *)
Theorem ist_runs_and_gracefully_halts :
  ∃ σ',
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], ist_demo_state) ([Instr Halted], σ')
    ∧ mem σ' !! img_flag ist_demo_image = Some (WInt 0%Z).
Proof.
  pose proof (machine_run_hw_correct (N.to_nat 16500%N) ist_demo_state Halted) as Hrun.
  specialize (Hrun ltac:(vm_compute; reflexivity)).
  destruct Hrun as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (ist_adequacy _ _ _ _ ist_demo_ok Hrun).
Qed.

(** Where the switcher saves the cause of the thread [i]'s last trap. *)
Definition ist_saved_mcause (i : nat) : Addr :=
  (b_trusted_stack (thread_of ist_demo_image i) ^+ TrustedStack_offset_mcause)%a.

(** The global [b] of [K]. *)
Definition ist_b_addr : Addr := cmpt_b_cgp (cmpt_of ist_demo_image "K").

(** Where [K] writes [42]. *)
Definition ist_overwrite_addr : Addr :=
  (cmpt_b_pcc (cmpt_of ist_demo_image "K")
     ^+ Z.of_nat (assembler.Asm_Griotte.label_offset (concat ist_K_asm) ".Lstatus_overwrite"))%a.

(** The yield in [B.f] (thread 0 to thread 1). The thread 0 is parked with
    the cause of an [ecall], inside [B.f]; the scheduler hands the thread
    1's handle to the switcher, which starts the thread 1 in [B]. *)
Remark ist_demo_f_yields :
  ∃ σ1,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], ist_demo_state)
      ([griotte_lang.Exec], σ1)
    ∧ rr_returning ist_demo_image MCAUSE_ECALL_MACHINE σ1 = true
    ∧ reg σ1 !! ca0 = Some (thread_handle ist_firmware ist_demo_image 1)
    ∧ mem σ1 !! ist_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE).
Proof.
  pose proof (machine_run_until_correct (rr_returning ist_demo_image MCAUSE_ECALL_MACHINE)
    (N.to_nat 16500%N) Executable ist_demo_state) as Hrun.
  assert (match machine_run_until (rr_returning ist_demo_image MCAUSE_ECALL_MACHINE)
            (N.to_nat 16500%N) (Executable, ist_demo_state) with
          | Some σ1 =>
              rr_returning ist_demo_image MCAUSE_ECALL_MACHINE σ1 = true ∧
              bool_decide (reg σ1 !! ca0 = Some (thread_handle ist_firmware ist_demo_image 1))
                = true ∧
              bool_decide (mem σ1 !! ist_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE))
                = true
          | None => False
          end) as Hσ1 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ1|]; [|done].
  destruct Hσ1 as (Hstop & Hca0 & Hmc0).
  exists σ1. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc0.
Qed.

(** The exit of the thread 1 (thread 1 to thread 0). The thread 1 has
    written [13] into [b], through the capability [B.f] kept, and is parked
    at the loop of an exited thread with the cause of a thread exit; one
    thread is still live, so the scheduler hands the thread 0's handle back,
    and the switcher resumes it after its [ecall] in [B.f]. *)
Remark ist_demo_adv_exits :
  ∃ σ2,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], ist_demo_state)
      ([griotte_lang.Exec], σ2)
    ∧ rr_returning ist_demo_image MCAUSE_THREAD_EXIT σ2 = true
    ∧ reg σ2 !! ca0 = Some (thread_handle ist_firmware ist_demo_image 0)
    ∧ mem σ2 !! ist_saved_mcause 1 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ2 !! ist_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ2 !! ist_b_addr = Some (WInt 13%Z).
Proof.
  pose proof (machine_run_until_correct (rr_returning ist_demo_image MCAUSE_THREAD_EXIT)
    (N.to_nat 16500%N) Executable ist_demo_state) as Hrun.
  assert (match machine_run_until (rr_returning ist_demo_image MCAUSE_THREAD_EXIT)
            (N.to_nat 16500%N) (Executable, ist_demo_state) with
          | Some σ2 =>
              rr_returning ist_demo_image MCAUSE_THREAD_EXIT σ2 = true ∧
              bool_decide (reg σ2 !! ca0 = Some (thread_handle ist_firmware ist_demo_image 0))
                = true ∧
              bool_decide (mem σ2 !! ist_saved_mcause 1 = Some (WInt MCAUSE_THREAD_EXIT))
                = true ∧
              bool_decide (mem σ2 !! ist_saved_mcause 0 = Some (WInt MCAUSE_ECALL_MACHINE))
                = true ∧
              bool_decide (mem σ2 !! ist_b_addr = Some (WInt 13%Z)) = true
          | None => False
          end) as Hσ2 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ2|]; [|done].
  destruct Hσ2 as (Hstop & Hca0 & Hmc1 & Hmc0 & Hb).
  exists σ2. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hca0.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hb.
Qed.

(** [K]'s write of [42] (the thread 0, back from [B.f]). When the PC first
    reaches it, interrupts are disabled, so the hardware takes no interrupt
    there, and [b] still holds the [13] of the thread 1. *)
Remark ist_demo_overwrite_disabled :
  ∃ σ3,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], ist_demo_state)
      ([griotte_lang.Exec], σ3)
    ∧ pc_at ist_overwrite_addr σ3 = true
    ∧ mie_of (get_a (sreg_word σ3 mstatus)) = InterruptDisabled
    ∧ mem σ3 !! ist_b_addr = Some (WInt 13%Z).
Proof.
  pose proof (machine_run_until_correct (pc_at ist_overwrite_addr)
    (N.to_nat 16500%N) Executable ist_demo_state) as Hrun.
  assert (match machine_run_until (pc_at ist_overwrite_addr)
            (N.to_nat 16500%N) (Executable, ist_demo_state) with
          | Some σ3 =>
              pc_at ist_overwrite_addr σ3 = true ∧
              bool_decide (mie_of (get_a (sreg_word σ3 mstatus)) = InterruptDisabled) = true ∧
              bool_decide (mem σ3 !! ist_b_addr = Some (WInt 13%Z)) = true
          | None => False
          end) as Hσ3 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_until _ _ _) as [σ3|]; [|done].
  destruct Hσ3 as (Hstop & Hmie & Hb).
  exists σ3. split_and!.
  - apply rtc_erased_step_hw. by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmie.
  - by apply bool_decide_eq_true_1 in Hb.
Qed.
