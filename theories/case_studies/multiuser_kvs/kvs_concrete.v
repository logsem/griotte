From stdpp Require Import gmap strings.
From iris.program_logic Require Import language.
From griotte Require Import
  machine_base machine_parameters machine_parameters_instance griotte_opsem griotte_lang
  hw_lang hw_machine_run switcher assert allocator_resources compartment_layout
  kvs kvs_main kvs_adequacy.
From griotte Require assembler.
(* Imported last: the fields of the image records. *)
From griotte Require Import image firmware firmware_ok image_state link kvs_firmware
  round_robin_scheduler_concrete.

#[export] Existing Instance machine_parameters_instance.
#[local] Transparent MemNum ONum.
#[local] Open Scope string_scope.

(** * A concrete instance of the KVS case study

    The KVS firmware with concrete sealing types and user keys, a concrete
    adversary [B] and the round-robin scheduler, laid out by the linker.
    Its initial state satisfies [kvs_initial_state_ok] by computation. From
    it two threads call the service: the thread 0 in [main], then in [B]
    through [main]'s call of [B.f], and the thread 1 in [B] from its export
    [adv]. An interrupt hits the thread 0 while it holds the lock of the
    service; the thread 1 then finds the lock taken and yields, and takes
    it once the thread 0 has exited; the scheduler halts the machine.
    [kvs_adequacy] applies to the run. *)

Definition kvs_switcher_sealing_type : OType := @finz.FinZ ONum 9 eq_refl eq_refl.
Definition kvs_service_sealing_type : OType := @finz.FinZ ONum 11 eq_refl eq_refl.

(** The firmware, with the user keys [1] (main) and [2] (B). *)
Definition kvs_demo_firmware : firmware := kvs_firmware kvs_service_sealing_type 1 2.

(** The adversary [B]: the code of [kvs_B_asm], one zeroed global, and its
    two exports [f] and [adv], both at the routine's entry. *)
Definition kvs_B_code : list Word := encodeInstrsW kvs_B_instrs.
Definition kvs_B_data : list Word := [WInt 0].

Definition kvs_demo_link_cfg : link_cfg :=
  rr_link_cfg 16 kvs_switcher_sealing_type [
    ("B", {| la_code    := kvs_B_code;
             la_data    := kvs_B_data;
             la_exports := [
               kvs_B_adv_entry;
               kvs_B_adv_entry
             ];
             la_handler := ExportTable_no_handler;
             la_handler_stackless := ExportTable_no_handler |})
  ] 16 kvs_demo_firmware.

(** ** The linked image and its initial state *)

Definition kvs_demo_image : fw_image :=
  Eval vm_compute in
    default (place kvs_demo_link_cfg kvs_demo_firmware).1
      (link kvs_demo_link_cfg kvs_demo_firmware).

Lemma kvs_demo_linked :
  link kvs_demo_link_cfg kvs_demo_firmware = Some kvs_demo_image.
Proof. vm_compute; reflexivity. Qed.

Definition kvs_demo_state : ExecConf := img_state kvs_demo_firmware kvs_demo_image.

(** The entry word of [adv], as the linker writes it: no argument, no
    minimum stack, at the routine's entry. *)
Definition kvs_B_adv_word : Z :=
  encode_entry_point InterruptEnabled 0 0 (Z.of_nat kvs_B_adv_entry).

Lemma kvs_demo_ok :
  kvs_initial_state_ok (img_flag kvs_demo_image) kvs_demo_state.
Proof.
  rewrite /kvs_initial_state_ok.
  exists (img_sw kvs_demo_image), (img_asrt kvs_demo_image), (img_lck kvs_demo_image),
    (thread_of kvs_demo_image 0), (thread_of kvs_demo_image 1),
    (img_idle kvs_demo_image), (img_boot kvs_demo_image),
    (cmpt_of kvs_demo_image "main"), (cmpt_of kvs_demo_image "kvs"), (cmpt_of kvs_demo_image "B"),
    (cmpt_of kvs_demo_image "sched"), kvs_service_sealing_type, 1%Z, 2%Z.
  split; first done.
  split_and!.
  (* The error handler offsets of the adversaries, as the configuration gives them. *)
  all: try exists_adv_handlers kvs_demo_link_cfg.
  (* The two exports of [B] *)
  all: try (exists kvs_B_adv_entry, 0%nat; split; [|exists kvs_B_adv_entry, 0%nat; split_and!]).
  (* The entry word of [adv]: the PC and the minimum stack of the thread 1 *)
  all: try (lazymatch goal with
            | |- ∃ z : Z, cmpt_exp_tbl_entries _ !! _ = Some (WInt z) ∧ _ =>
                exists kvs_B_adv_word; split
            end).
  all: try (lazymatch goal with
            | |- ∃ _ _ _ : Z, _ => exists 0%Z, 0%Z, 0%Z; split_and!
            end).
  all: try (lazymatch goal with
            | |- ∃ _ : InterruptStatus, _ => exists InterruptEnabled
            end).
  all: try (lazymatch goal with
            | |- ∀ r, _ => rewrite /kvs_demo_state /img_state /img_regs;
                           solve_start_other_registers
            end).
  all: solve_concrete_condition.
Qed.

(** ** The run *)

(** The interrupt of the run: the machine timer's. The hardware takes an
    interrupt whenever interrupts are enabled, whatever the timer devices
    hold; in this run [mtime] stays [0], below the threshold the scheduler
    programs. *)
Definition kvs_irq_cause : Z := (MCAUSE_INTR + MCAUSE_MTIME)%Z.

#[local] Lemma kvs_irq_cause_in : kvs_irq_cause ∈ irq_causes.
Proof. rewrite /kvs_irq_cause /irq_causes. apply list_elem_of_here. Qed.

(** Where the interrupt hits the thread 0: [addOrUpdate]'s restriction of
    [cgp] to the table, right after [acquire] has taken the lock, with
    interrupts enabled. *)
Definition kvs_irq_addr (img : fw_image) : Addr :=
  (cmpt_b_pcc (cmpt_of img "kvs")
     ^+ Z.of_nat (assembler.Asm_Griotte.label_offset (concat kvs_service_asm)
                    ".LaddOrUpdate_table"))%a.

(** [kvs_demo_state] starts at the switcher's call of the scheduler, which
    resumes the thread 0 in [main]. [main] calls [addOrUpdate], whose
    [acquire] takes the lock; the run stops right after it, where
    interrupts are enabled, and takes an interrupt there: the switcher
    parks the thread 0 and calls the scheduler, which starts the thread 1
    in [B]. [B] calls [addOrUpdate]; its [try_lock] finds the lock taken,
    and the thread 1 yields by an [ecall]. The thread 0 resumes, completes
    its insertion and releases the lock; [main] calls [B.f], which inserts
    [B]'s value; [main] reads its own value back, asserts it and returns,
    which exits the thread 0. The thread 1 resumes after its [ecall],
    takes the lock, updates [B]'s value and returns, which exits the
    thread 1; the scheduler halts the machine. The scheduler is called five
    times: the boot, the interrupt, the yield and the two exits. The first
    conjunct is the run with the interrupt: [machine_run_irq] gives a
    result only if the run reaches the table of [addOrUpdate] with
    interrupts enabled and takes the interrupt there. [kvs_adequacy]
    applies to the run: the flag of the assert library is still zero. *)
Theorem kvs_runs_and_gracefully_halts :
  machine_run_irq (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N)
    kvs_irq_cause (N.to_nat 12000%N) kvs_demo_state = Some Halted
  ∧ ∃ σ',
      rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
        ([Instr Halted], σ')
      ∧ mem σ' !! img_flag kvs_demo_image = Some (WInt 0%Z).
Proof.
  assert (machine_run_irq (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N)
            kvs_irq_cause (N.to_nat 12000%N) kvs_demo_state = Some Halted)
    as Hirq by (vm_compute; reflexivity).
  split; first exact Hirq.
  pose proof kvs_irq_cause_in as Hcause.
  destruct (machine_run_irq_hw_correct _ _ _ _ _ _ Hcause Hirq) as [σ' Hrun].
  exists σ'. split; first exact Hrun.
  exact (kvs_adequacy _ _ _ _ kvs_demo_ok Hrun).
Qed.

(** ** The hand-overs and the lock *)

(** Where the switcher saves the cause of the thread [i]'s last trap. *)
Definition kvs_saved_mcause (i : nat) : Addr :=
  (b_trusted_stack (thread_of kvs_demo_image i) ^+ TrustedStack_offset_mcause)%a.

(** The scheduler is about to return from a call with cause [c], handing
    the thread [i] back. *)
Definition kvs_returning (c : Z) (i : nat) (φ : ExecConf) : bool :=
  rr_returning kvs_demo_image c φ &&
  bool_decide (reg φ !! ca0 = Some (thread_handle kvs_demo_firmware kvs_demo_image i)).

(** The lock word of the service, right after its table. *)
Definition kvs_demo_lock_addr : Addr :=
  (cmpt_b_cgp (cmpt_of kvs_demo_image "kvs") ^+ KVS_LOCK_OFFSET)%a.

(** The slot [i] of the table in [φ]: its option word, its full key and its
    value. *)
Definition kvs_demo_slot (i : Z) (φ : ExecConf) : list (option Word) :=
  (λ j, mem φ !! (cmpt_b_cgp (cmpt_of kvs_demo_image "kvs") ^+ (ASM_SIZEOF_KVS_ENTRY * i + j))%a)
    <$> [0; 1; 2]%Z.

(** The instruction after the call of [try_lock] in [addOrUpdate]'s
    [acquire], seven words before its table. *)
Definition kvs_try_lock_ret_addr (img : fw_image) : Addr :=
  (kvs_irq_addr img ^+ (-7))%a.

(** The scheduler's [Halt], when every user thread has exited. *)
Definition kvs_sched_halt_addr (img : fw_image) : Addr :=
  (cmpt_a_code (cmpt_of img "sched") ^+ 8)%a.

(** The interrupt (thread 0 to thread 1). Where it hits, the thread 0's
    [try_lock] has returned [0], the lock word is [1] and interrupts are
    enabled. When the scheduler is about to return from the call the
    interrupt causes, the thread 0 is parked with the interrupt's cause and
    still holds the lock, and the scheduler hands the thread 1's handle to
    the switcher, which starts the thread 1 in [B]. *)
Remark kvs_demo_interrupt_holding :
  (∃ σ0,
     rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
       ([griotte_lang.Exec], σ0)
     ∧ pc_at (kvs_irq_addr kvs_demo_image) σ0 = true
     ∧ mie_of (get_a (sreg_word σ0 mstatus)) = InterruptEnabled
     ∧ reg σ0 !! ct0 = Some (WInt 0%Z)
     ∧ mem σ0 !! kvs_demo_lock_addr = Some (WInt 1%Z))
  ∧ (∃ σ1,
       rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
         ([griotte_lang.Exec], σ1)
       ∧ kvs_returning kvs_irq_cause 1 σ1 = true
       ∧ mem σ1 !! kvs_saved_mcause 0 = Some (WInt kvs_irq_cause)
       ∧ mem σ1 !! kvs_demo_lock_addr = Some (WInt 1%Z)).
Proof.
  split.
  - pose proof (machine_run_until_correct (pc_at (kvs_irq_addr kvs_demo_image))
      (N.to_nat 1000%N) Executable kvs_demo_state) as Hrun.
    assert (match machine_run_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) (Executable, kvs_demo_state) with
            | Some σ0 =>
                pc_at (kvs_irq_addr kvs_demo_image) σ0 = true ∧
                bool_decide (mie_of (get_a (sreg_word σ0 mstatus)) = InterruptEnabled) = true ∧
                bool_decide (reg σ0 !! ct0 = Some (WInt 0%Z)) = true ∧
                bool_decide (mem σ0 !! kvs_demo_lock_addr = Some (WInt 1%Z)) = true
            | None => False
            end) as Hσ0 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_until _ _ _) as [σ0|]; [|done].
    destruct Hσ0 as (Hstop & Hmie & Hct0 & Hlock).
    exists σ0. split_and!.
    + apply rtc_erased_step_hw. by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hmie.
    + by apply bool_decide_eq_true_1 in Hct0.
    + by apply bool_decide_eq_true_1 in Hlock.
  - pose proof kvs_irq_cause_in as Hcause.
    pose proof (machine_run_irq_until_hw_correct
      (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
      (kvs_returning kvs_irq_cause 1) (N.to_nat 12000%N) kvs_demo_state) as Hrun.
    assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) kvs_irq_cause
              (kvs_returning kvs_irq_cause 1) (N.to_nat 12000%N) kvs_demo_state with
            | Some σ1 =>
                kvs_returning kvs_irq_cause 1 σ1 = true ∧
                bool_decide (mem σ1 !! kvs_saved_mcause 0 = Some (WInt kvs_irq_cause)) = true ∧
                bool_decide (mem σ1 !! kvs_demo_lock_addr = Some (WInt 1%Z)) = true
            | None => False
            end) as Hσ1 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_irq_until _ _ _ _ _ _) as [σ1|]; [|done].
    destruct Hσ1 as (Hstop & Hmc0 & Hlock).
    exists σ1. split_and!.
    + by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hmc0.
    + by apply bool_decide_eq_true_1 in Hlock.
Qed.

(** The thread 1 finds the lock taken and yields (thread 1 to thread 0).
    After the interrupt, the first return of [try_lock] in [addOrUpdate]
    is the thread 1's: it returns [-1], the lock word still [1]. The thread
    1 then yields by an [ecall]: it is parked with the cause of an
    [ecall], and the scheduler hands the thread 0's handle back. The thread
    0's saved cause is the interrupt's: the switcher resumes it at the
    instruction the interrupt hit, still holding the lock. *)
Remark kvs_demo_busy_yields :
  (∃ σ2,
     rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
       ([griotte_lang.Exec], σ2)
     ∧ pc_at (kvs_try_lock_ret_addr kvs_demo_image) σ2 = true
     ∧ reg σ2 !! ct0 = Some (WInt (-1)%Z)
     ∧ mem σ2 !! kvs_demo_lock_addr = Some (WInt 1%Z))
  ∧ (∃ σ3,
       rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
         ([griotte_lang.Exec], σ3)
       ∧ kvs_returning MCAUSE_ECALL_MACHINE 0 σ3 = true
       ∧ mem σ3 !! kvs_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)
       ∧ mem σ3 !! kvs_saved_mcause 0 = Some (WInt kvs_irq_cause)
       ∧ mem σ3 !! kvs_demo_lock_addr = Some (WInt 1%Z)).
Proof.
  pose proof kvs_irq_cause_in as Hcause.
  split.
  - pose proof (machine_run_irq_until_hw_correct
      (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
      (pc_at (kvs_try_lock_ret_addr kvs_demo_image)) (N.to_nat 12000%N)
      kvs_demo_state) as Hrun.
    assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) kvs_irq_cause
              (pc_at (kvs_try_lock_ret_addr kvs_demo_image)) (N.to_nat 12000%N)
              kvs_demo_state with
            | Some σ2 =>
                pc_at (kvs_try_lock_ret_addr kvs_demo_image) σ2 = true ∧
                bool_decide (reg σ2 !! ct0 = Some (WInt (-1)%Z)) = true ∧
                bool_decide (mem σ2 !! kvs_demo_lock_addr = Some (WInt 1%Z)) = true
            | None => False
            end) as Hσ2 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_irq_until _ _ _ _ _ _) as [σ2|]; [|done].
    destruct Hσ2 as (Hstop & Hct0 & Hlock).
    exists σ2. split_and!.
    + by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hct0.
    + by apply bool_decide_eq_true_1 in Hlock.
  - pose proof (machine_run_irq_until_hw_correct
      (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
      (kvs_returning MCAUSE_ECALL_MACHINE 0) (N.to_nat 12000%N) kvs_demo_state) as Hrun.
    assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) kvs_irq_cause
              (kvs_returning MCAUSE_ECALL_MACHINE 0) (N.to_nat 12000%N) kvs_demo_state with
            | Some σ3 =>
                kvs_returning MCAUSE_ECALL_MACHINE 0 σ3 = true ∧
                bool_decide (mem σ3 !! kvs_saved_mcause 1
                             = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
                bool_decide (mem σ3 !! kvs_saved_mcause 0 = Some (WInt kvs_irq_cause)) = true ∧
                bool_decide (mem σ3 !! kvs_demo_lock_addr = Some (WInt 1%Z)) = true
            | None => False
            end) as Hσ3 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_irq_until _ _ _ _ _ _) as [σ3|]; [|done].
    destruct Hσ3 as (Hstop & Hmc1 & Hmc0 & Hlock).
    exists σ3. split_and!.
    + by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hmc1.
    + by apply bool_decide_eq_true_1 in Hmc0.
    + by apply bool_decide_eq_true_1 in Hlock.
Qed.

(** The exit of the thread 0 (thread 0 to thread 1). One thread is still
    live, so the scheduler hands the thread 1's handle back; the thread 1
    is still parked after its [ecall]. The lock is free. The table holds
    [main]'s value [12] in the slot [15], under the full key [65537] of its
    key [1] and its user key [1], and [B]'s value [13] in the slot [14],
    under the full key [131073] of its key [1] and its user key [2]; the
    flag of the assert library is zero. *)
Remark kvs_demo_t0_exits :
  ∃ σ4,
    rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
      ([griotte_lang.Exec], σ4)
    ∧ kvs_returning MCAUSE_THREAD_EXIT 1 σ4 = true
    ∧ mem σ4 !! kvs_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
    ∧ mem σ4 !! kvs_saved_mcause 1 = Some (WInt MCAUSE_ECALL_MACHINE)
    ∧ mem σ4 !! kvs_demo_lock_addr = Some (WInt 0%Z)
    ∧ kvs_demo_slot 15 σ4 = [Some (WInt 1%Z); Some (WInt 65537%Z); Some (WInt 12%Z)]
    ∧ kvs_demo_slot 14 σ4 = [Some (WInt 1%Z); Some (WInt 131073%Z); Some (WInt 13%Z)]
    ∧ mem σ4 !! img_flag kvs_demo_image = Some (WInt 0%Z).
Proof.
  pose proof kvs_irq_cause_in as Hcause.
  pose proof (machine_run_irq_until_hw_correct
    (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
    (kvs_returning MCAUSE_THREAD_EXIT 1) (N.to_nat 12000%N) kvs_demo_state) as Hrun.
  assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
            (N.to_nat 1000%N) kvs_irq_cause
            (kvs_returning MCAUSE_THREAD_EXIT 1) (N.to_nat 12000%N) kvs_demo_state with
          | Some σ4 =>
              kvs_returning MCAUSE_THREAD_EXIT 1 σ4 = true ∧
              bool_decide (mem σ4 !! kvs_saved_mcause 0
                           = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
              bool_decide (mem σ4 !! kvs_saved_mcause 1
                           = Some (WInt MCAUSE_ECALL_MACHINE)) = true ∧
              bool_decide (mem σ4 !! kvs_demo_lock_addr = Some (WInt 0%Z)) = true ∧
              bool_decide (kvs_demo_slot 15 σ4
                           = [Some (WInt 1%Z); Some (WInt 65537%Z); Some (WInt 12%Z)]) = true ∧
              bool_decide (kvs_demo_slot 14 σ4
                           = [Some (WInt 1%Z); Some (WInt 131073%Z); Some (WInt 13%Z)]) = true ∧
              bool_decide (mem σ4 !! img_flag kvs_demo_image
                           = Some (WInt 0%Z)) = true
          | None => False
          end) as Hσ4 by (vm_compute; split_and!; reflexivity).
  destruct (machine_run_irq_until _ _ _ _ _ _) as [σ4|]; [|done].
  destruct Hσ4 as (Hstop & Hmc0 & Hmc1 & Hlock & Hslot15 & Hslot14 & Hflag).
  exists σ4. split_and!.
  - by apply Hrun.
  - done.
  - by apply bool_decide_eq_true_1 in Hmc0.
  - by apply bool_decide_eq_true_1 in Hmc1.
  - by apply bool_decide_eq_true_1 in Hlock.
  - by apply bool_decide_eq_true_1 in Hslot15.
  - by apply bool_decide_eq_true_1 in Hslot14.
  - by apply bool_decide_eq_true_1 in Hflag.
Qed.

(** The thread 1's retry. After the thread 0's exit, the first return of
    [try_lock] in [addOrUpdate] is the thread 1's second attempt: it
    returns [0], and the lock word is [1]. At the scheduler's [Halt], once
    the thread 1 has updated [B]'s value and exited, the lock is free
    again, the table holds both values, and the flag of the assert library
    is zero. *)
Remark kvs_demo_retry_takes :
  (∃ σ5,
     rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
       ([griotte_lang.Exec], σ5)
     ∧ pc_at (kvs_try_lock_ret_addr kvs_demo_image) σ5 = true
     ∧ mem σ5 !! kvs_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)
     ∧ reg σ5 !! ct0 = Some (WInt 0%Z)
     ∧ mem σ5 !! kvs_demo_lock_addr = Some (WInt 1%Z))
  ∧ (∃ σ6,
       rtc (@erased_step griotte_hw_lang) ([griotte_lang.Exec], kvs_demo_state)
         ([griotte_lang.Exec], σ6)
       ∧ pc_at (kvs_sched_halt_addr kvs_demo_image) σ6 = true
       ∧ mem σ6 !! kvs_saved_mcause 1 = Some (WInt MCAUSE_THREAD_EXIT)
       ∧ mem σ6 !! kvs_demo_lock_addr = Some (WInt 0%Z)
       ∧ kvs_demo_slot 15 σ6 = [Some (WInt 1%Z); Some (WInt 65537%Z); Some (WInt 12%Z)]
       ∧ kvs_demo_slot 14 σ6 = [Some (WInt 1%Z); Some (WInt 131073%Z); Some (WInt 13%Z)]
       ∧ mem σ6 !! img_flag kvs_demo_image = Some (WInt 0%Z)).
Proof.
  pose proof kvs_irq_cause_in as Hcause.
  split.
  - pose proof (machine_run_irq_until_hw_correct
      (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
      (λ φ, pc_at (kvs_try_lock_ret_addr kvs_demo_image) φ
            && bool_decide (mem φ !! kvs_saved_mcause 0 = Some (WInt MCAUSE_THREAD_EXIT)))
      (N.to_nat 12000%N) kvs_demo_state) as Hrun.
    assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) kvs_irq_cause
              (λ φ, pc_at (kvs_try_lock_ret_addr kvs_demo_image) φ
                    && bool_decide (mem φ !! kvs_saved_mcause 0
                                    = Some (WInt MCAUSE_THREAD_EXIT)))
              (N.to_nat 12000%N) kvs_demo_state with
            | Some σ5 =>
                pc_at (kvs_try_lock_ret_addr kvs_demo_image) σ5 = true ∧
                bool_decide (mem σ5 !! kvs_saved_mcause 0
                             = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
                bool_decide (reg σ5 !! ct0 = Some (WInt 0%Z)) = true ∧
                bool_decide (mem σ5 !! kvs_demo_lock_addr = Some (WInt 1%Z)) = true
            | None => False
            end) as Hσ5 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_irq_until _ _ _ _ _ _) as [σ5|]; [|done].
    destruct Hσ5 as (Hstop & Hmc0 & Hct0 & Hlock).
    exists σ5. split_and!.
    + by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hmc0.
    + by apply bool_decide_eq_true_1 in Hct0.
    + by apply bool_decide_eq_true_1 in Hlock.
  - pose proof (machine_run_irq_until_hw_correct
      (pc_at (kvs_irq_addr kvs_demo_image)) (N.to_nat 1000%N) kvs_irq_cause
      (pc_at (kvs_sched_halt_addr kvs_demo_image)) (N.to_nat 12000%N)
      kvs_demo_state) as Hrun.
    assert (match machine_run_irq_until (pc_at (kvs_irq_addr kvs_demo_image))
              (N.to_nat 1000%N) kvs_irq_cause
              (pc_at (kvs_sched_halt_addr kvs_demo_image)) (N.to_nat 12000%N)
              kvs_demo_state with
            | Some σ6 =>
                pc_at (kvs_sched_halt_addr kvs_demo_image) σ6 = true ∧
                bool_decide (mem σ6 !! kvs_saved_mcause 1
                             = Some (WInt MCAUSE_THREAD_EXIT)) = true ∧
                bool_decide (mem σ6 !! kvs_demo_lock_addr = Some (WInt 0%Z)) = true ∧
                bool_decide (kvs_demo_slot 15 σ6
                             = [Some (WInt 1%Z); Some (WInt 65537%Z); Some (WInt 12%Z)]) = true ∧
                bool_decide (kvs_demo_slot 14 σ6
                             = [Some (WInt 1%Z); Some (WInt 131073%Z); Some (WInt 13%Z)]) = true ∧
                bool_decide (mem σ6 !! img_flag kvs_demo_image
                             = Some (WInt 0%Z)) = true
            | None => False
            end) as Hσ6 by (vm_compute; split_and!; reflexivity).
    destruct (machine_run_irq_until _ _ _ _ _ _) as [σ6|]; [|done].
    destruct Hσ6 as (Hstop & Hmc1 & Hlock & Hslot15 & Hslot14 & Hflag).
    exists σ6. split_and!.
    + by apply Hrun.
    + done.
    + by apply bool_decide_eq_true_1 in Hmc1.
    + by apply bool_decide_eq_true_1 in Hlock.
    + by apply bool_decide_eq_true_1 in Hslot15.
    + by apply bool_decide_eq_true_1 in Hslot14.
    + by apply bool_decide_eq_true_1 in Hflag.
Qed.
