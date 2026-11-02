From griotte Require Import griotte_opsem.
#[local] Open Scope Z_scope.

(** * Dispatch on the cause, after the exception spill

    What it is: the two tests of [.Lexception_might_handle] in the switcher,
    CHERIoT's [beq a0, t1, .Lhandle_error] with a0 = [MCAUSE_CHERI] and
    [bltu t1, a0, .Lhandle_error] with a0 = 8, are Griotte's
    [jeq ".Lhandle_error" ca0 ct1] and [jlt ".Lhandle_error" ct1 ca0], with
    t1 = mcause. Griotte's conditional jumps compare signed integers
    ([jcond_test]); CHERIoT's [bltu] is unsigned. The causes that must reach
    [.Lexception_scheduler_call] are the two interrupts, the [ecall] and the
    thread exit: none jumps. On CHERIoT's resume path,
    [bne t0, t1, .Lcommon_context_install] with t1 = 11 skips the increment
    of the resumed PC for every cause but the [ecall]'s, in particular for
    the external interrupt 2^31 + 11.

    Assumptions: the interrupt causes are the positive integers 2^31 + 7 and
    2^31 + 11 (mcause's top bit set, as an unsigned 32-bit value); the
    [ecall] and exit causes are CHERIoT's 11 and 24. *)

(** The causes that the switcher hands to the scheduler. *)
Definition scheduler_causes : list Z :=
  irq_causes ++ [MCAUSE_ECALL_MACHINE; MCAUSE_THREAD_EXIT].

(** Neither test of [.Lexception_might_handle] jumps for the cause [c]: the
    exception path falls through to [.Lexception_scheduler_call]. The
    operands of the jumps do not matter to [jcond_test]. *)
Definition falls_to_scheduler_call (c : Z) : Prop :=
  ∀ off r1 r2 off' r1' r2',
    jcond_test (Jeq off r1 r2) MCAUSE_CHERI c = false ∧
    jcond_test (Jlt off' r1' r2') c 8 = false.

(** Some test jumps: the exception path goes to [.Lhandle_error]. *)
Definition goes_to_handle_error (c : Z) : Prop :=
  ∀ off r1 r2 off' r1' r2',
    jcond_test (Jeq off r1 r2) MCAUSE_CHERI c = true ∨
    jcond_test (Jlt off' r1' r2') c 8 = true.

Lemma scheduler_causes_dispatch : Forall falls_to_scheduler_call scheduler_causes.
Proof.
  rewrite /scheduler_causes /irq_causes /=.
  repeat (constructor; [intros ??????; split; reflexivity|]). constructor.
Qed.

(** The faults go to [.Lhandle_error]: CHERI faults and the causes below 8
    (Griotte's faults have the causes 1, 2, 5, 7 and 28). *)
Lemma fault_causes_dispatch :
  Forall goes_to_handle_error
    [MCAUSE_INST_ACCESS_FAULT; MCAUSE_ILLEGAL_INSTRUCTION;
     MCAUSE_LOAD_ACCESS_FAULT; MCAUSE_STORE_ACCESS_FAULT; MCAUSE_CHERI].
Proof.
  repeat (constructor; [intros ??????; first [left; reflexivity | right; reflexivity]|]).
  constructor.
Qed.

(** The signed [jlt] agrees with CHERIoT's unsigned [bltu] on every cause
    that is a 32-bit unsigned value: such a cause is non-negative. *)
Lemma bltu_signed_agree c :
  (0 ≤ c < 2^32)%Z →
  Z.ltb c 8 = Z.ltb (c mod 2^32) (8 mod 2^32).
Proof.
  intros Hc. rewrite (Z.mod_small c); [|done].
  rewrite (Z.mod_small 8); [done|]. split; vm_compute; [discriminate | reflexivity].
Qed.

(** The resume path skips the increment of the resumed PC exactly for the
    [ecall]'s cause: [bne t0, t1] with t1 = 11 jumps for every other cause. *)
Lemma resume_skip_increment c off r1 r2 :
  jcond_test (Jne off r1 r2) c MCAUSE_ECALL_MACHINE = negb (c =? MCAUSE_ECALL_MACHINE)%Z.
Proof. reflexivity. Qed.

Lemma external_interrupt_not_ecall : MCAUSE_INTR + MCAUSE_MEXTERN ≠ MCAUSE_ECALL_MACHINE.
Proof.
  unfold MCAUSE_INTR, MCAUSE_MEXTERN, MCAUSE_ECALL_MACHINE. intros H. vm_compute in H.
  discriminate H.
Qed.
