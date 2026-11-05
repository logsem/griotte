From griotte Require Import machine_parameters assembler.

(** * The lock library

    A try-lock, entered with interrupts disabled: a compare-exchange of 0
    to 1, as the RTOS's interrupt-disabled atomics on a core without
    atomic instructions. It returns through the return sentry of its
    caller, which restores the caller's posture. *)

(** The layout of the library. A class without parameter: no [Hint Mode],
    as [assertLayout]. *)
Class locksLayout : Type :=
  mkLocksLayout {
      b_locks : Addr ;
      e_locks : Addr ;
    }.

Section Locks_Code.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (** [try_lock]: [ct0] points to the lock word. Returns 0 in [ct0] if the
      lock was free and is now taken, -1 otherwise; [ct1] is 0 on return;
      the other registers are unchanged.
<<
[[cheriot::interrupt_state(disabled)]]
int __cheri_libcall try_lock(int *l) { if (0 != *l) return -1; *l = 1; return 0; }
>> *)
  Definition locks_try_lock_asm : list asm_code :=
    [ load ct1 ct0;
      jnez ("try_lock_busy")%asm ct1;
      store ct0 1;
      mov ct0 0;
      ret;
      #"try_lock_busy";
      mov ct0 (-1);
      mov ct1 0;
      ret
    ].

  Definition locks_try_lock : list instr :=
    Eval compute in assemble locks_try_lock_asm.
  Lemma locks_try_lock_assembles : asm_ok (assemble_check locks_try_lock_asm).
  Proof. asm_check. Qed.
  Definition locks_try_lock_instrs : list Word :=
    encodeInstrsW locks_try_lock.
End Locks_Code.

(** The sentry of [try_lock]: entering it disables interrupts. *)
Definition try_lock_entry `{locksLayout} : Word :=
  Sentry FwdDisable RX Global b_locks e_locks b_locks.
