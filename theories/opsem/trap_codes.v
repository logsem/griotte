From stdpp Require Import numbers.

(** Exception causes, with the names and values of CHERIoT's
    [sdk/include/priv/riscv.h]. *)
Definition MCAUSE_INST_ACCESS_FAULT : Z := 1.
Definition MCAUSE_ILLEGAL_INSTRUCTION : Z := 2.
Definition MCAUSE_LOAD_ACCESS_FAULT : Z := 5.
Definition MCAUSE_STORE_ACCESS_FAULT : Z := 7.
(** The cause the switcher writes when a thread exits (CHERIoT's
    [MCAUSE_THREAD_EXIT], [sdk/include/priv/riscv.h]). *)
Definition MCAUSE_THREAD_EXIT : Z := 24.
Definition MCAUSE_CHERI : Z := 28.
(** The interrupt bit of mcause (bit 31) and the interrupt codes, with the
    names and values of CHERIoT's [sdk/include/priv/riscv.h]. *)
Definition MCAUSE_INTR : Z := 2 ^ 31.
Definition MCAUSE_MTIME : Z := 7.
Definition MCAUSE_MEXTERN : Z := 11.
(** The cause of an environment call from machine mode (CHERIoT's
    [MCAUSE_ECALL_MACHINE]). *)
Definition MCAUSE_ECALL_MACHINE : Z := 11.

(** The value that exception entry writes to mtval when the exception has
    none (cheriot-sail's [tval None]): an illegal instruction, whose
    instruction bits Griotte does not report, and an environment call. *)
Definition MTVAL_NONE : Z := 0.
