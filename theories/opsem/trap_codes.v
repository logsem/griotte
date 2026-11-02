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

(** The value that trap entry writes to mtval for a fault that has none
    (an illegal instruction: cheriot-sail's default, without the
    instruction bits). *)
Definition MTVAL_NONE : Z := 0.
