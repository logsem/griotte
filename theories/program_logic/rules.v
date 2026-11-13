(** * The program-logic rules of the machine instructions

    The rules live in [rules/], in layers.

    - [shapes/]: the shape rules, generic over the step function of the
      instruction. [step.v]: the lifting of a step to a WP, the outcome of
      a step in closed form ([faulted_outcome], [step_outcome]), the fault
      rules ([wp_fault_step], [wp_instr_faulted_0] to [wp_instr_faulted_3]).
      [regs.v]: the register shape, for an instruction that writes at most
      one register and moves the PC: [wp_regs_step], its k-ary instances
      ([wp_regs_next_1] to [wp_regs_next_4], the [_any_dst] forms, the jump
      rules [wp_regs_jump_0] to [wp_regs_jump_3]), and the hint databases
      [regs_next_ok_db] and [regs_next_ok_lax_db]. [memory_access.v]: the
      memory shape: the master load and store rules, the loaded word as a
      [load_choice], the k-ary load and store rules, and the hint database
      [mem_next_ok_db].
    - [instructions/]: one file per family of instructions. Per
      instruction: its steps in closed form (pure lemmas, [<instr>_next_ok]
      or [<instr>_jump_agree]), their hint lines, then its dedicated WP
      rules, where a shape rule is not enough.
    - [devices/]: the platform devices. [traps/]: trap entry, the cause of
      a fault, the volatile registers and ecall. [ghost/]: the rules on the
      ghost state of the registry and of quarantined objects.

    The instructions of [machine_instructions], by file:
    - [shapes/step.v]: Fail, Halt.
    - [instructions/arithmetic.v]: Mov, Lt, Le, Add, Sub, Mul, LAnd, LOr,
      LShiftL, LShiftR.
    - [instructions/cheri.v]: Lea, SetA, Restrict, Subseg, ClearTag, GetP,
      GetL, GetB, GetE, GetLen, GetA, GetOType, GetWType, GetTag, Seal,
      UnSeal, Auipcc.
    - [instructions/control.v]: Jmp, Jeq, Jne, Jlt, Jle, Jalr.
    - [instructions/memory_accesses.v]: CLoad, Store (and [devices/] for
      their device forms).
    - [instructions/system.v]: Mret, SetMIE, SpecialRW.
    - [traps/ecall.v]: Ecall.

    [iInstr] finds the rule of an instruction in [proofmode_instr_rules.v]
    ([dispatch_instr_rule]): a register instruction is stepped by
    [dispatch_next_ok], which searches [regs_next_ok_db], then
    [regs_next_ok_lax_db], leaving the undecided facts as side goals; CLoad
    and Store by [dispatch_mem], which searches [mem_next_ok_db]; only
    GetTag (its witness rule), Jalr, the system instructions, Ecall, Fail
    and Halt have named entries.

    A new register or memory instruction needs one lemma in closed form in
    the file of its family, and one hint line: no WP rule, no dispatch
    entry, no case of the fundamental theorem. *)

From griotte Require Export
     instructions.arithmetic instructions.cheri instructions.control
     instructions.memory_accesses instructions.system
     devices.shadow devices.revoker devices.timer
     traps.ecall traps.entry ghost.registry
     rules_hwm.

(** Program specifications

   There is a small discrepancy between how program specifications are written
   in the paper and in the Coq development.

   The paper presenting Cerise distinguishes between three kinds of program
   specifications:

   ⟨P⟩ → ⟨s. Q⟩   single instruction
   {P} ⇝ {s. Q}   code fragment
   {P} ⇝ ∙        complete safe execution

   In this Coq development, we express specifications using slightly more
   primitive constructs: Iris' standard notion of weakest-precondition (WP) and
   Hoare triples. Specifications from the paper can be seen as sugar for these
   constructs, as follows:

   - single instruction: instead of ⟨P⟩ → ⟨s. Q⟩, we write:

     {{{ P }}} Instr Executable {{{ s. Q }}}

     (see for instance [wp_subseg_rebase])

  - code fragment: instead of {P} ⇝ {s. Q}, we write:

     ∀φ, P ∗ (Q -∗ WP Exec {{ φ }}) ⊢ WP Exec {{ φ }}

    (see for instance [examples.macros_new.rclear_spec])

  - complete safe execution: instead of {P} ⇝ ∙, we write:

     P -∗ WP Exec {{ λ _, True }}

    (see for instance [examples.minimal_counter.counter_full_run_spec])

  Rules for sequencing specifications then all become consequences of the
  general "bind rule" for weakest preconditions
  [iris.program_logic.weakestpre.wp_bind]. (Thanks to our definition of
  "evaluation contexts" corresponding to instruction sequencing.) Similarly, the
  "frame rule" is simply a consequence of a generic property of weakest
  preconditions [iris.program_logic.weakestpre.wp_strong_mono].
*)
From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.

(* Reexport CMRA for Griotte *)
From griotte Require Export state_interp.
(* Reexport resources for registers and memory *)
From griotte Require Export memory_region shapes.step machine_instructions.
