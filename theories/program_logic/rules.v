(* Program logic rules for machine instructions are split into several files,
   with one file for each instruction, which we import below. *)
From griotte Require Export
     instructions.arithmetic instructions.cheri instructions.control
     instructions.memory_accesses instructions.system
     devices.shadow devices.revoker devices.timer
     traps.ecall traps.entry ghost.registry.

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

     (see for instance [rules_Subseg.wp_subseg_rebase])

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
