(** * Switcher: code and functional specifications

    The switcher's code and layout, its code tactics, the macro specifications
    used by its clients, its invariant, and the functional specifications of
    its call and return routines. *)

From griotte Require Export
  switcher switcher_tactics export_table_layout clear_registers_spec switcher_load_spec.
From griotte Require Export switcher_preamble.
From griotte Require Export switcher_spec_call switcher_spec_return.
