From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec.
From griotte Require Export switcher_preamble error_handling.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the block specifications of the error-handling example

    The code of [main] ([error_handling_main_code]) and of [stats]
    ([stats_code]) is specified by blocks, along the control flow, between
    the calls through the switcher:
    - [error_handling_spec_main_blocks_1]: blocks 0-2 of [main] (the call
      to [adv]) and blocks 3-6 (the call to [stats_read] with the untagged
      capability of [x]), up to the entry point of the switcher,
    - [error_handling_spec_main_blocks_2]: blocks 7-8 (the check of the
      result and its assert) and blocks 9-12 (the call to [stats_read] with
      the capability of [x]),
    - [error_handling_spec_main_blocks_3]: blocks 13-15 (the check of the
      result, its assert, and the halt),
    - [error_handling_spec_read_blocks]: the blocks of [stats_read],
    - [error_handling_spec_handler_blocks]: the body of the error handler
      of [stats].

    The specifications do not mention the invariants of the example: they
    are stated over plain points-to. *)

Section Error_Handling_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [error_handling_main_code], as focused by
      [focus_block]. *)
  Definition error_handling_main_blocks : list (list Word) :=
    ltac:(code_blocks_of error_handling_main_adv_phase_code)
    ++ ltac:(code_blocks_of error_handling_main_read_1_phase_code)
    ++ ltac:(code_blocks_of error_handling_main_read_2_phase_code).

  Lemma error_handling_main_code_blocks :
    error_handling_main_code = concat error_handling_main_blocks.
  Proof. reflexivity. Qed.

  (** The blocks of [stats_code]. *)
  Definition stats_blocks : list (list Word) :=
    ltac:(code_blocks_of stats_read_code)
    ++ ltac:(code_blocks_of stats_handler_code).

  Lemma stats_code_blocks : stats_code = concat stats_blocks.
  Proof. reflexivity. Qed.

End Error_Handling_Code.

(** Offset of the label [s] of [error_handling_main_asm] from the start of
    the PCC, the imports. *)
Notation main_label s := (asm_label error_handling_main_asm s).

(** Offset of the label [s] in [error_handling_main_code], which starts at
    the label [.Lmain]. *)
Notation main_label_offset s := (asm_label_offset error_handling_main_asm ".Lmain" s).

(** Index of the block of [error_handling_main_code] that defines the label
    [s]. *)
Notation main_block s := (asm_block error_handling_main_asm s).

(** Offset of the label [s] of [stats_asm] from the start of the PCC, which
    is the start of [stats_code] ([stats] has no import). *)
Notation stats_label s := (asm_label stats_asm s).

(** Index of the block of [stats_code] that defines the label [s]. *)
Notation stats_block s := (asm_block stats_asm s).

(** Unfold [error_handling_main_code] into the chain of its blocks. *)
Ltac main_unfold_code :=
  rewrite /error_handling_main_code /error_handling_main_adv_phase_code
    /error_handling_main_read_1_phase_code /error_handling_main_read_2_phase_code
    -!app_assoc.

(** Unfold [stats_code] into the chain of its blocks. *)
Ltac stats_unfold_code :=
  rewrite /stats_code /stats_read_code /stats_handler_code -!app_assoc.

Section Error_Handling_States.
  Context
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {assertlayout : assertLayout}
  .

  (** The bounds of the code of [main]: its PCC [[pc_b, pc_e)] starts with
      the imports, and the code starts at [pc_a]. *)
  Definition main_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length error_handling_main_code)%a ∧
    (pc_b + main_label ".Lmain")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false.

  (** The bounds of the code of [stats]: its PCC [[pc_b, pc_e)] starts with
      the code. *)
  Definition stats_code_bounds (pc_b pc_e : Addr) : Prop :=
    SubBounds pc_b pc_e pc_b (pc_b ^+ length stats_code)%a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false.

  (** The capability of the entry point of the switcher. *)
  Definition main_switcher_entry : Word :=
    WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call.

  (** The capability of the entry point of the assert routine. *)
  Definition main_assert_entry : Word :=
    WSentry Inherit true RX Global b_assert e_assert b_assert.

End Error_Handling_States.
