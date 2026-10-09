From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec switcher_preamble counter.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [counter_spec]

    The proof of [counter_spec] (see [counter_spec]) is split along the
    control flow of [counter_main_code]. The block-group lemmas only depend
    on this file:
    - [counter_spec_main_blocks_1]: blocks 0-3, increment the counter,
      fetch the imports and jump to the switcher, for the call to [C_f],
    - [counter_spec_main_blocks_2]: block 4, from the return of the call
      to [C_f], restore the return address, clear the return values and
      return.

    The logical steps between the block groups, which do not execute code,
    are in [counter_spec_world] (revocation of the world before the call,
    and repair of the world before the return).

    The block-group lemmas start and end at addresses of the code
    [counter_main_code], given by [counter_block_offset] and
    [counter_instr_offset]. *)

Section Counter_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [counter_main_code], as focused by [focus_block]. *)
  Definition counter_main_blocks : list (list Word) :=
    ltac:(code_blocks_of counter_main_code).

  Lemma counter_main_code_blocks : counter_main_code = concat counter_main_blocks.
  Proof. reflexivity. Qed.

End Counter_Code.

(** Offset of the first instruction of the block [n] in [counter_main_code]. *)
Notation counter_block_offset := (code_block_offset counter_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [counter_main_code]. *)
Notation counter_instr_offset := (code_instr_offset counter_main_blocks).

(** Unfold [counter_main_code] into the chain of its blocks, in the goal
    (both in the code and in the continuation). *)
Ltac counter_unfold_code := rewrite /counter_main_code.

Section Counter_States.
  Context
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  (** The bounds of the code and of the imports, as given to
      [counter_spec]. *)
  Definition counter_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length counter_main_code)%a ∧
    (pc_b + length (counter_main_imports C_f))%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition counter_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End Counter_States.
