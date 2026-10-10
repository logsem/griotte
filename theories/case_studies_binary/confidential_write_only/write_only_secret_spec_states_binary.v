From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Export switcher fetch_spec_binary write_only_secret_binary.
From griotte Require Export case_study_spec_helpers_binary.

(** * Shared interfaces of the proof of [write_only_secret_spec]

    The proof of [write_only_secret_spec] is split along the control flow
    of [write_only_secret_main_code], executed in lockstep by both runs.
    The block-group lemmas only depend on this file:
    - [write_only_secret_spec_init_blocks_1_binary]: block 0, restrict the
      capability [cgp] to the permission [WO], in [ca0],
    - [write_only_secret_spec_call_blocks_2_binary]: blocks 1-3, fetch the
      imports and jump to the switcher, for the call to [B.f],
    - [write_only_secret_spec_halt_blocks_3_binary]: the last instruction
      of block 3, halt.

    The safety predicate of the shared cell, and the logical steps between
    the block groups, which do not execute code, are in
    [write_only_secret_spec_world_binary].

    The block-group lemmas start and end at addresses of the code
    [write_only_secret_main_code], given by [write_only_secret_block_offset]
    and [write_only_secret_instr_offset]. *)

Section Write_only_secret_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [write_only_secret_main_code], as focused by [focus_block]. *)
  Definition write_only_secret_main_blocks : list (list Word) :=
    ltac:(code_blocks_of write_only_secret_main_code).

  Lemma write_only_secret_main_code_blocks :
    write_only_secret_main_code = concat write_only_secret_main_blocks.
  Proof. reflexivity. Qed.

End Write_only_secret_Code.

(** Offset of the first instruction of the block [n] in [write_only_secret_main_code]. *)
Notation write_only_secret_block_offset := (code_block_offset write_only_secret_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [write_only_secret_main_code]. *)
Notation write_only_secret_instr_offset := (code_instr_offset write_only_secret_main_blocks).

Section Write_only_secret_States.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** The bounds of the code and of the two imports. *)
  Definition write_only_secret_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length write_only_secret_main_code)%a ∧
    (pc_b + 2)%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition write_only_secret_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End Write_only_secret_States.
