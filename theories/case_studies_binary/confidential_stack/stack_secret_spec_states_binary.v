From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Export switcher fetch_spec_binary stack_secret_binary.
From griotte Require Export case_study_spec_helpers_binary.

(** * Shared interfaces of the proof of [stack_secret_spec]

    The proof of [stack_secret_spec] is split along the control flow of
    [stack_secret_main_code], executed in lockstep by both runs. The
    block-group lemmas only depend on this file:
    - [stack_secret_spec_init_blocks_1_binary]: block 0, store the secret
      at [csp_b] and at [csp_b + 5], and move the stack pointer to
      [csp_b + 1],
    - [stack_secret_spec_call_blocks_2_binary]: blocks 1-3, fetch the
      imports and jump to the switcher, for the call to [B.f],
    - [stack_secret_spec_halt_blocks_3_binary]: the last instruction of
      block 3, halt.

    The logical steps between the block groups, which do not execute code,
    are in [stack_secret_spec_world_binary].

    The block-group lemmas start and end at addresses of the code
    [stack_secret_main_code], given by [stack_secret_block_offset] and
    [stack_secret_instr_offset]. *)

Section Stack_secret_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [stack_secret_main_code], as focused by [focus_block]. *)
  Definition stack_secret_main_blocks : list (list Word) :=
    ltac:(code_blocks_of stack_secret_main_code).

  Lemma stack_secret_main_code_blocks :
    stack_secret_main_code = concat stack_secret_main_blocks.
  Proof. reflexivity. Qed.

End Stack_secret_Code.

(** Offset of the first instruction of the block [n] in [stack_secret_main_code]. *)
Notation stack_secret_block_offset := (code_block_offset stack_secret_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [stack_secret_main_code]. *)
Notation stack_secret_instr_offset := (code_instr_offset stack_secret_main_blocks).

Section Stack_secret_States.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** The bounds of the code and of the two imports. *)
  Definition stack_secret_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_secret_main_code)%a ∧
    (pc_b + 2)%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition stack_secret_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End Stack_secret_States.
