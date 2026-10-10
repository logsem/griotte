From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Export switcher fetch_spec_binary cmdc_binary.
From griotte Require Export case_study_spec_helpers_binary.

(** * Shared interfaces of the proof of [cmdc_spec]

    The proof of [cmdc_spec] is split along the
    control flow of [cmdc_conf_main_code], executed in lockstep by both
    runs. The block-group lemmas only depend on this file:
    - [cmdc_spec_init_blocks_1_binary]: block 0, store [secret_c] into
      [c], erase [b], and prepare the argument of the call to [B.f],
    - [cmdc_spec_call_blocks_2_binary]: blocks 1-3 (resp. 5-7), fetch the
      imports and jump to the switcher, for the call to [B.f] (resp. [C.g]),
    - [cmdc_spec_prep_blocks_3_binary]: block 4, erase [c], store
      [secret_b] into [b], and prepare the argument of the call to [C.g],
    - [cmdc_spec_halt_blocks_4_binary]: the last instruction of block 7,
      halt.

    The two calls have the same shape, so that
    [cmdc_spec_call_blocks_2_binary] is parametrised by the call
    ([cmdc_call]).

    The logical steps between the block groups, which do not execute code,
    are in [cmdc_spec_world_binary].

    The block-group lemmas start and end at addresses of the code
    [cmdc_conf_main_code], given by [cmdc_block_offset] and
    [cmdc_instr_offset]. *)

Section CMDC_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [cmdc_conf_main_code], as focused by [focus_block]. *)
  Definition cmdc_conf_main_blocks : list (list Word) :=
    ltac:(code_blocks_of cmdc_conf_main_code).

  Lemma cmdc_conf_main_code_blocks : cmdc_conf_main_code = concat cmdc_conf_main_blocks.
  Proof. reflexivity. Qed.

End CMDC_Code.

(** Offset of the first instruction of the block [n] in [cmdc_conf_main_code]. *)
Notation cmdc_block_offset := (code_block_offset cmdc_conf_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [cmdc_conf_main_code]. *)
Notation cmdc_instr_offset := (code_instr_offset cmdc_conf_main_blocks).

(** ** The two calls of [cmdc_conf_main_code]

    The call to [B.f] (blocks 1-3) and the call to [C.g] (blocks 5-7) have
    the same code, up to the import of the callee. *)
Inductive cmdc_call := cmdc_call_B | cmdc_call_C.

(** The first block of the call: fetch the entry point of the switcher. *)
Definition cmdc_call_block (c : cmdc_call) : nat :=
  match c with cmdc_call_B => 1 | cmdc_call_C => 5 end.

(** The index of the import of the callee. *)
Definition cmdc_call_import (c : cmdc_call) : Z :=
  match c with cmdc_call_B => 1 | cmdc_call_C => 2 end.

(** The callee. *)
Definition cmdc_call_target (c : cmdc_call) (B_f C_g : Sealable) : Sealable :=
  match c with cmdc_call_B => B_f | cmdc_call_C => C_g end.

Section CMDC_States.
  Context `{MP: MachineParameters} {swlayout : switcherLayout}.

  (** The bounds of the code and of the three imports. *)
  Definition cmdc_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length cmdc_conf_main_code)%a ∧
    (pc_b + 3)%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition cmdc_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End CMDC_States.
