From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode proofmode_binary.
From griotte Require Export switcher fetch_spec_binary stack_callee_secret_binary.
From griotte Require Export case_study_spec_helpers_binary.

(** * Shared interfaces of the proofs of [stack_callee_secret_run_spec] and
    [stack_callee_secret_f_spec]

    The proofs of [stack_callee_secret_run_spec] (see
    [stack_callee_secret_spec_run_binary]) and of [stack_callee_secret_f_spec]
    (see [stack_callee_secret_spec_binary]) are split along the control flow
    of [stack_callee_secret_code], executed in lockstep by both runs. The
    block-group lemmas only depend on this file:
    - [stack_callee_secret_spec_run_blocks_1_binary]: blocks 0-2, fetch the
      imports and jump to the switcher, for the call to [B.adv],
    - [stack_callee_secret_spec_run_blocks_2_binary]: the last instruction
      of block 2, from the return of the call to [B.adv], halt,
    - [stack_callee_secret_spec_f_blocks_1_binary]: block 3, the body of
      [T.f]: write the secret at the base of the stack frame, and return.

    The logical steps between the block groups, which do not execute code,
    are in [stack_callee_secret_spec_world_binary].

    The block-group lemmas start and end at addresses of the code
    [stack_callee_secret_code], given by [stack_callee_secret_block_offset]
    and [stack_callee_secret_instr_offset]. *)

Section Stack_callee_secret_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [stack_callee_secret_code], as focused by [focus_block]. *)
  Definition stack_callee_secret_blocks : list (list Word) :=
    ltac:(code_blocks_of stack_callee_secret_code_run)
    ++ ltac:(code_blocks_of stack_callee_secret_code_f).

  Lemma stack_callee_secret_code_blocks :
    stack_callee_secret_code = concat stack_callee_secret_blocks.
  Proof. reflexivity. Qed.

End Stack_callee_secret_Code.

(** Offset of the first instruction of the block [n] in [stack_callee_secret_code]. *)
Notation stack_callee_secret_block_offset := (code_block_offset stack_callee_secret_blocks).

(** Offset of the [i]-th instruction of the block [n] in [stack_callee_secret_code]. *)
Notation stack_callee_secret_instr_offset := (code_instr_offset stack_callee_secret_blocks).

(** Unfold [stack_callee_secret_code] into the chain of its blocks, in the
    goal (both in the code and in the continuation). *)
Ltac stack_callee_secret_unfold_code :=
  rewrite /stack_callee_secret_code /stack_callee_secret_code_run -!app_assoc.

Section Stack_callee_secret_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {specg : specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  (** The bounds of the code and of the two imports. *)
  Definition stack_callee_secret_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length stack_callee_secret_code)%a ∧
    (pc_b + 2)%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition stack_callee_secret_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

  (** The entry point [T.f] is the first instruction of block 3. *)
  Lemma stack_callee_secret_f_entry (pc_b pc_e pc_a : Addr) :
    stack_callee_secret_code_bounds pc_b pc_e pc_a ->
    (pc_b ^+ Z.of_nat stack_callee_secret_f_offset)%a
    = (pc_a ^+ stack_callee_secret_block_offset 3)%a.
  Proof.
    intros [_ Himports_contiguous].
    assert (stack_callee_secret_block_offset 3 = Z.of_nat (length stack_callee_secret_code_run))
      as -> by reflexivity.
    rewrite /stack_callee_secret_f_offset.
    cbn [length stack_callee_secret_imports].
    solve_addr.
  Qed.

  (** The resources of [T] that are never shared: its imports and code, the
      same in both runs, and its private data, the secret of each run. *)
  Definition stack_callee_secret_inv
    (pc_b pc_a cgp_b : Addr) (B_adv : Sealable) (secret1 secret2 : Z) : iProp Σ :=
    [[ pc_b , pc_a ]] ↦ₐ [[ stack_callee_secret_imports B_adv ]]
    ∗ [[ pc_b , pc_a ]] ↣ₐ [[ stack_callee_secret_imports B_adv ]]
    ∗ codefrag pc_a stack_callee_secret_code
    ∗ spec_codefrag pc_a stack_callee_secret_code
    ∗ cgp_b ↦ₐ WInt secret1
    ∗ cgp_b ↣ₐ WInt secret2.

End Stack_callee_secret_States.
