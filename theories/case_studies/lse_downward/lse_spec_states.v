From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec.
From griotte Require Export switcher_preamble lse.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proofs of [lse_run_spec] and [lse_f_spec]

    The proofs of [lse_run_spec] (see [lse_spec]) and of [lse_f_spec]
    (see [lse_spec_closure]) are split along the control flow of
    [lse_main_code]. The block-group lemmas only depend on this file:
    - [lse_spec_run_blocks_1]: blocks 0-3, store [2] in [a], fetch the
      imports and jump to the switcher, for the call to [C_f],
    - [lse_spec_run_blocks_2]: block 3, from the return of the call to
      [C_f], return: the thread exits,
    - [lse_spec_f_blocks_1]: block 4, push the capability of [a] on the
      stack and load [a],
    - [lse_spec_f_blocks_2]: blocks 5-6, assert that [a] contains [2], and
      return.

    The logical steps between the block groups, which do not execute code,
    are in [lse_spec_world] (revocation of the world before the call to
    [C_f] and at the entry point of [f], repair of the world before the
    return of [f]).

    The block-group lemmas start and end at addresses of the code
    [lse_main_code], given by the labels of [lse_main_asm]
    ([lse_label_offset]). *)

(** The namespace of the invariant on the global [a] of [lse]. *)
Definition Nlse : namespace := nroot .@ "lse".

Section LSE_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [lse_main_code], as focused by [focus_block]. *)
  Definition lse_main_blocks : list (list Word) :=
    ltac:(code_blocks_of LSE_main_code_run)
    ++ ltac:(code_blocks_of LSE_main_code_f).

  Lemma lse_main_code_blocks : lse_main_code = concat lse_main_blocks.
  Proof. reflexivity. Qed.

End LSE_Code.

(** Offset of the first instruction of the block [n] in [lse_main_code]. *)
Notation lse_block_offset := (code_block_offset lse_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [lse_main_code]. *)
Notation lse_instr_offset := (code_instr_offset lse_main_blocks).

(** Offset of the label [s] of [lse_main_asm] from the start of the PCC,
    the imports. *)
Notation lse_label s := (asm_label lse_main_asm s).

(** Offset of the label [s] in [lse_main_code], which starts at the label
    [.Llse_run]. *)
Notation lse_label_offset s := (asm_label_offset lse_main_asm ".Llse_run" s).

(** Index of the block of [lse_main_code] that defines the label [s]. *)
Notation lse_block s := (asm_block lse_main_asm s).

(** Unfold [lse_main_code] into the chain of its blocks, in the goal (both in
    the code and in the continuation). *)
Ltac lse_unfold_code :=
  rewrite /lse_main_code /LSE_main_code_run -!app_assoc /LSE_main_code_f.

Section LSE_States.
  Context
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {assertlayout : assertLayout}
  .

  (** The bounds of the code and of the imports, as given to
      [lse_run_spec] and [lse_f_spec]. *)
  Definition lse_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length lse_main_code) ∧
    (pc_b + lse_label ".Llse_run")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false.



  (** The capability of [a], pushed on the stack by [f]. *)
  Definition lse_a_cap (cgp_b : Addr) : Word :=
    Cap RW Global cgp_b (cgp_b ^+ 1) cgp_b.

End LSE_States.
