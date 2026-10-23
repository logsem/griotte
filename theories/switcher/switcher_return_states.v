From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export logrel switcher switcher_preamble.

(** * Shared interfaces of the return routine of the switcher

    The proofs of [switcher_ret_specification_gen] (functional
    specification) and [interp_expr_switcher_return] (validity of the return
    entry point) run the same code. They share the block-group lemmas of
    [switcher_return_blocks_n], which only depend on this file:
    - [switcher_return_blocks_1]: first part of block 13, pop the topmost
      frame of the trusted stack,
    - [switcher_return_blocks_2]: second part of block 13 and blocks 14-16,
      restore the callee-save registers, clear the stack frame and the
      registers, and jump back to the caller.

    The block-group lemmas start and end at labels of the code
    [switcher_instrs], whose offsets are given by [switcher_label_offset] (see
    [switcher_preamble]). *)

Section Switcher_Return_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The return entry point is the first address of block 13. *)
  Lemma switcher_return_block_13 :
    a_switcher_return = (a_switcher_call ^+ switcher_label_offset "switcher_after_compartment_call")%a.
  Proof. rewrite switcher_return_offset. by offsets_compute. Qed.

End Switcher_Return_States.
