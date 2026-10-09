From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export logrel switcher switcher_preamble.

(** * Shared interfaces of the return routine of the switcher

    The proofs of [switcher_ret_specification_gen] (functional
    specification) and [interp_expr_switcher_return] (validity of the return
    entry point) run the same code. They share the block-group lemmas of
    [switcher_return_blocks_n], which only depend on this file:
    - [switcher_return_blocks_1]: first part of block 12, pop the topmost
      frame of the trusted stack,
    - [switcher_return_blocks_2]: second part of block 12 and blocks 13-15,
      restore the callee-save registers, clear the stack frame and the
      registers, and jump back to the caller.

    The block-group lemmas start and end at the first address of blocks of
    the code [switcher_instrs], given by [switcher_block_offset] (see
    [switcher_preamble]). *)

Section Switcher_Return_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The return entry point is the first address of block 12. *)
  Lemma switcher_return_block_12 :
    a_switcher_return = (a_switcher_call ^+ switcher_block_offset 12)%a.
  Proof. rewrite switcher_return_offset. by offsets_compute. Qed.

  (** The bounds of the caller's stack frame, as stored in the call frame. *)
  Lemma switcher_stk_bounds_frame (b e a : Addr) :
    (b <= a)%a ->
    (a ^+ 3 < e)%a ->
    is_Some (a + 4)%a ->
    switcher_stk_bounds b e a.
  Proof. intros ?? [a4 ?]. rewrite /switcher_stk_bounds. split; [|split]; solve_addr. Qed.

End Switcher_Return_States.
