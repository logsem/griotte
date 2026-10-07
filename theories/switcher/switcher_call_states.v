From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble switcher_macros_spec.

(** * Shared interfaces of the call routine of the switcher

    The proofs of [switcher_cc_specification_gen] (functional specification)
    and [interp_expr_switcher_call] (validity of the call entry point) run the
    same code. They share the block-group lemmas of [switcher_call_blocks_n],
    which only depend on this file:
    - [switcher_call_blocks_1]: blocks 0-1, checks on [csp] (and block 17,
      the forced unwind when the checks fail),
    - [switcher_call_blocks_2]: blocks 2-3, spill of the callee-save
      registers and push on the trusted stack (and block 16, when the
      trusted stack is exhausted),
    - [switcher_call_blocks_3]: blocks 4-7, chop and clear the callee stack,
      load the unsealing capability and unseal the entry point,
    - [switcher_call_blocks_4]: blocks 7-11, load the callee and jump to it.

    The block-group lemmas start and end at the first address of blocks of
    the code [switcher_instrs], given by [switcher_block_offset] (see
    [switcher_preamble]). *)

Section Switcher_Call_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The checks of blocks 0 and 1 on the stack pointer [wcsp]. *)
  Definition switcher_csp_checked (wcsp : Word) : Prop :=
    rules_Get.denote (GetP ct2 csp) wcsp = Some (encodePerm RWL) ∧
    rules_Get.denote (GetL ct2 csp) wcsp = Some (encodeLoc Local).

  Lemma switcher_csp_checked_stk b e a :
    switcher_csp_checked (WCap RWL Local b e a).
  Proof. done. Qed.

  Lemma switcher_csp_checked_cap p g b e a :
    switcher_csp_checked (WCap p g b e a) -> p = RWL ∧ g = Local.
  Proof.
    intros [Hp Hg]; cbn in Hp, Hg; simplify_eq.
    split; [by apply encodePerm_inj | by apply encodeLoc_inj].
  Qed.

End Switcher_Call_States.
