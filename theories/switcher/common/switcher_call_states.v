From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export switcher switcher_preamble logrel.

(** * Shared interfaces of the call routine of the switcher

    The proofs of [switcher_cc_specification_gen] (functional specification)
    and [interp_expr_switcher_call] (validity of the call entry point) run the
    same code. They share the block lemmas of [call/], one file per region
    of the code, named after its entry label, and their compositions in
    [call_path]:
    - [switch_csp_check]: the checks on [csp];
    - [switch_entry_first_spill]: the spill of the callee-save registers;
    - [switcher_trusted_stack_push]: the push on the trusted stack;
    - [switch_stack_chop]: chop and clear the callee's stack, and load the
      unsealing capability;
    - [switch_unseal_entry]: unseal and decode the entry point, and load
      the callee;
    - [switcher_clear_unused_args]: clear the registers and jump to the
      callee.
    The failures are in [failure/].

    The block lemmas start and end at labels of the code [switcher_instrs],
    whose offsets are given by [switcher_label_offset] (see
    [switcher_tactics]). *)

Section Switcher_Call_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The checks of blocks 0 and 1 on the stack pointer [wcsp]. *)
  Definition switcher_csp_checked (wcsp : LWord) : Prop :=
    rules_Get.denote (GetP ct2 csp) wcsp.(lw) = Some (encodePerm RWL) ∧
    rules_Get.denote (GetL ct2 csp) wcsp.(lw) = Some (encodeLoc Local).

  Lemma switcher_csp_checked_stk b e a :
    switcher_csp_checked (WCap true RWL Local b e a).
  Proof. done. Qed.

  Lemma switcher_csp_checked_cap p g b e a π :
    switcher_csp_checked (WCap true p g b e a @@? π) -> p = RWL ∧ g = Local.
  Proof.
    intros [Hp Hg]; cbn in Hp, Hg; simplify_eq.
    split; [by apply encodePerm_inj | by apply encodeLoc_inj].
  Qed.

End Switcher_Call_States.
