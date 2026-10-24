From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export logrel switcher switcher_preamble.

(** * Shared interfaces of the return routine of the switcher

    The proofs of [switcher_ret_specification_gen] (functional
    specification) and [interp_expr_switcher_return] (validity of the return
    entry point) run the same code. They share the block lemmas of
    [callback/], one file per region of the code, named after its entry
    label, and their compositions in [callback_path]:
    - [switcher_after_compartment_call]: pop the topmost frame of the
      trusted stack, and restore the callee-save registers;
    - [switcher_zero_callee_frame]: clear the stack frame and the
      registers, and jump back to the caller.

    The block lemmas start and end at labels of the code [switcher_instrs],
    whose offsets are given by [switcher_label_offset] (see
    [switcher_tactics]). *)

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
