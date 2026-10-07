From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble deep_immutability.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [droe_spec]

    The proof of [droe_spec] (see [deep_immutability_spec]) is split along the
    control flow of [droe_main_code]. The block-group lemmas only depend on
    this file:
    - [droe_spec_init_blocks_1]: block 0, initialisation of the data,
    - [droe_spec_share_blocks_2]: blocks 1-2 (fetch the imports) and block 3
      up to the call to the adversary,
    - [droe_spec_assert_blocks_3]: block 3, from the return of the call,
      block 4 (assertion) and block 5 (halt).

    The logical steps between the block groups, which do not execute code,
    are in [droe_spec_world].

    The block-group lemmas start and end at addresses of the code
    [droe_main_code], given by [droe_block_offset] and [droe_instr_offset]. *)

Section DROE_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [droe_main_code], as focused by [focus_block]. *)
  Definition droe_main_blocks : list (list Word) := ltac:(code_blocks_of droe_main_code).

  Lemma droe_main_code_blocks : droe_main_code = concat droe_main_blocks.
  Proof. reflexivity. Qed.

End DROE_Code.

(** Offset of the first instruction of the block [n] in [droe_main_code]. *)
Notation droe_block_offset := (code_block_offset droe_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [droe_main_code]. *)
Notation droe_instr_offset := (code_instr_offset droe_main_blocks).

Section DROE_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The imported words, in the order of [droe_main_imports]. *)
  Definition droe_imports (pc_b : Addr) (C_f : Sealable) : iProp Σ :=
    pc_b ↦ₐ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    (pc_b ^+ 1)%a ↦ₐ WSentry RX Global b_assert e_assert b_assert ∗
    (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f.

  (** The imports and the code, that the block groups return unchanged. *)
  Definition droe_static_mem (pc_b pc_a : Addr) (C_f : Sealable) : iProp Σ :=
    droe_imports pc_b C_f ∗
    codefrag pc_a droe_main_code.

  (** The bounds of the code and of the imports, as given to [droe_spec]. *)
  Definition droe_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length droe_main_code)%a ∧
    (pc_b + length (droe_main_imports C_f))%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition droe_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End DROE_States.
