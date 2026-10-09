From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble deep_locality.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [dle_spec]

    The proof of [dle_spec] (see [deep_locality_spec]) is split along the
    control flow of [dle_main_code]. The block-group lemmas only depend on
    this file:
    - [dle_spec_init_blocks_1]: block 0, initialisation of the data,
    - [dle_spec_share_blocks_2]: blocks 1-2 (fetch the imports) and block 3
      up to the first call to the adversary,
    - [dle_spec_overwrite_blocks_3]: block 3, from the return of the first
      call up to the second call to the adversary,
    - [dle_spec_assert_blocks_4]: block 3, from the return of the second
      call, block 4 (assertion) and block 5 (halt).

    The logical steps between the block groups, which do not execute code,
    are in [dle_spec_world].

    The block-group lemmas start and end at addresses of the code
    [dle_main_code], given by [dle_block_offset] and [dle_instr_offset]. *)

Section DLE_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [dle_main_code], as focused by [focus_block]. *)
  Definition dle_main_blocks : list (list Word) := ltac:(code_blocks_of dle_main_code).

  Lemma dle_main_code_blocks : dle_main_code = concat dle_main_blocks.
  Proof. reflexivity. Qed.

End DLE_Code.

(** Offset of the first instruction of the block [n] in [dle_main_code]. *)
Notation dle_block_offset := (code_block_offset dle_main_blocks).

(** Offset of the [i]-th instruction of the block [n] in [dle_main_code]. *)
Notation dle_instr_offset := (code_instr_offset dle_main_blocks).

Section DLE_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The imported words, in the order of [dle_main_imports]. *)
  Definition dle_imports (pc_b : Addr) (C_f : Sealable) : iProp Σ :=
    pc_b ↦ₐ WSentry XSRW_ Local b_switcher e_switcher a_switcher_call ∗
    (pc_b ^+ 1)%a ↦ₐ WSentry RX Global b_assert e_assert b_assert ∗
    (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f.

  (** The imports and the code, that the block groups return unchanged. *)
  Definition dle_static_mem (pc_b pc_a : Addr) (C_f : Sealable) : iProp Σ :=
    dle_imports pc_b C_f ∗
    codefrag pc_a dle_main_code.

  (** The bounds of the code and of the imports, as given to [dle_spec]. *)
  Definition dle_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code)%a ∧
    (pc_b + length (dle_main_imports C_f))%a = Some pc_a.

  (** The capability of the entry point of the switcher. *)
  Definition dle_switcher_entry : Word :=
    WSentry XSRW_ Local b_switcher e_switcher a_switcher_call.

End DLE_States.
