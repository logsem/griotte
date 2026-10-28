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
      call, block 4 (fetch the switcher again) and block 5 up to the second
      call to the adversary,
    - [dle_spec_assert_blocks_4]: block 5, from the return of the second
      call, block 6 (assertion) and block 7 (return).

    The logical steps between the block groups, which do not execute code,
    are in [dle_spec_world].

    The block-group lemmas start and end at addresses of the code
    [dle_main_code], given by the labels of [dle_main_asm]
    ([dle_label_offset]). *)

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

(** Offset of the label [s] of [dle_main_asm] from the start of the PCC,
    the imports. The labels do not depend on the argument of
    [dle_main_asm]. *)
Notation dle_label s := (asm_label (dle_main_asm 0) s).

(** Offset of the label [s] in [dle_main_code], which starts at the label
    [.Ldle_init]. *)
Notation dle_label_offset s := (asm_label_offset (dle_main_asm 0) ".Ldle_init" s).

(** Index of the block of [dle_main_code] that defines the label [s]. *)
Notation dle_block s := (asm_block (dle_main_asm 0) s).

Section DLE_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The imported words, in the order of [dle_main_imports]. *)
  Definition dle_imports (pc_b : Addr) (C_f : Sealable) : iProp Σ :=
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher C_f.

  (** The imports and the code, that the block groups return unchanged. *)
  Definition dle_static_mem (pc_b pc_a : Addr) (C_f : Sealable) : iProp Σ :=
    dle_imports pc_b C_f ∗
    codefrag_pers pc_a dle_main_code.

  (** The bounds of the code and of the imports, as given to [dle_spec]. *)
  Definition dle_code_bounds (pc_b pc_e pc_a : Addr) (C_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length dle_main_code) ∧
    (pc_b + dle_label ".Ldle_init")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher C_f) = false.


End DLE_States.
