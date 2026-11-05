From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble temporal_isolation.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [ti_spec]

    The proof of [ti_spec] (see [temporal_isolation_spec]) is split along
    the control flow of [ti_K_code]. The block-group lemmas only depend on
    this file:
    - [ti_spec_init_blocks_1]: block 0, initialisation of [b] and of the
      local capability to [b], the argument of the call,
    - [ti_spec_call_blocks_2]: blocks 1-2 (fetch the imports) and block 3
      up to the call to [B.f],
    - [ti_spec_assert_blocks_3]: block 3, from the return of the call
      (overwrite [b]), block 4 (assertion) and block 5 (return).

    The logical steps between the block groups, which do not execute code,
    are in [ti_spec_world].

    The block-group lemmas start and end at addresses of the code
    [ti_K_code], given by the labels of [ti_K_asm]
    ([ti_label_offset]). *)

Section TI_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [ti_K_code], as focused by [focus_block]. *)
  Definition ti_K_blocks : list (list Word) := ltac:(code_blocks_of ti_K_code).

  Lemma ti_K_code_blocks : ti_K_code = concat ti_K_blocks.
  Proof. reflexivity. Qed.

End TI_Code.

(** Offset of the first instruction of the block [n] in [ti_K_code]. *)
Notation ti_block_offset := (code_block_offset ti_K_blocks).

(** Offset of the [i]-th instruction of the block [n] in [ti_K_code]. *)
Notation ti_instr_offset := (code_instr_offset ti_K_blocks).

(** Offset of the label [s] of [ti_K_asm] from the start of the PCC, the
    imports. *)
Notation ti_label s := (asm_label ti_K_asm s).

(** Offset of the label [s] in [ti_K_code], which starts at the label
    [.Lti_run]. *)
Notation ti_label_offset s := (asm_label_offset ti_K_asm ".Lti_run" s).

(** Index of the block of [ti_K_code] that defines the label [s]. *)
Notation ti_block s := (asm_block ti_K_asm s).

Section TI_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The imported words, in the order of [ti_K_imports]. *)
  Definition ti_imports (pc_b : Addr) (B_f : Sealable) : iProp Σ :=
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher B_f.

  (** The imports and the code, that the block groups return unchanged. *)
  Definition ti_static_mem (pc_b pc_a : Addr) (B_f : Sealable) : iProp Σ :=
    ti_imports pc_b B_f ∗
    codefrag_pers pc_a ti_K_code.

  (** The bounds of the code and of the imports, as given to [ti_spec]. *)
  Definition ti_code_bounds (pc_b pc_e pc_a : Addr) (B_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length ti_K_code) ∧
    (pc_b + ti_label ".Lti_run")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher B_f) = false.

End TI_States.
