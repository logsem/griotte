From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble thread_synchronisation.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proofs of [tsy_run1_spec] and [tsy_run2_spec]

    The proofs of the two threads of [K] (see [tsy_spec_run1] and
    [tsy_spec_run2]) are split along the control flow of [tsy_K_code]. The
    block-group lemmas only depend on this file:
    - [tsy_spec_init_blocks_1]: block 0, the entry of [run1], which prepares
      the capability to [b], the argument of the call,
    - [tsy_spec_call_blocks_2]: blocks 1-2 (fetch the imports) and block 3
      up to the call to [B.f],
    - [tsy_spec_exit_blocks_3]: the return of [run1] (block 3), the
      assertion of [run2] (block 5) and the return of [run2] (block 6).

    The block-group lemmas start and end at addresses of the code
    [tsy_K_code], given by the labels of [tsy_K_asm]
    ([tsy_label_offset]). *)

Section TSY_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [tsy_K_code], as focused by [focus_block]. *)
  Definition tsy_K_blocks : list (list Word) := ltac:(code_blocks_of tsy_K_code).

  Lemma tsy_K_code_blocks : tsy_K_code = concat tsy_K_blocks.
  Proof. reflexivity. Qed.

End TSY_Code.

(** Offset of the first instruction of the block [n] in [tsy_K_code]. *)
Notation tsy_block_offset := (code_block_offset tsy_K_blocks).

(** Offset of the [i]-th instruction of the block [n] in [tsy_K_code]. *)
Notation tsy_instr_offset := (code_instr_offset tsy_K_blocks).

(** Offset of the label [s] of [tsy_K_asm] from the start of the PCC, the
    imports. *)
Notation tsy_label s := (asm_label tsy_K_asm s).

(** Offset of the label [s] in [tsy_K_code], which starts at the label
    [.Lsync_run1]. *)
Notation tsy_label_offset s := (asm_label_offset tsy_K_asm ".Lsync_run1" s).

(** Index of the block of [tsy_K_code] that defines the label [s]. *)
Notation tsy_block s := (asm_block tsy_K_asm s).

Section TSY_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The bounds of the code and of the imports, as given to the specs of
      the threads. *)
  Definition tsy_code_bounds (pc_b pc_e pc_a : Addr) (B_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length tsy_K_code) ∧
    (pc_b + tsy_label ".Lsync_run1")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher B_f) = false.

End TSY_States.
