From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Export fetch_spec assert_spec switcher_preamble interrupt_status.
From griotte Require Export case_study_spec_helpers.

(** * Shared interfaces of the proof of [ist_spec]

    The proof of [ist_spec] (see [interrupt_status_spec]) is split along
    the control flow of [ist_K_code]. The block-group lemmas only depend on
    this file:
    - [ist_spec_init_blocks_1]: block 0, initialisation of [b] and of the
      capability to [b], the argument of the call,
    - [ist_spec_call_blocks_2]: blocks 1-2 (fetch the imports) and block 3
      up to the call to [B.f],
    - [ist_spec_check_blocks_3]: block 3, from the return of the call
      (overwrite [b] and load it), then block 4 (assertion) and block 5
      (return).

    The logical steps between the block groups, which do not execute code,
    are in [ist_spec_world].

    The block-group lemmas start and end at addresses of the code
    [ist_K_code], given by the labels of [ist_K_asm]
    ([ist_label_offset]). *)

Section IST_Code.
  Context `{MP: MachineParameters}.

  (** The blocks of [ist_K_code], as focused by [focus_block]. *)
  Definition ist_K_blocks : list (list Word) := ltac:(code_blocks_of ist_K_code).

  Lemma ist_K_code_blocks : ist_K_code = concat ist_K_blocks.
  Proof. reflexivity. Qed.

End IST_Code.

(** Offset of the first instruction of the block [n] in [ist_K_code]. *)
Notation ist_block_offset := (code_block_offset ist_K_blocks).

(** Offset of the [i]-th instruction of the block [n] in [ist_K_code]. *)
Notation ist_instr_offset := (code_instr_offset ist_K_blocks).

(** Offset of the label [s] of [ist_K_asm] from the start of the PCC, the
    imports. *)
Notation ist_label s := (asm_label ist_K_asm s).

(** Offset of the label [s] in [ist_K_code], which starts at the label
    [.Lstatus_run]. *)
Notation ist_label_offset s := (asm_label_offset ist_K_asm ".Lstatus_run" s).

(** Index of the block of [ist_K_code] that defines the label [s]. *)
Notation ist_block s := (asm_block ist_K_asm s).

Section IST_States.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  (** The imported words, in the order of [ist_K_imports]. *)
  Definition ist_imports (pc_b : Addr) (B_f : Sealable) : iProp Σ :=
    pc_b ↦ₐ□ switcher_entry_call ∗
    (pc_b ^+ 1) ↦ₐ□ assert_entry ∗
    (pc_b ^+ 2) ↦ₐ□ WSealed ot_switcher B_f.

  (** The imports and the code, that the block groups return unchanged. *)
  Definition ist_static_mem (pc_b pc_a : Addr) (B_f : Sealable) : iProp Σ :=
    ist_imports pc_b B_f ∗
    codefrag_pers pc_a ist_K_code.

  (** The bounds of the code and of the imports, as given to [ist_spec]. *)
  Definition ist_code_bounds (pc_b pc_e pc_a : Addr) (B_f : Sealable) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length ist_K_code) ∧
    (pc_b + ist_label ".Lstatus_run")%a = Some pc_a ∧
    disjoint_from_shadow pc_b pc_e ∧
    is_heap_address pc_b = false ∧
    is_heap_cap (WSealed ot_switcher B_f) = false.

End IST_States.
