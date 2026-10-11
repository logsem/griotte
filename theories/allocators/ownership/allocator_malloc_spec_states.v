From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocators.ownership Require Export allocator_preamble allocator_macros_spec.

(** * Shared interfaces of the proof of [malloc]

    The proof of the specifications of [malloc] is split along the control
    flow of [allocator_malloc_code]. The block-group lemmas only depend on
    this file:
    - [allocator_malloc_spec_owner_blocks_1]: block 0, the owner identifier
      of the allocator capability in [ca0], and the trap on a malformed
      allocator capability,
    - [allocator_malloc_spec_size_check_blocks_2]: block 1, the check of the
      requested size, and the rejection of an invalid size (blocks 10 and 12),
    - [allocator_malloc_spec_prepare_blocks_3]: block 2, the capacity check,
      the payload capability and the header, and the rejection of an
      exhausted heap (blocks 11 and 12),
    - [allocator_malloc_spec_zero_blocks_4]: block 3, zeroing the payload,
    - [allocator_malloc_spec_translate_paint_blocks_5]: blocks 4-8, the shadow
      capability, the painting of the header and the same-value store over
      the payload,
    - [allocator_malloc_spec_publish_blocks_6]: blocks 9 and 12, publishing
      the bump cursor and returning the capability.

    The logical steps between the block groups, which do not execute code,
    are in [allocator_malloc_spec_world].

    The block-group lemmas start and end at addresses of the code
    [allocator_malloc_code], given by [allocator_malloc_block_offset]. *)

Section AllocatorMallocCode.
  Context {MP : MachineParameters}.

  (** The code of [malloc], as the chain of its blocks. *)
  Definition allocator_malloc_code : list Word :=
    allocator_owner_instrs ctp ca0 ct3 ct4 ++
    allocator_malloc_instrs_n 1 ++
    allocator_malloc_instrs_n 2 ++
    allocator_zero_instrs ca2 ct2 ct3 ++
    fetch_instrs allocator_shadow_import_off ctp ct3 ca2 ++
    allocator_malloc_instrs_n 5 ++
    allocator_paint_instrs ctp ca2 ShadowQuarantined ++
    allocator_malloc_instrs_n 7 ++
    allocator_paint_instrs ctp ca2 ShadowLive ++
    allocator_malloc_instrs_n 9 ++
    allocator_malloc_instrs_n 10 ++
    allocator_malloc_instrs_n 11 ++
    encodeInstrsW [Jalr cnull cra].

  Lemma allocator_malloc_instrs_code : allocator_malloc_instrs = allocator_malloc_code.
  Proof. reflexivity. Qed.

  (** The blocks of [allocator_malloc_code], as focused by [focus_block]. *)
  Definition allocator_malloc_blocks : list (list Word) :=
    ltac:(code_blocks_of allocator_malloc_code).

End AllocatorMallocCode.

(** Offset of the first instruction of the block [n] in [allocator_malloc_code]. *)
Notation allocator_malloc_block_offset := (code_block_offset allocator_malloc_blocks).

(** Offset of the [i]-th instruction of the block [n] in [allocator_malloc_code]. *)
Notation allocator_malloc_instr_offset := (code_instr_offset allocator_malloc_blocks).

(** Unfold [allocator_malloc_code] into the chain of its blocks. *)
Ltac allocator_malloc_unfold_code h := unfold_code allocator_malloc_code h.

Section AllocatorMallocStates.
  Context {MP : MachineParameters} {layout : allocatorLayout}.

  (** The bounds of the code: the PCC, the shadow table and the bump slot. *)
  Definition allocator_malloc_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_code)%a ∧
    disjoint_from_shadow pc_b pc_e ∧
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e.

  Lemma allocator_malloc_entry_bounds {layout_wf : allocatorLayoutWf} :
    allocator_malloc_code_bounds allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr.
  Proof.
    split_and!.
    - rewrite -allocator_malloc_instrs_code. apply allocator_malloc_pcc_bounds.
    - apply allocator_pcc_disjoint_from_shadow.
    - apply allocator_cgp_not_in_pcc.
  Qed.

End AllocatorMallocStates.
