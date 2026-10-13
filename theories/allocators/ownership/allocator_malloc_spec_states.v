From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocators.ownership Require Export allocator_preamble allocator_macros_spec.
From griotte.allocators.common Require Export allocator_common_spec_states.

(** * Shared interfaces of the proof of [malloc]

    The proof of the specifications of [malloc] is split along the control
    flow of [allocator_malloc_code]. The block-group lemmas only depend on
    this file:
    - [allocator_malloc_spec_owner_blocks_1]: block 0, the owner identifier
      of the allocator capability in [ca0], and the trap on a malformed
      allocator capability,
    - [allocator_malloc_spec_size_check_blocks_2]: block 1, the check of the
      requested size, and the rejection of an invalid size (block 5),
    - [allocator_malloc_spec_prepare_blocks_3]: block 2, the capacity check,
      the payload capability and the header, and the rejection of an
      exhausted heap (block 5),
    - [allocator_common_malloc_spec_shadow_blocks]: block 3, the shared
      shadow segment: zeroing the payload, the shadow capability, the
      painting of the header and the same-value store over the payload,
    - [allocator_malloc_spec_publish_blocks_4]: blocks 4 and 5, publishing
      the bump cursor and returning the capability.
    Block 5 is the shared exit segment, specified in
    [allocator_common_malloc_spec_exit_blocks].

    The logical steps between the block groups, which do not execute code,
    are in [allocator_malloc_spec_world].

    The block-group lemmas start and end at addresses of the code
    [allocator_malloc_code], given by [allocator_malloc_block_offset]. *)

Section AllocatorMallocCode.
  Context {MP : MachineParameters}.

  (** The code of [malloc], as the chain of its blocks. *)
  Definition allocator_malloc_code : list Word :=
    allocator_owner_instrs allocator_malloc_owner_off ctp ca0 ++
    allocator_malloc_instrs_n 1 ++
    allocator_malloc_instrs_n 2 ++
    allocator_malloc_shadow_code ++
    allocator_malloc_instrs_n 8 ++
    allocator_malloc_exit_code.

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

(** Offset of the label [s] of [malloc] in [allocator_malloc_code], whose
    entry is the label [.Lmalloc_owner]. *)
Notation allocator_malloc_label_offset s :=
  (asm_label_offset allocator_asm ".Lmalloc_owner" s).

(** Offsets of the exits of [malloc] in [allocator_malloc_code]. *)
Notation allocator_malloc_invalid_offset := (allocator_malloc_label_offset ".malloc_invalid").
Notation allocator_malloc_no_memory_offset := (allocator_malloc_label_offset ".malloc_no_memory").
Notation allocator_malloc_return_offset := (allocator_malloc_label_offset ".malloc_return").

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

  (** The shared segments of [allocator_malloc_code]. *)

  Lemma allocator_malloc_shadow_bounds pc_b pc_e pc_a :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    allocator_segment_bounds allocator_malloc_shadow_code pc_b pc_e
      (pc_a ^+ allocator_malloc_block_offset 3)%a.
  Proof.
    intros (Hpc & Hshadow & _). split; last done.
    cbn in Hpc. offsets_compute. solve_addr.
  Qed.

  Lemma allocator_malloc_exit_bounds pc_b pc_e pc_a :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    allocator_segment_bounds allocator_malloc_exit_code pc_b pc_e
      (pc_a ^+ allocator_malloc_block_offset 5)%a.
  Proof.
    intros (Hpc & Hshadow & _). split; last done.
    cbn in Hpc. offsets_compute. solve_addr.
  Qed.

  Lemma allocator_malloc_shadow_end pc_b pc_e pc_a :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    ((pc_a ^+ allocator_malloc_block_offset 3) ^+ allocator_malloc_shadow_block_offset 5)%a =
    (pc_a ^+ allocator_malloc_block_offset 4)%a.
  Proof. intros (Hpc & _ & _). cbn in Hpc. offsets_compute. solve_addr. Qed.

End AllocatorMallocStates.

Section AllocatorMallocSegments.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {MP : MachineParameters}.

  Lemma allocator_malloc_shadow_acc pc_a :
    codefrag_pers pc_a allocator_malloc_code -∗
    codefrag_pers (pc_a ^+ allocator_malloc_block_offset 3)%a allocator_malloc_shadow_code.
  Proof.
    iIntros "#Hcode_main".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    focus_block_nochangePC 3 "Hcode_main" as a_shadow Ha_shadow "Hcode" "Hcont".
    assert (a_shadow = (pc_a ^+ allocator_malloc_block_offset 3)%a) as <-
      by (cbn in Ha_shadow; offsets_compute; solve_addr).
    iExact "Hcode".
  Qed.

  Lemma allocator_malloc_exit_acc pc_a :
    codefrag_pers pc_a allocator_malloc_code -∗
    codefrag_pers (pc_a ^+ allocator_malloc_block_offset 5)%a allocator_malloc_exit_code.
  Proof.
    iIntros "#Hcode_main".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    focus_block_nochangePC 5 "Hcode_main" as a_exit Ha_exit "Hcode" "Hcont".
    assert (a_exit = (pc_a ^+ allocator_malloc_block_offset 5)%a) as <-
      by (cbn in Ha_exit; offsets_compute; solve_addr).
    iExact "Hcode".
  Qed.

End AllocatorMallocSegments.
