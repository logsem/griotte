From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocators.ownership Require Export allocator_preamble allocator_macros_spec.
From griotte.allocators.common Require Export allocator_common_spec_states.

(** * Shared interfaces of the proof of [free]

    The proof of the specifications of [free] is split along the control flow
    of [allocator_free_code]. The block-group lemmas only depend on this
    file:
    - [allocator_free_spec_owner_blocks_1]: block 0, the owner identifier of
      the allocator capability in [ca0], and the trap on a malformed
      allocator capability,
    - [allocator_free_spec_check_blocks_2]: blocks 1 and 2, the checks of the
      tag and of the bounds of the request against the allocated prefix,
    - [allocator_free_spec_header_blocks_3]: blocks 3 and 4, the shadow
      capability and the local check of the header and of its owner,
    - [allocator_free_spec_return_blocks_4]: the rejection of a request, in
      the tail (block 5).
    Block 5 is the shared tail of [free], specified in
    [allocator_common_free_spec_tail_blocks]: the painting of the payload,
    the result [ALLOC_OK], the revocation, the return and the rejection.

    The logical steps between the block groups, which do not execute code,
    are in [allocator_free_spec_world].

    The block-group lemmas start and end at addresses of the code
    [allocator_free_code], given by [allocator_free_block_offset]. *)

Section AllocatorFreeCode.
  Context {MP : MachineParameters}.

  (** The code of [free], as the chain of its blocks. *)
  Definition allocator_free_code : list Word :=
    allocator_owner_instrs allocator_free_owner_off ctp ca0 ++
    allocator_free_instrs_n 1 ++
    allocator_free_instrs_n 2 ++
    allocator_free_instrs_n 3 ++
    allocator_free_instrs_n 4 ++
    allocator_free_tail_code.

  Lemma allocator_free_instrs_code : allocator_free_instrs = allocator_free_code.
  Proof. reflexivity. Qed.

  (** The blocks of [allocator_free_code], as focused by [focus_block]. *)
  Definition allocator_free_blocks : list (list Word) :=
    ltac:(code_blocks_of allocator_free_code).

End AllocatorFreeCode.

(** Offset of the first instruction of the block [n] in [allocator_free_code]. *)
Notation allocator_free_block_offset := (code_block_offset allocator_free_blocks).

(** Offset of the [i]-th instruction of the block [n] in [allocator_free_code]. *)
Notation allocator_free_instr_offset := (code_instr_offset allocator_free_blocks).

(** Offset of the label [s] of [free] in [allocator_free_code], whose
    entry is the label [.Lfree_owner]. *)
Notation allocator_free_label_offset s :=
  (asm_label_offset allocator_asm ".Lfree_owner" s).

(** Offset of the rejection of [free] in [allocator_free_code]. *)
Notation allocator_free_invalid_offset := (allocator_free_label_offset ".free_invalid").

(** Unfold [allocator_free_code] into the chain of its blocks. *)
Ltac allocator_free_unfold_code h := unfold_code allocator_free_code h.

Section AllocatorFreeStates.
  Context {MP : MachineParameters} {layout : allocatorLayout}.

  (** The bounds of the code: the PCC, the shadow table and the bump slot. *)
  Definition allocator_free_code_bounds (pc_b pc_e pc_a : Addr) : Prop :=
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_code)%a ∧
    disjoint_from_shadow pc_b pc_e ∧
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e.

  Lemma allocator_free_entry_bounds {layout_wf : allocatorLayoutWf} :
    allocator_free_code_bounds allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr.
  Proof.
    split_and!.
    - rewrite -allocator_free_instrs_code. apply allocator_free_pcc_bounds.
    - apply allocator_pcc_disjoint_from_shadow.
    - apply allocator_cgp_not_in_pcc.
  Qed.

  (** The shared tail of [allocator_free_code]. *)

  Lemma allocator_free_tail_bounds pc_b pc_e pc_a :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e
      (pc_a ^+ allocator_free_block_offset 5)%a.
  Proof.
    intros (Hpc & Hshadow & _). split; last done.
    cbn in Hpc. offsets_compute. solve_addr.
  Qed.

End AllocatorFreeStates.

Section AllocatorFreeSegments.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {MP : MachineParameters}.

  Lemma allocator_free_tail_acc pc_a :
    codefrag_pers pc_a allocator_free_code -∗
    codefrag_pers (pc_a ^+ allocator_free_block_offset 5)%a allocator_free_tail_code.
  Proof.
    iIntros "#Hcode_main".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    focus_block_nochangePC 5 "Hcode_main" as a_tail Ha_tail "Hcode" "Hcont".
    assert (a_tail = (pc_a ^+ allocator_free_block_offset 5)%a) as <-
      by (cbn in Ha_tail; offsets_compute; solve_addr).
    iExact "Hcode".
  Qed.

End AllocatorFreeSegments.
