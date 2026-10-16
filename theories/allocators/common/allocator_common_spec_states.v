From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocators.common Require Export allocator_common_preamble allocator_common_macros_spec.

(** * Shared interfaces of the proofs of the shared code segments

    The entries of both allocators contain three segments of shared code,
    each a single block of their code:
    - [allocator_malloc_shadow_code], the zeroing of the payload and the
      writes of the shadow entries of a new allocation, in [malloc],
    - [allocator_malloc_exit_code], the rejections and the return of [malloc],
    - [allocator_free_tail_code], the quarantine, the revocation, the
      rejection and the return of [free].

    Their block-group lemmas start and end at addresses of these segments,
    given by [allocator_malloc_shadow_block_offset],
    [allocator_malloc_exit_block_offset] and [allocator_free_tail_block_offset].
    Each allocator focuses the segment in its own code. *)

#[global] Instance allocator_free_in_prefix_dec {MP : MachineParameters} next w :
  Decision (allocator_free_in_prefix next w).
Proof.
  unfold allocator_free_in_prefix.
  destruct w as [z|sb|tag p g b e a|ot sb].
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - destruct sb as [tag p g b e a|tag p g b e a].
    + destruct tag.
      * destruct (decide (heap_b < b /\ b < e /\ e <= next)%a) as [Hbounds|Hbounds].
        { left. exists p, g, b, e, a. auto. }
        right. intros (p' & g' & b' & e' & a' & Heq & Hrange).
        inversion Heq; subst. contradiction.
      * right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
    + right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
Defined.

Section AllocatorCommonSegments.
  Context {MP : MachineParameters}.

  (** The shadow segment of [malloc], as the chain of its blocks. *)
  Definition allocator_malloc_shadow_code : list Word :=
    allocator_zero_instrs ca2 ct2 ca3 ++
    allocator_malloc_shadow_instrs_n 1 ++
    allocator_paint_instrs ctp ca2 ShadowQuarantined ++
    allocator_malloc_shadow_instrs_n 3 ++
    allocator_paint_instrs ctp ca2 ShadowLive.

  Definition allocator_malloc_shadow_blocks : list (list Word) :=
    ltac:(code_blocks_of allocator_malloc_shadow_code).

  (** The exits of [malloc], as the chain of their blocks. *)
  Definition allocator_malloc_exit_code : list Word :=
    allocator_malloc_exit_instrs_n 0 ++
    allocator_malloc_exit_instrs_n 1 ++
    encodeInstrsW [Jalr cnull cra].

  Definition allocator_malloc_exit_blocks : list (list Word) :=
    ltac:(code_blocks_of allocator_malloc_exit_code).

  (** The tail of [free], as the chain of its blocks. *)
  Definition allocator_free_tail_code : list Word :=
    allocator_paint_instrs ctp ca2 ShadowQuarantined ++
    allocator_free_tail_instrs_n 1 ++
    allocator_free_tail_instrs_n 2 ++
    allocator_paint_instrs ctp ca2 ShadowLive ++
    allocator_free_tail_instrs_n 4 ++
    allocator_free_tail_instrs_n 5 ++
    encodeInstrsW [Jalr cnull cra].

  Definition allocator_free_tail_blocks : list (list Word) :=
    ltac:(code_blocks_of allocator_free_tail_code).

End AllocatorCommonSegments.

(** Offset of the first instruction of the block [n] of each segment. *)
Notation allocator_malloc_shadow_block_offset :=
  (code_block_offset allocator_malloc_shadow_blocks).
Notation allocator_malloc_exit_block_offset :=
  (code_block_offset allocator_malloc_exit_blocks).
Notation allocator_free_tail_block_offset :=
  (code_block_offset allocator_free_tail_blocks).

(** Unfold a segment into the chain of its blocks. *)
Ltac allocator_malloc_shadow_unfold_code h := unfold_code allocator_malloc_shadow_code h.
Ltac allocator_malloc_exit_unfold_code h := unfold_code allocator_malloc_exit_code h.
Ltac allocator_free_tail_unfold_code h := unfold_code allocator_free_tail_code h.

Section AllocatorCommonSegmentBounds.
  Context {MP : MachineParameters}.

  (** The bounds of a segment [code] at [a]: the PCC and the shadow table. *)
  Definition allocator_segment_bounds (code : list Word) (pc_b pc_e a : Addr) : Prop :=
    SubBounds pc_b pc_e a (a ^+ length code)%a ∧
    disjoint_from_shadow pc_b pc_e.

End AllocatorCommonSegmentBounds.
