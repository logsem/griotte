From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocators.ownership Require Export allocator_preamble allocator_macros_spec.

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
    - [allocator_free_spec_quarantine_blocks_4]: blocks 5 and 6, the painting
      of the payload and the result [ALLOC_OK],
    - [allocator_free_spec_revoke_blocks_5]: blocks 7-9, the revoker
      capability, the revoker store and the unpainting of the payload,
    - [allocator_free_spec_return_blocks_6]: blocks 10-12, the return, and the
      result [ALLOC_INVALID] of a rejected request.

    The logical steps between the block groups, which do not execute code,
    are in [allocator_free_spec_world].

    The block-group lemmas start and end at addresses of the code
    [allocator_free_code], given by [allocator_free_block_offset]. *)

Global Instance allocator_free_in_prefix_dec {MP : MachineParameters} next w :
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

Section AllocatorFreeCode.
  Context {MP : MachineParameters}.

  (** The code of [free], as the chain of its blocks. *)
  Definition allocator_free_code : list Word :=
    allocator_owner_instrs ctp ca0 ct3 ct4 ++
    allocator_free_instrs_n 1 ++
    allocator_free_instrs_n 2 ++
    fetch_instrs allocator_shadow_import_off ctp ct3 ca2 ++
    allocator_free_instrs_n 4 ++
    allocator_paint_instrs ctp ca2 ShadowQuarantined ++
    allocator_free_instrs_n 6 ++
    fetch_instrs allocator_revoker_import_off ct3 ct4 ca2 ++
    allocator_free_instrs_n 8 ++
    allocator_paint_instrs ctp ca2 ShadowLive ++
    allocator_free_instrs_n 10 ++
    allocator_free_instrs_n 11 ++
    encodeInstrsW [Jalr cnull cra].

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

End AllocatorFreeStates.
