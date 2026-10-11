From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte Require Export code_blocks.
From griotte.allocator Require Export allocator_preamble allocator_macros_spec.

(** * Shared interfaces of the proof of [free]

    The proof of the specifications of [free] is split along the control flow
    of [allocator_free_code]. The block-group lemmas only depend on this
    file:
    - [allocator_free_spec_check_blocks_1]: blocks 0 and 1, the checks of the
      tag and of the bounds of the request against the allocated prefix,
    - [allocator_free_spec_header_blocks_2]: blocks 2 and 3, the shadow
      capability and the local check of the header,
    - [allocator_free_spec_quarantine_blocks_3]: blocks 4 and 5, the painting
      of the payload and the result [ALLOC_OK],
    - [allocator_free_spec_revoke_blocks_4]: blocks 6-8, the revoker
      capability, the revoker store and the unpainting of the payload,
    - [allocator_free_spec_return_blocks_5]: blocks 9-11, the return, and the
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
    allocator_free_instrs_n 0 ++
    allocator_free_instrs_n 1 ++
    fetch_instrs allocator_shadow_import_off ctp ct3 ca2 ++
    allocator_free_instrs_n 3 ++
    allocator_paint_instrs ctp ca2 ShadowQuarantined ++
    allocator_free_instrs_n 5 ++
    fetch_instrs allocator_revoker_import_off ct3 ct4 ca2 ++
    allocator_free_instrs_n 7 ++
    allocator_paint_instrs ctp ca2 ShadowLive ++
    allocator_free_instrs_n 9 ++
    allocator_free_instrs_n 10 ++
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
