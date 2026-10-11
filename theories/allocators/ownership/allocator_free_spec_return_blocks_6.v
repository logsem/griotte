From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, blocks 10-12: the return

    After a successful [free], block 10 jumps to the return, block 12. A
    rejected request continues at block 11, which sets [ALLOC_INVALID] and
    clears [ca1], and returns through block 12. *)

Section AllocatorFreeReturnBlocks6.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_free_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 10)%a ∗
    cra ↦ᵣ wret ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       cnull ↦ᵣ WInt 0 ∗
       codefrag pc_a allocator_free_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _).
    iIntros "(HPC & Hcra & Hcnull & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".

    (* Block 10: jump to the return *)
    focus_block 10 "Hcode_main" of allocator_free_blocks at pc_a as a_jmp Ha_jmp
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Jmp .free_return. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_free_block_offset 12)%a);
        offsets_compute; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: return *)
    focus_block 12 "Hcode_main" of allocator_free_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_return_spec with "[- $HPC $Hcra $Hcnull $Hcode]"); [solve_addr|done|].
    iNext. iIntros "(HPC & Hcra & Hcnull & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hφ". iFrame.
  Qed.

  (** Blocks 11 and 12: set [ALLOC_INVALID] and return. *)
  Lemma allocator_free_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 11)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       cnull ↦ᵣ WInt 0 ∗
       codefrag pc_a allocator_free_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".

    (* Block 11: set ALLOC_INVALID *)
    focus_block 11 "Hcode_main" of allocator_free_blocks at pc_a as a_invalid Ha_invalid
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ALLOC_INVALID. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 12: return *)
    focus_block 12 "Hcode_main" of allocator_free_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_return_spec with "[- $HPC $Hcra $Hcnull $Hcode]"); [solve_addr|done|].
    iNext. iIntros "(HPC & Hcra & Hcnull & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hφ". iFrame.
  Qed.

End AllocatorFreeReturnBlocks6.
