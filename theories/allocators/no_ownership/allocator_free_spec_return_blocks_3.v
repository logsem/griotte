From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.no_ownership Require Import allocator_free_spec_states.
From griotte.allocators.common Require Import allocator_common_free_spec_tail_blocks.

(** * Free, the rejection of a request

    A rejected request continues in the tail (block 4), which sets
    [ALLOC_INVALID], clears [ca1] and returns. *)

Section AllocatorFreeReturnBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_free_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wnull ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       cnull ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_free_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds. pose proof Hbounds as (Hpc & _ & _).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & #Hcode_main & Hφ)".
    iDestruct (allocator_free_tail_acc with "Hcode_main") as "#Hcode".
    assert ((pc_a ^+ allocator_free_invalid_offset)%a =
      ((pc_a ^+ allocator_free_block_offset 4) ^+ allocator_free_tail_block_offset 5)%a)
      as -> by (cbn in Hpc; offsets_compute; solve_addr).
    iApply (allocator_free_tail_invalid_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hcode]");
      first by apply allocator_free_tail_bounds.
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorFreeReturnBlocks3.
