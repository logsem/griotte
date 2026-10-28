From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.
From griotte.allocators.common Require Import allocator_common_free_spec_tail_blocks.

(** * Free, the rejection of a request

    A rejected request continues in the tail (block 5), which sets
    [ALLOC_INVALID], clears [ca1] and returns. *)

Section AllocatorFreeReturnBlocks4.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_free_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset) ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_free_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros Hbounds Htgt. pose proof Hbounds as (Hpc & _ & _).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & #Hcode_main & Hφ)".
    iDestruct (allocator_free_tail_acc with "Hcode_main") as "#Hcode".
    assert (pc_a ^+ allocator_free_invalid_offset =
      (pc_a ^+ allocator_free_block_offset 5) ^+ allocator_free_tail_block_offset 5)
      as -> by (cbn in Hpc; offsets_compute; solve_addr).
    iApply (allocator_free_tail_invalid_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hcode]");
      [by apply allocator_free_tail_bounds | done |].
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorFreeReturnBlocks4.
