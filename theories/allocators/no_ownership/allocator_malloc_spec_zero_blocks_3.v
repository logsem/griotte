From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.no_ownership Require Import allocator_malloc_spec_states.

(** * Malloc, block 2: zeroing the payload

    Block 2 is the zeroing loop over the payload [b, finish), through the
    payload capability in [ca2]. *)

Section AllocatorMallocZeroBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_malloc_zero_spec
    (E : coPset) (pc_b pc_e pc_a b finish : Addr) (ι : AId) (w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (heap_b <= b /\ b < finish /\ finish <= heap_e)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 2)%a ∗
    ca2 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
    ct2 ↦ᵣ WInt finish ∗
    ct3 ↦ᵣ w3 ∗
    allocator_range_memory b finish ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 3)%a ∗
       ca2 ↦ᵣ (WCap true RW Global b finish finish) @@ ι ∗
       ct2 ↦ᵣ WInt finish ∗
       ct3 ↦ᵣ WInt 0 ∗
       ([∗ list] a ∈ finz.seq_between b finish, a ↦ₐ WInt 0) ∗
       codefrag pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hrange.
    iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hmem & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 2: zero the payload *)
    focus_block 2 "Hcode_main" of allocator_malloc_blocks at pc_a as a_zero Ha_zero
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_zero_spec ca2 ct2 ct3 E RX Global pc_b pc_e a_zero
      RW Global b finish (Some ι) w3 with "[- $HPC $Hca2 $Hct2 $Hct3 $Hmem $Hcode]");
      [done|solve_addr|done|done|solve_addr| |].
    { repeat constructor; set_solver. }
    iNext. iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hzeros & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 3)%a.
    iApply "Hφ". iFrame.
  Qed.

End AllocatorMallocZeroBlocks3.
