From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.no_ownership Require Import allocator_malloc_spec_states.
From griotte.allocators.common Require Import allocator_common_malloc_spec_exit_blocks.

(** * Malloc, blocks 3 and 4: publishing the bump cursor and returning

    Block 3 advances the heap root past the new allocation, publishes it in
    the bump slot, and moves the payload capability to [ca0]. The exit
    segment (block 4) returns. *)

Section AllocatorMallocPublishBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_malloc_publish_spec
    (E : coPset) (pc_b pc_e pc_a next b finish : Addr) (n : Z) (πn : option AId) (ι : AId)
    (wret wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (next + allocator_header_words)%a = Some b ->
    (b + n)%a = Some finish ->
    (heap_b < next /\ b < finish /\ finish <= heap_e)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 3)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    cra ↦ᵣ wret ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct4 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wnull ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e finish ∗
       ct4 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       ca0 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       ca1 ↦ᵣ WInt 0 ∗
       cnull ↦ᵣ WInt 0 ∗
       allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e finish ∗
       codefrag pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds Hbase Hfinish Hrange. pose proof Hbounds as (Hpc & Hpc_shadow & Hcgp_pc).
    iIntros "(HPC & Hcgp & Hcra & Hct0 & Hct4 & Hca0 & Hca1 & Hcnull & Hslot & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hbase.
    pose proof allocator_cgp_size.

    (* Block 3: publish the bump cursor *)
    focus_block 3 "Hcode_main" of allocator_malloc_blocks at pc_a as a_publish Ha_publish
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Lea ct0 allocator_header_words. *)
    iInstr "Hcode".
    (* Lea ct0 ca0. *)
    iInstr "Hcode".
    (* Store cgp ct0. *)
    iInstr "Hcode".
    { apply allocator_cgp_not_shadow. }
    { apply withinBounds_true_iff. solve_addr. }
    (* Mov ca0 ct4. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_malloc_return_offset)%a);
        offsets_compute; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: return *)
    change_pc_to
      ((pc_a ^+ allocator_malloc_block_offset 4) ^+ allocator_malloc_exit_block_offset 2)%a.
    iDestruct (allocator_malloc_exit_acc with "Hcode_main") as "[Hcode Hcont]".
    iApply (allocator_malloc_exit_return_spec with "[- $HPC $Hcra $Hcnull $Hcode]");
      first by apply allocator_malloc_exit_bounds.
    iNext. iIntros "(HPC & Hcra & Hcnull & Hcode & Hlc)".
    iApply "Hφ". iFrame. iApply ("Hcont" with "Hcode").
  Qed.

End AllocatorMallocPublishBlocks3.
