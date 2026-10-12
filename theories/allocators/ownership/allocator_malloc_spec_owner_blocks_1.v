From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_malloc_spec_states.

(** * Malloc, block 0: the owner identifier of the allocator capability

    Block 0 unseals the allocator capability in [ca0] with the imported
    unsealing key, and loads its owner identifier into [ctp]. On success, the
    group ends at block 1. A malformed allocator capability traps. *)

Section AllocatorMallocOwnerBlocks1.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_malloc_owner_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (g : Locality) (a : Addr) (o : Z)
    (wtp w3 w4 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ□ allocator_unsealing_key ∗
    a ↦ₐ WInt o ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1)%a ∗
       ctp ↦ᵣ WInt o ∗
       ct3 ↦ᵣ WInt 0 ∗
       ct4 ↦ᵣ WInt 0 ∗
       ca0 ↦ᵣ allocator_capability g a ∗
       (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ□ allocator_unsealing_key ∗
       a ↦ₐ WInt o ∗
       codefrag_pers pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hshadow_a Ha.
    iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & #Hkey & Howner & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 0: the owner identifier *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_owner_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Hkey $Howner $Hcode]"); try done.
    { apply withinBounds_true_iff. rewrite /allocator_unsealing_key_import_off.
      pose proof (eq_refl : length (allocator_owner_instrs ctp ca0 ct3 ct4) = 11%nat).
      solve_addr. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & _ & Howner & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 1)%a.
    iApply "Hφ". iFrame "∗ Hcode_main Hkey".
  Qed.

  Lemma allocator_malloc_owner_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wsealed wtp w3 w4 : LWord) (P : iProp Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ wsealed ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ□ allocator_unsealing_key ∗
    codefrag_pers pc_a allocator_malloc_code
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hwsealed.
    iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & #Hkey & #Hcode_main)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 0: the unsealing or the load of the owner identifier traps *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iApply (allocator_owner_invalid_spec with
      "[$HPC $Hctp $Hct3 $Hct4 $Hca0 $Hkey $Hcode]"); try done.
    { apply withinBounds_true_iff. rewrite /allocator_unsealing_key_import_off.
      pose proof (eq_refl : length (allocator_owner_instrs ctp ca0 ct3 ct4) = 11%nat).
      solve_addr. }
  Qed.

End AllocatorMallocOwnerBlocks1.
