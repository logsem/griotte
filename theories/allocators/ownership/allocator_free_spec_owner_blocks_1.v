From iris.proofmode Require Import proofmode.
From griotte Require Import switcher_namespace rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, block 0: the owner identifier of the allocator capability

    Block 0 unseals the allocator capability in [ca0] with the imported
    unsealing key, and loads its owner identifier into [ctp]. On success, the
    group ends at block 1. A malformed allocator capability traps. *)

Section AllocatorFreeOwnerBlocks1.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_free_owner_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (g : Locality) (a : Addr) (o : Z)
    (wtp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (pc_b + allocator_free_pcc_off)%a = Some pc_a ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->
    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
    a ↦ₐ WInt o ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ (PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 1) ∗
       ctp ↦ᵣ WInt o ∗
       ca0 ↦ᵣ allocator_capability g a ∗
       (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
       a ↦ₐ WInt o ∗
       codefrag_pers pc_a allocator_free_code
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hpcc Hshadow_a Ha.
    iIntros "(HPC & Hctp & Hca0 & #Hkey & Howner & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".

    (* Block 0: the owner identifier *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_owner_spec with
      "[- $HPC $Hctp $Hca0 $Hkey $Howner $Hcode]"); try done.
    { rewrite /allocator_unsealing_key_import_off.
      rewrite allocator_free_pcc_off_eq /allocator_malloc_pcc_off in Hpcc.
      let n := eval vm_compute in (length allocator_malloc_instrs) in
      change (length allocator_malloc_instrs) with n in Hpcc.
      let v := eval vm_compute in allocator_free_owner_off in
      change allocator_free_owner_off with v.
      solve_addr. }
    { apply withinBounds_true_iff. rewrite /allocator_unsealing_key_import_off.
      pose proof (eq_refl : length (allocator_owner_instrs allocator_free_owner_off ctp ca0) = 4%nat).
      solve_addr. }
    iNext. iIntros "(HPC & Hctp & Hca0 & _ & Howner & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_block_offset 1).
    iApply "Hφ". iFrame "∗ Hcode_main Hkey".
  Qed.

  Lemma allocator_free_owner_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wsealed wtp : LWord)
    (P : iProp Σ) :
    let a_owner_end := (pc_a ^+ length (allocator_owner_instrs allocator_free_owner_off ctp ca0)) in
    ↑Ntstack ⊆ E ->
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (pc_b + allocator_free_pcc_off)%a = Some pc_a ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->
    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ca0 ↦ᵣ wsealed ∗
    (pc_b ^+ allocator_unsealing_key_import_off) ↦ₐ□ allocator_unsealing_key ∗
    codefrag_pers pc_a allocator_free_code ∗
    (∀ a, ⌜a ∈ₐ [pc_a, a_owner_end)⌝ -∗
      ctp ↦ᵣ - ∗
      ca0 ↦ᵣ wsealed -∗
      trap_safe (Cap RX Global pc_b pc_e a) E (λ v, ⌜v = HaltedV⌝ → P)%I)
    ⊢ WP Exec @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros a_owner_end HEswitcher (Hpc & Hpc_shadow & _) Hpcc Hwsealed.
    subst a_owner_end.
    iIntros "(HPC & Hctp & Hca0 & #Hkey & #Hcode_main & Hfailed)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".

    (* Block 0: the unsealing or the load of the owner identifier traps *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iApply (allocator_owner_invalid_spec with
      "[$HPC $Hctp $Hca0 $Hkey $Hcode Hfailed]"); try done.
    { rewrite /allocator_unsealing_key_import_off.
      rewrite allocator_free_pcc_off_eq /allocator_malloc_pcc_off in Hpcc.
      let n := eval vm_compute in (length allocator_malloc_instrs) in
      change (length allocator_malloc_instrs) with n in Hpcc.
      let v := eval vm_compute in allocator_free_owner_off in
      change allocator_free_owner_off with v.
      solve_addr. }
    { apply withinBounds_true_iff. rewrite /allocator_unsealing_key_import_off.
      pose proof (eq_refl : length (allocator_owner_instrs allocator_free_owner_off ctp ca0) = 4%nat).
      solve_addr. }
  Qed.

End AllocatorFreeOwnerBlocks1.
