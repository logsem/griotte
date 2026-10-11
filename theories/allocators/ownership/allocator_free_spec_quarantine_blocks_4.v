From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, blocks 5 and 6: the quarantine of the payload

    Block 5 paints the payload [b, e) quarantined, while the status token of
    its identifier [ι] is in [APainting]. Block 6 sets the result
    [ALLOC_OK] and clears [ca1]. *)

Section AllocatorFreeQuarantineBlocks4.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_free_quarantine_spec
    (E : coPset) (pc_b pc_e pc_a b e : Addr) (ι : AId) (wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 5)%a ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (b - heap_b))%a ∗
    ca2 ↦ᵣ WInt (e - b) ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    ι ↦st{1} APainting ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 7)%a ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
       ca2 ↦ᵣ WInt 0 ∗
       ca0 ↦ᵣ WInt ALLOC_OK ∗
       ca1 ↦ᵣ WInt 0 ∗
       ι ↦st{1} APainting ∗
       ([∗ list] a ∈ finz.seq_between b e,
          a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι)) ∗
       codefrag pc_a allocator_free_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hbounds.
    iIntros "(HPC & Hctp & Hca2 & Hca0 & Hca1 & Hpainting & Hpayload & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.

    (* Block 5: paint the payload quarantined *)
    focus_block 5 "Hcode_main" of allocator_free_blocks at pc_a as a_paint Ha_paint
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_paint_spec ShadowLive ShadowQuarantined ctp ca2 E RX Global
      pc_b pc_e a_paint b e (shadow_b ^+ (b - heap_b))%a (shadow_b ^+ (e - heap_b))%a
      (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι))
      with "[- $HPC $Hctp $Hca2 $Hcode $Hpainting $Hpayload]");
      [done|solve_addr|done|solve_addr|solve_addr|solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_painting. }
    iNext. iIntros "(HPC & Hctp & Hca2 & Hpainting & Hpayload & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: the result *)
    focus_block 6 "Hcode_main" of allocator_free_blocks at pc_a as a_success Ha_success
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ALLOC_OK. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_block_offset 7)%a.
    iApply "Hφ". iFrame.
  Qed.

End AllocatorFreeQuarantineBlocks4.
