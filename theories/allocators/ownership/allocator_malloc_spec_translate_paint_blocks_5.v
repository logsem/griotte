From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_malloc_spec_states.

(** * Malloc, blocks 4-8: the shadow entries of the new allocation

    Block 4 fetches the shadow capability from the imports. Block 5
    translates the header address [next] to its shadow entry. Block 6 paints
    the three header words quarantined. Block 7 loads the payload size, and
    block 8 stores [ShadowLive] over the payload, whose cells are claimed by
    [ι]. *)

Section AllocatorMallocTranslatePaintBlocks5.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_malloc_translate_paint_spec
    (E : coPset) (pc_b pc_e pc_a next b finish : Addr) (ι : AId) (wctp w3 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (heap_b < next)%a ->
    (next + allocator_header_words)%a = Some b ->
    (b < finish /\ finish <= heap_e)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 4)%a ∗
    ctp ↦ᵣ wctp ∗
    ct3 ↦ᵣ w3 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt finish ∗
    (pc_b ^+ allocator_shadow_import_off)%a ↦ₐ
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    ([∗ list] a ∈ finz.seq_between next b, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
    ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 9)%a ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (finish - heap_b))%a ∗
       ct3 ↦ᵣ WInt (next - heap_b) ∗
       ca2 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt finish ∗
       (pc_b ^+ allocator_shadow_import_off)%a
         ↦ₐ WCap true RW Global shadow_b shadow_e shadow_b ∗
       ([∗ list] a ∈ finz.seq_between next b,
          a ↦ₛ ShadowQuarantined ∗ addr_alloc a Unclaimed) ∗
       ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
       codefrag pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hnext Hbase Hrange.
    iIntros "(HPC & Hctp & Hct3 & Hca2 & Hct0 & Hct1 & Hct2 & Himport & Hheader & Hpayload &
      Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hbase.
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sh := (shadow_b ^+ (next - heap_b))%a).
    set (sb := (shadow_b ^+ (b - heap_b))%a).
    set (se := (shadow_b ^+ (finish - heap_b))%a).
    assert (Hshadow : (shadow_b <= sh /\ sh < sb /\ sb < se /\ se <= shadow_e)%a).
    { subst sh sb se. solve_addr. }

    (* Block 4: fetch the shadow capability *)
    focus_block 4 "Hcode_main" of allocator_malloc_blocks at pc_a as a_fetch Ha_fetch
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_fetch_spec with "[- $HPC $Hctp $Hct3 $Hca2 $Hcode $Himport]");
      [done|solve_addr| |done|apply allocator_shadow_import_not_heap|done|done|done|].
    { apply withinBounds_true_iff. rewrite /allocator_shadow_import_off. solve_addr. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hcode)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 5: translate the header address to its shadow entry *)
    focus_block 5 "Hcode_main" of allocator_malloc_blocks at pc_a as a_translate Ha_translate
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    replace (b - heap_b - 3)%Z with (next - heap_b)%Z by solve_addr.
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    { transitivity (Some sh); subst sh; solve_addr. }
    (* Mov ca2 allocator_header_words. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 6: paint the header words quarantined *)
    focus_block 6 "Hcode_main" of allocator_malloc_blocks at pc_a as a_hpaint Ha_hpaint
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    replace 3%Z with (b - next)%Z by solve_addr.
    iApply (allocator_paint_spec ShadowLive ShadowQuarantined ctp ca2 E RX Global
      pc_b pc_e a_hpaint next b sh sb emp (λ a, addr_alloc a Unclaimed)
      with "[- $HPC $Hctp $Hca2 $Hcode $Hheader]");
      [done|solve_addr|done|solve_addr|solve_addr|subst sh sb; solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sh. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_unclaimed. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hheader & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 7: the payload size *)
    focus_block 7 "Hcode_main" of allocator_malloc_blocks at pc_a as a_count Ha_count
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 8: store [ShadowLive] over the payload *)
    focus_block 8 "Hcode_main" of allocator_malloc_blocks at pc_a as a_paint Ha_paint
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_paint_spec ShadowLive ShadowLive ctp ca2 E RX Global
      pc_b pc_e a_paint b finish sb se emp (λ a, addr_alloc a (Claimed ι))
      with "[- $HPC $Hctp $Hca2 $Hcode $Hpayload]");
      [done|solve_addr|done|solve_addr|solve_addr|subst sb se; solve_addr| | |by left|].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sb. solve_addr. }
    { repeat constructor; set_solver. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hpayload & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 9)%a.
    iApply "Hφ". iFrame.
  Qed.

End AllocatorMallocTranslatePaintBlocks5.
