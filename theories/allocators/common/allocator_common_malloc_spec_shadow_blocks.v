From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.common Require Import allocator_common_spec_states.

(** * Malloc, the shadow segment

    The shadow segment [allocator_malloc_shadow_code] of [malloc] is shared
    by the allocators. Block 0 is the zeroing loop over the payload
    [b, finish), through the payload capability in [ca2]. Block 1
    translates the header address [next] to its shadow entry, through the
    shadow capability in [ctp]. Block 2 paints the three header words
    quarantined. Block 3 loads the payload size, and block 4 stores
    [ShadowLive] over the payload, whose cells are claimed by [ι]. *)

Section AllocatorMallocShadowBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorCommonLayoutWf}.

  Lemma allocator_malloc_zero_spec
    (E : coPset) (pc_b pc_e pc_a b finish : Addr) (ι : AId) (q : Qp) (w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_malloc_shadow_code pc_b pc_e pc_a ->
    (heap_b <= b /\ b < finish /\ finish <= heap_e)%a ->
    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    ca2 ↦ᵣ (Cap RW Global b finish b) @@ ι ∗
    ι ↦st{q} ALive ∗
    ct2 ↦ᵣ WInt finish ∗
    ca3 ↦ᵣ w3 ∗
    allocator_range_memory b finish ∗
    codefrag_pers pc_a allocator_malloc_shadow_code ∗
    ▷ (PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_shadow_block_offset 1) ∗
       ca2 ↦ᵣ (Cap RW Global b finish finish) @@ ι ∗
       ι ↦st{q} ALive ∗
       ct2 ↦ᵣ WInt finish ∗
       ca3 ↦ᵣ WInt 0 ∗
       ([∗ list] a ∈ finz.seq_between b finish, a ↦ₐ WInt 0) ∗
       codefrag_pers pc_a allocator_malloc_shadow_code
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow) Hrange.
    iIntros "(HPC & Hca2 & Hst & Hct2 & Hct3 & Hmem & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_shadow_unfold_code "Hcode_main".

    (* Block 0: zero the payload *)
    focus_block 0 "Hcode_main" of allocator_malloc_shadow_blocks at pc_a as a_zero Ha_zero
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_zero_spec ca2 ct2 ca3 E RX Global pc_b pc_e a_zero
      RW Global b finish (Some ι) (DerefLive ι q) w3
      with "[- $HPC $Hca2 $Hst $Hct2 $Hct3 $Hmem $Hcode]");
      [done|solve_addr|done|done|solve_addr| |done|].
    { repeat constructor; set_solver. }
    iNext. iIntros "(HPC & Hca2 & Hst & Hct2 & Hct3 & Hzeros & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_shadow_block_offset 1).
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  Lemma allocator_malloc_translate_paint_spec
    (E : coPset) (pc_b pc_e pc_a next b finish : Addr) (ι : AId) (w3 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_malloc_shadow_code pc_b pc_e pc_a ->
    (heap_b < next)%a ->
    (next + allocator_header_words)%a = Some b ->
    (b < finish /\ finish <= heap_e)%a ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_shadow_block_offset 1) ∗
    ctp ↦ᵣ Cap RW Global shadow_b shadow_e shadow_b ∗
    ca3 ↦ᵣ w3 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt finish ∗
    ([∗ list] a ∈ finz.seq_between next b, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
    ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
    codefrag_pers pc_a allocator_malloc_shadow_code ∗
    ▷ (PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_shadow_block_offset 5) ∗
       ctp ↦ᵣ Cap RW Global shadow_b shadow_e (shadow_b ^+ (finish - heap_b)) ∗
       ca3 ↦ᵣ WInt (next - heap_b) ∗
       ca2 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt finish ∗
       ([∗ list] a ∈ finz.seq_between next b,
          a ↦ₛ ShadowQuarantined ∗ addr_alloc a Unclaimed) ∗
       ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
       codefrag_pers pc_a allocator_malloc_shadow_code
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow) Hnext Hbase Hrange.
    iIntros "(HPC & Hctp & Hct3 & Hca2 & Hct0 & Hct1 & Hct2 & Hheader & Hpayload &
      #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_shadow_unfold_code "Hcode_main".
    unfold allocator_header_words in Hbase.
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sh := shadow_b ^+ (next - heap_b)).
    set (sb := shadow_b ^+ (b - heap_b)).
    set (se := shadow_b ^+ (finish - heap_b)).
    assert (Hshadow : (shadow_b <= sh /\ sh < sb /\ sb < se /\ se <= shadow_e)%a).
    { subst sh sb se. solve_addr. }

    (* Block 1: translate the header address to its shadow entry *)
    focus_block 1 "Hcode_main" of allocator_malloc_shadow_blocks at pc_a as a_translate Ha_translate
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetB ca3 ct0. *)
    iInstr "Hcode".
    (* Sub ca3 ct1 ca3. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 allocator_header_words. *)
    iInstr "Hcode".
    replace (b - heap_b - 3)%Z with (next - heap_b)%Z by solve_addr.
    (* Lea ctp ctp ca3. *)
    iInstr "Hcode".
    { transitivity (Some sh); subst sh; solve_addr. }
    (* Mov ca2 allocator_header_words. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 2: paint the header words quarantined *)
    focus_block 2 "Hcode_main" of allocator_malloc_shadow_blocks at pc_a as a_hpaint Ha_hpaint
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    replace 3%Z with (b - next)%Z by solve_addr.
    iApply (allocator_paint_spec ShadowLive ShadowQuarantined ctp ca2 E RX Global
      pc_b pc_e a_hpaint next b sh sb emp (λ a, addr_alloc a Unclaimed)
      with "[- $HPC $Hctp $Hca2 $Hcode $Hheader]");
      [done|solve_addr|done|solve_addr|solve_addr|subst sh sb; solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sh. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_unclaimed. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hheader & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 3: the payload size *)
    focus_block 3 "Hcode_main" of allocator_malloc_shadow_blocks at pc_a as a_count Ha_count
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 4: store [ShadowLive] over the payload *)
    focus_block 4 "Hcode_main" of allocator_malloc_shadow_blocks at pc_a as a_paint Ha_paint
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_paint_spec ShadowLive ShadowLive ctp ca2 E RX Global
      pc_b pc_e a_paint b finish sb se emp (λ a, addr_alloc a (Claimed ι))
      with "[- $HPC $Hctp $Hca2 $Hcode $Hpayload]");
      [done|solve_addr|done|solve_addr|solve_addr|subst sb se; solve_addr| | |by left|].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sb. solve_addr. }
    { repeat constructor; set_solver. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hpayload & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_shadow_block_offset 5).
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorMallocShadowBlocks.
