From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.no_ownership Require Import allocator_malloc_spec_states.

(** * Malloc, block 1: the capacity check, the payload and the header

    Block 1 reloads the heap root from the bump slot and checks the remaining
    capacity. On success, it bounds the payload capability, which is rebased
    to the fresh identifier [ι] of the payload, and writes the header; the
    group ends at block 2. On an exhausted heap, it continues at block 10,
    which sets [ALLOC_NO_MEMORY], and returns through block 11. *)

Section AllocatorMallocPrepareBlocks2.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_malloc_prepare_success_spec
    (E : coPset) (pc_b pc_e pc_a next b finish : Addr) (n : Z) (πn : option AId) (ι : AId)
    (w0 w1 w2 w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (0 < n)%Z ->
    (heap_b < next)%a ->
    (next + allocator_header_words)%a = Some b ->
    (b + n)%a = Some finish ->
    (finish <= heap_e)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    allocator_range_memory next b ∗
    alloc_obj ι b finish ∗
    ι ↦st{1} ALive ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 2)%a ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca0 ↦ᵣ WInt n @@? πn ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt finish ∗
       ct3 ↦ᵣ WInt 0 ∗
       ct4 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       ca2 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       allocator_header next b finish (0%Z, 0%Z) ∗
       ι ↦st{1} ALive ∗
       codefrag pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) Hpositive Hnext Hbase Hfinish Hroom.
    iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hslot & Hheader &
      #Hobj & Htok & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hbase.
    pose proof allocator_cgp_size.
    pose proof heap_valid.

    (* Block 1: the capacity check, the payload and the header *)
    focus_block 1 "Hcode_main" of allocator_malloc_blocks at pc_a as a_prep Ha_prep
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { apply allocator_cgp_not_shadow. }
    { done. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca0. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with false
      by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .malloc_no_memory ct3. *)
    iInstr "Hcode".
    (* Add ct1 ct1 allocator_header_words. *)
    iInstr "Hcode".
    replace (next + 3)%Z with (finz.to_z b) by solve_addr.
    (* Add ct2 ct1 ca0. *)
    iInstr "Hcode".
    replace (b + n)%Z with (finz.to_z finish) by solve_addr.
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    (* Lea ct4 allocator_header_words. *)
    iInstr "Hcode".
    (* Subseg ct4 ct1 ct2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_subseg_rebase _ _ _ _ _ _ _ _ ct4 ct1 ct2 RW Global heap_b heap_e b _ b _ finish
              b finish _ ι 1 ALive with "[$HPC $Hi $Hct4 $Hct1 $Hct2 $Hobj $Htok]");
      try solve_pure.
    { rewrite /isWithin. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct1 & Hct2 & Hct4 & _ & Htok)". wp_pure.
    iSpecialize ("Hcode" with "Hi").

    (* Write the header from the header cells. *)
    assert (Hnextb : (next < b)%a) by solve_addr.
    assert (Hsecondb : (next ^+ 1 < b)%a) by solve_addr.
    assert (Hthirdb : (next ^+ 2 < b)%a) by solve_addr.
    assert (Hthirdaddr : ((next ^+ 1)%a ^+ 1)%a = (next ^+ 2)%a) by solve_addr.
    assert (Hthirdend : ((next ^+ 2)%a ^+ 1)%a = b) by solve_addr.
    assert (Hempty : finz.seq_between b b = []) by (apply finz_seq_between_empty; solve_addr).
    iEval (rewrite /allocator_range_memory
      (finz_seq_between_cons next b Hnextb) big_sepL_cons
      (finz_seq_between_cons (next ^+ 1)%a b Hsecondb) big_sepL_cons
      Hthirdaddr (finz_seq_between_cons (next ^+ 2)%a b Hthirdb) big_sepL_cons
      Hthirdend Hempty) in "Hheader".
    iDestruct "Hheader" as "([%wend Hend] & [%wr1 Hr1] & [%wr2 Hr2] & _)".
    (* Store ct0 ct2. *)
    iInstr "Hcode".
    { eapply (disjoint_from_shadow_not_in heap_b heap_e next); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    (* Store ct0 0 1. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_z_imm _ _ _ _ _ _ _ _ _ _ ct0 0 wr1 _ _ _ _ _ (next ^+ 1)%a 1
      with "[$HPC $Hi $Hct0 $Hr1]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hr1)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Store ct0 0 2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_z_imm _ _ _ _ _ _ _ _ _ _ ct0 0 wr2 _ _ _ _ _ (next ^+ 2)%a 2
      with "[$HPC $Hi $Hct0 $Hr2]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hr2)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Mov ca2 ct4. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 2)%a.
    iApply "Hφ". iFrame. rewrite /allocator_header /=. iFrame. done.
  Qed.

  (** Blocks 10 and 11: set [ALLOC_NO_MEMORY] and return. *)
  Lemma allocator_malloc_oom_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 10)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
       ca1 ↦ᵣ WInt 0 ∗
       cnull ↦ᵣ WInt 0 ∗
       codefrag pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 10: set ALLOC_NO_MEMORY *)
    focus_block 10 "Hcode_main" of allocator_malloc_blocks at pc_a as a_oom Ha_oom
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ALLOC_NO_MEMORY. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 11: return *)
    focus_block 11 "Hcode_main" of allocator_malloc_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_return_spec with "[- $HPC $Hcra $Hcnull $Hcode]"); [solve_addr|done|].
    iNext. iIntros "(HPC & Hcra & Hcnull & Hcode & Hlc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_prepare_oom_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (n : Z) (πn : option AId)
    (wret w0 w1 w2 w3 w4 wa2 wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (0 < n)%Z ->
    (heap_b < next /\ next <= heap_e)%a ->
    (heap_e - next - allocator_header_words < n)%Z ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ca1 ↦ᵣ wca1 ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    cnull ↦ᵣ wnull ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
       ca1 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       cnull ↦ᵣ WInt 0 ∗
       allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       codefrag pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds Hpositive Hnext Hoom. pose proof Hbounds as (Hpc & Hpc_shadow & Hcgp_pc).
    iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcnull &
      Hslot & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hoom.
    pose proof allocator_cgp_size.

    (* Block 1: the capacity check fails *)
    focus_block 1 "Hcode_main" of allocator_malloc_blocks at pc_a as a_prep Ha_prep
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { apply allocator_cgp_not_shadow. }
    { done. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca0. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_no_memory ct3. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_malloc_block_offset 10)%a);
        offsets_compute; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    iApply (allocator_malloc_oom_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hcode_main]");
      first done.
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & Hcode_main & _)".
    iApply "Hφ". iFrame.
  Qed.

End AllocatorMallocPrepareBlocks2.
