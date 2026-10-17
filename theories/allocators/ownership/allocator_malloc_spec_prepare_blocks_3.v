From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_malloc_spec_states.
From griotte.allocators.common Require Import allocator_common_malloc_spec_exit_blocks.

(** * Malloc, block 2: the capacity check, the payload and the header

    Block 2 reloads the heap root from the bump slot and checks the remaining
    capacity. On success, it bounds the payload capability, which is rebased
    to the fresh identifier [ι] of the payload, and writes the header, with
    the owner identifier [o] held in [ctp]; the group ends at block 3. On an
    exhausted heap, it continues at the exit segment (block 5), which sets
    [ALLOC_NO_MEMORY] and returns. *)

Section AllocatorMallocPrepareBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_malloc_prepare_success_spec
    (E : coPset) (pc_b pc_e pc_a next b finish : Addr) (n o : Z) (πn : option AId) (ι : AId)
    (w0 w1 w2 w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (pc_b + allocator_malloc_pcc_off)%a = Some pc_a ->
    (0 < n)%Z ->
    (heap_b < next)%a ->
    (next + allocator_header_words)%a = Some b ->
    (b + n)%a = Some finish ->
    (finish <= heap_e)%a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 2)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca1 ↦ᵣ WInt n @@? πn ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ca3 ↦ᵣ w3 ∗
    ca4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    (pc_b ^+ allocator_shadow_import_off)%a ↦ₐ□
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    allocator_range_memory next b ∗
    alloc_obj ι b finish ∗
    ι ↦st{1} ALive ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 3)%a ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       ca1 ↦ᵣ WInt n @@? πn ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt finish ∗
       ca3 ↦ᵣ WInt 0 ∗
       ca4 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       ca2 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
       allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       (pc_b ^+ allocator_shadow_import_off)%a ↦ₐ□
         WCap true RW Global shadow_b shadow_e shadow_b ∗
       allocator_header next b finish (o, 0%Z) ∗
       ι ↦st{1} ALive ∗
       codefrag_pers pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & Hcgp_pc) Hpcc Hpositive Hnext Hbase Hfinish Hroom.
    iIntros "(HPC & Hcgp & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hslot &
      #Himport & Hheader &
      #Hobj & Htok & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hbase.
    pose proof allocator_cgp_size.
    pose proof heap_valid.

    (* Block 2: the capacity check, the payload and the header *)
    focus_block 2 "Hcode_main" of allocator_malloc_blocks at pc_a as a_prep Ha_prep
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iPoseProof deref_res_none as "-#Hdw".
    (* CLoad ct0 cgp. *)
    iInstrApply "Hcode" wp_load_success_exact
      with "[$HPC $Hct0 $Hcgp $Hslot $Hdw]"
      as "(HPC & Hct0 & Hcgp & Hslot & _)".
    { apply allocator_cgp_not_shadow. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ca3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ca1. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with false
      by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .malloc_no_memory ca3. *)
    iInstr "Hcode".
    (* Add ct1 ct1 allocator_header_words. *)
    iInstr "Hcode".
    replace (next + 3)%Z with (finz.to_z b) by solve_addr.
    (* Add ct2 ct1 ca1. *)
    iInstr "Hcode".
    replace (b + n)%Z with (finz.to_z finish) by solve_addr.
    (* Mov ca4 ct0. *)
    iInstr "Hcode".
    (* Lea ca4 allocator_header_words. *)
    iInstr "Hcode".
    (* Subseg ca4 ct1 ct2. *)
    iInstrApply "Hcode" (wp_subseg_rebase _ _ _ _ _ _ _ _ ca4 ct1 ct2 RW Global heap_b heap_e b _ b _ finish
              b finish _ ι 1 ALive)
      with "[$HPC $Hct4 $Hct1 $Hct2 $Hobj $Htok]"
      as "(HPC & Hct1 & Hct2 & Hct4 & _ & Htok)".
    { rewrite /isWithin. solve_addr. }
    { solve_addr. }
    { by left. }
    { done. }

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
    iPoseProof deref_res_none as "-#Hdw".
    (* Store ct0 ctp 1. *)
    iInstrApply "Hcode" (wp_store_success_reg_imm _ _ _ _ _ _ _ _ _ _ ct0 ctp wr1 _ _ _ _ _ (next ^+ 1)%a 1)
      with "[$HPC $Hct0 $Hctp $Hr1 $Hdw]"
      as "(HPC & Hctp & Hct0 & Hr1 & _)".
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    iPoseProof deref_res_none as "-#Hdw".
    (* Store ct0 0 2. *)
    iInstrApply "Hcode" (wp_store_success_z_imm _ _ _ _ _ _ _ _ _ _ ct0 0 wr2 _ _ _ _ _ (next ^+ 2)%a 2)
      with "[$HPC $Hct0 $Hr2 $Hdw]"
      as "(HPC & Hct0 & Hr2 & _)".
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    (* Mov ca2 ca4. *)
    iInstr "Hcode".
    (* The shadow capability, at the first import. *)
    pose proof allocator_shadow_import_not_heap.
    rewrite /allocator_malloc_pcc_off in Hpcc.
    (* Auipcc ctp ".Limport_shadow". *)
    iInstr "Hcode".
    { instantiate (1 := (pc_b ^+ allocator_shadow_import_off)%a).
      rewrite /allocator_shadow_import_off. offsets_compute; solve_addr. }
    (* CLoad ctp ctp 0. *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hpc_shadow.
      apply withinBounds_true_iff. offsets_compute; solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iEval (cbn [load_word]) in "Hctp".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 3)%a.
    iApply "Hφ". iFrame "∗ Hcode_main Himport". rewrite /allocator_header /=. iFrame "∗". done.
  Qed.

  (** Block 5, the exit segment: set [ALLOC_NO_MEMORY] and return. *)
  Lemma allocator_malloc_oom_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_no_memory_offset)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ φ FailedV ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds. pose proof Hbounds as (Hpc & _ & _).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & #Hcode_main & Hfailed & Hφ)".
    iDestruct (allocator_malloc_exit_acc with "Hcode_main") as "#Hcode".
    assert ((pc_a ^+ allocator_malloc_no_memory_offset)%a =
      ((pc_a ^+ allocator_malloc_block_offset 5) ^+ allocator_malloc_exit_block_offset 1)%a)
      as -> by (cbn in Hpc; offsets_compute; solve_addr).
    iApply (allocator_malloc_exit_oom_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hcode]");
      first by apply allocator_malloc_exit_bounds.
    iFrame "Hfailed".
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  Lemma allocator_malloc_prepare_oom_spec
    (E : coPset) (pc_b pc_e pc_a next : Addr) (n : Z) (πn : option AId)
    (wret wca0 w0 w1 w2 w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    (0 < n)%Z ->
    (heap_b < next /\ next <= heap_e)%a ->
    (heap_e - next - allocator_header_words < n)%Z ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 2)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ WInt n @@? πn ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ca3 ↦ᵣ w3 ∗
    ca4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ φ FailedV ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
       ca1 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ca3 ↦ᵣ - ∗
       ca4 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
       codefrag_pers pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds Hpositive Hnext Hoom. pose proof Hbounds as (Hpc & Hpc_shadow & Hcgp_pc).
    iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 &
      Hslot & #Hcode_main & Hfailed & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".
    unfold allocator_header_words in Hoom.
    pose proof allocator_cgp_size.

    (* Block 2: the capacity check fails *)
    focus_block 2 "Hcode_main" of allocator_malloc_blocks at pc_a as a_prep Ha_prep
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iPoseProof deref_res_none as "-#Hdw".
    (* CLoad ct0 cgp. *)
    iInstrApply "Hcode" wp_load_success_exact
      with "[$HPC $Hct0 $Hcgp $Hslot $Hdw]"
      as "(HPC & Hct0 & Hcgp & Hslot & _)".
    { apply allocator_cgp_not_shadow. }
    { intros _. left. apply allocator_heap_root_authority. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between. solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ca3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ca3 ca3 ca1. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_no_memory ca3. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_malloc_no_memory_offset)%a);
        offsets_compute; solve_addr. }
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    iApply (allocator_malloc_oom_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcode_main]");
      first done.
    iFrame "Hfailed".
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & _)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorMallocPrepareBlocks3.
