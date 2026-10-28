From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_malloc_spec_states.
From griotte.allocators.common Require Import allocator_common_malloc_spec_exit_blocks.

(** * Malloc, block 1: the check of the requested size

    Block 1 checks that [ca1] holds a positive integer. On success, the
    group ends at block 2. On failure, it continues at the exit segment
    (block 5), which sets [ALLOC_INVALID] and returns. *)

Section AllocatorMallocSizeCheckBlocks2.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_malloc_size_check_valid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    allocator_positive_size wreq.(lw) ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1) ∗
    ca1 ↦ᵣ wreq ∗
    ca3 ↦ᵣ wtmp ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ (PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 2) ∗
       ca1 ↦ᵣ wreq ∗
       ca3 ↦ᵣ - ∗
       codefrag_pers pc_a allocator_malloc_code
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & _ & _) (n & Hreq & Hpositive).
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(HPC & Hca1 & Hct3 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 1: the size check *)
    focus_block 1 "Hcode_main" of allocator_malloc_blocks at pc_a as a_size Ha_size
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetWType ca3 ca1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_int n 0) /wt_int Z.sub_diag.
    (* Jne .malloc_invalid ca3 0. *)
    iInstr "Hcode".
    (* Lt ca3 0 ca1. *)
    iInstr "Hcode".
    replace (0 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jne .malloc_size_ok ca3 0. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 2).
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  (** Block 5, the exit segment: set [ALLOC_INVALID] and return. *)
  Lemma allocator_malloc_reject_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_invalid_offset) ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros Hbounds Htgt.
    iIntros "(HPC & Hcra & Hca0 & Hca1 & #Hcode_main & Hφ)".
    iDestruct (allocator_malloc_exit_acc with "Hcode_main") as "#Hcode".
    iApply (allocator_malloc_exit_reject_spec with
      "[- $HPC $Hcra $Hca0 $Hca1 $Hcode]");
      [by apply allocator_malloc_exit_bounds | done |].
    iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  Lemma allocator_malloc_size_check_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wca0 wreq wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    ¬ allocator_positive_size wreq.(lw) ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1) ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wca0 ∗
    ca1 ↦ᵣ wreq ∗
    ca3 ↦ᵣ wtmp ∗
    codefrag_pers pc_a allocator_malloc_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       ca3 ↦ᵣ - ∗
       codefrag_pers pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros Hbounds Hinvalid Htgt. pose proof Hbounds as (Hpc & _ & _).
    destruct wreq as [wreq π]; cbn in Hinvalid.
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct3 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 1: the size check fails *)
    focus_block 1 "Hcode_main" of allocator_malloc_blocks at pc_a as a_size Ha_size
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetWType ca3 ca1. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    destruct (is_z wreq) eqn:Hreq_z.
    - destruct wreq; cbn in *; try done.
      rewrite (encodeWordType_correct_int z 0) /wt_int Z.sub_diag.
      (* Jne .malloc_invalid ca3 0. *)
      iInstr "Hcode".
      (* Lt ca3 0 ca1. *)
      iInstr "Hcode".
      destruct (decide (0 < z)%Z) as [Hzpos|Hznonpos].
      { exfalso. apply Hinvalid. exists z. split; [reflexivity|exact Hzpos]. }
      replace (0 <? z)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      (* Jne .malloc_size_ok ca3 0. *)
      iInstr "Hcode".
      (* Jmp .malloc_invalid. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_malloc_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_malloc_invalid_offset).
      iApply (allocator_malloc_reject_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcode_main]");
        [done|done|].
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & Hlc)".
      iApply "Hφ". iFrame "∗ Hcode_main".
    - assert (Hnonzero : WInt (encodeWordType wreq - encodeWordType (WInt 0)) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq (WInt 0)) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType (WInt 0)) by lia.
        destruct wreq; cbn in Hreq_z, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hencode); contradiction. }
      (* Jne .malloc_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_malloc_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      change_pc_to (pc_a ^+ allocator_malloc_invalid_offset).
      iApply (allocator_malloc_reject_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcode_main]");
        [done|done|].
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & _ & Hlc)".
      iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorMallocSizeCheckBlocks2.
