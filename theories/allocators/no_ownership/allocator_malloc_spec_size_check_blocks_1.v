From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.no_ownership Require Import allocator_malloc_spec_states.

(** * Malloc, block 0: the check of the requested size

    Block 0 checks that [ca0] holds a positive integer. On success, the
    group ends at block 1. On failure, it continues at block 9, which sets
    [ALLOC_INVALID], and returns through block 11. *)

Section AllocatorMallocSizeCheckBlocks1.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_malloc_size_check_valid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    allocator_positive_size wreq.(lw) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ca0 ↦ᵣ wreq ∗
    ct3 ↦ᵣ wtmp ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 1)%a ∗
       ca0 ↦ᵣ wreq ∗
       ct3 ↦ᵣ - ∗
       codefrag pc_a allocator_malloc_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & _ & _) (n & Hreq & Hpositive).
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(HPC & Hca0 & Hct3 & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 0: the size check *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_int n 0) /wt_int Z.sub_diag.
    (* Jnz .malloc_invalid ct3. *)
    iInstr "Hcode".
    (* Lt ct3 0 ca0. *)
    iInstr "Hcode".
    replace (0 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_size_ok ct3. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_malloc_block_offset 1)%a.
    iApply "Hφ". iFrame.
  Qed.

  (** Blocks 9 and 11: set [ALLOC_INVALID] and return. *)
  Lemma allocator_malloc_reject_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_malloc_block_offset 9)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
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

    (* Block 9: set ALLOC_INVALID *)
    focus_block 9 "Hcode_main" of allocator_malloc_blocks at pc_a as a_invalid Ha_invalid
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Mov ca0 ALLOC_INVALID. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_malloc_block_offset 11)%a);
        offsets_compute; solve_addr. }
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

  Lemma allocator_malloc_size_check_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wtmp wca1 wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_malloc_code_bounds pc_b pc_e pc_a ->
    ¬ allocator_positive_size wreq.(lw) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    ct3 ↦ᵣ wtmp ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a allocator_malloc_code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       ct3 ↦ᵣ - ∗
       cnull ↦ᵣ WInt 0 ∗
       codefrag pc_a allocator_malloc_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds Hinvalid. pose proof Hbounds as (Hpc & _ & _).
    destruct wreq as [wreq π]; cbn in Hinvalid.
    iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct3 & Hcnull & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_unfold_code "Hcode_main".

    (* Block 0: the size check fails *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    destruct (is_z wreq) eqn:Hreq_z.
    - destruct wreq; cbn in *; try done.
      rewrite (encodeWordType_correct_int z 0) /wt_int Z.sub_diag.
      (* Jnz .malloc_invalid ct3. *)
      iInstr "Hcode".
      (* Lt ct3 0 ca0. *)
      iInstr "Hcode".
      destruct (decide (0 < z)%Z) as [Hzpos|Hznonpos].
      { exfalso. apply Hinvalid. exists z. split; [reflexivity|exact Hzpos]. }
      replace (0 <? z)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      (* Jnz .malloc_size_ok ct3. *)
      iInstr "Hcode".
      (* Jmp .malloc_invalid. *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_malloc_block_offset 9)%a.
      iApply (allocator_malloc_reject_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hcode_main]");
        first done.
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & Hcode_main & Hlc)".
      iApply "Hφ". iFrame.
    - assert (Hnonzero : WInt (encodeWordType wreq - encodeWordType (WInt 0)) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq (WInt 0)) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType (WInt 0)) by lia.
        destruct wreq; cbn in Hreq_z, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hencode); contradiction. }
      (* Jnz .malloc_invalid ct3. *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      change_pc_to (pc_a ^+ allocator_malloc_block_offset 9)%a.
      iApply (allocator_malloc_reject_spec with "[- $HPC $Hcra $Hca0 $Hca1 $Hcnull $Hcode_main]");
        first done.
      iNext. iIntros "(HPC & Hcra & Hca0 & Hca1 & Hcnull & Hcode_main & Hlc)".
      iApply "Hφ". iFrame.
  Qed.

End AllocatorMallocSizeCheckBlocks1.
