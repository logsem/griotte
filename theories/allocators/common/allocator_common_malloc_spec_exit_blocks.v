From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.common Require Import allocator_common_spec_states.

(** * Malloc, the exit segment

    The exit segment [allocator_malloc_exit_code] of [malloc] is shared by the
    allocators. Block 0 sets [ALLOC_INVALID], block 1 sets [ALLOC_NO_MEMORY],
    and block 2 returns. *)

Section AllocatorMallocExitBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {MP : MachineParameters}.
  Context {th : Thread} {CL : CritLink Σ th}.

  (** Block 2: return. *)
  Lemma allocator_malloc_exit_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret : LWord)
    (mie : InterruptStatus)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_malloc_exit_code pc_b pc_e pc_a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    default mie (jalr_target_mie wret.(lw)) = mie ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_exit_block_offset 2) ∗
    cra ↦ᵣ wret ∗
    MIE ↦ₜ mie ∗
    codefrag_pers pc_a allocator_malloc_exit_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       MIE ↦ₜ mie ∗
       codefrag_pers pc_a allocator_malloc_exit_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow) Htgt Hkeep.
    iIntros "(HPC & Hcra & Hmie & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_exit_unfold_code "Hcode_main".

    (* Block 2: return *)
    focus_block 2 "Hcode_main" of allocator_malloc_exit_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hmie $Hcode]"); [solve_addr|done|done|done|].
    iNext. iIntros "(HPC & Hcra & Hmie & _ & Hlc)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  (** Blocks 0 and 2: set [ALLOC_INVALID] and return. *)
  Lemma allocator_malloc_exit_reject_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (mie : InterruptStatus)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_malloc_exit_code pc_b pc_e pc_a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    default mie (jalr_target_mie wret.(lw)) = mie ->
    PC ↦ₚ Cap RX Global pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    MIE ↦ₜ mie ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_malloc_exit_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       MIE ↦ₜ mie ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_malloc_exit_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros Hbounds Htgt Hkeep. pose proof Hbounds as (Hpc & Hpc_shadow).
    iIntros "(HPC & Hcra & Hmie & Hca0 & Hca1 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_exit_unfold_code "Hcode_main".

    (* Block 0: set ALLOC_INVALID *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ALLOC_INVALID. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_exit_block_offset 2).
    iApply (allocator_malloc_exit_return_spec with "[- $HPC $Hcra $Hmie $Hcode_main]");
      [done|done|done|].
    iNext. iIntros "(HPC & Hcra & Hmie & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  (** Blocks 1 and 2: set [ALLOC_NO_MEMORY] and return. *)
  Lemma allocator_malloc_exit_oom_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (mie : InterruptStatus)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_malloc_exit_code pc_b pc_e pc_a ->
    jalr_target_ok cnull cra wret.(lw) = true ->
    default mie (jalr_target_mie wret.(lw)) = mie ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_malloc_exit_block_offset 1) ∗
    cra ↦ᵣ wret ∗
    MIE ↦ₜ mie ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_malloc_exit_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       MIE ↦ₜ mie ∗
       ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_malloc_exit_code ∗
       £ 1
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros Hbounds Htgt Hkeep. pose proof Hbounds as (Hpc & Hpc_shadow).
    iIntros "(HPC & Hcra & Hmie & Hca0 & Hca1 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_malloc_exit_unfold_code "Hcode_main".

    (* Block 1: set ALLOC_NO_MEMORY *)
    focus_block 1 "Hcode_main" of allocator_malloc_exit_blocks at pc_a as a_oom Ha_oom
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ALLOC_NO_MEMORY. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_malloc_exit_block_offset 2).
    iApply (allocator_malloc_exit_return_spec with "[- $HPC $Hcra $Hmie $Hcode_main]");
      [done|done|done|].
    iNext. iIntros "(HPC & Hcra & Hmie & _ & Hlc)".
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorMallocExitBlocks.
