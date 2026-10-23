From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * The blocks of [stats_read]

    Block 0 tests the lock, the first global of [stats], at [cgp]. When it
    is free, block 1 takes it ([stats_read_take_spec]) and block 2 loads
    through the pointer of the caller, in [ca0] ([stats_read_load_spec]).
    Block 3 releases the lock and returns ([stats_read_release_spec]). When
    the lock is taken, block 4 returns [EBUSY]: this case is not specified,
    since the invariant of [stats] gives a free lock.

    The load is the fault site of [stats]: only its successful execution
    is specified here. The specifications are stated over plain points-to:
    the lock is the cell [cgp_b]. *)

Section Error_Handling_Read_Blocks.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  (** The lock is free: take it, up to the load. *)
  Lemma stats_read_take_spec
    (pc_b pc_e cgp_b cgp_e : Addr)
    (wct0 : LWord) :
    stats_code_bounds pc_b pc_e ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_read")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ct0 ↦ᵣ wct0 ∗
    cgp_b ↦ₐ WInt 0 ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_load")%a ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        ct0 ↦ᵣ WInt 0 ∗
        cgp_b ↦ₐ WInt 1 ∗
        codefrag_pers pc_b stats_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow)
      "(HPC & Hcgp & Hct0 & Hlock & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.

    (* Block 0: the lock test *)
    focus_block (stats_block ".Lstats_read") "Hcode_stats" of stats_blocks at pc_b
      as a_test Ha_test "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* CLoad ct0 cgp 0 *)
    iInstr "Hcode".
    { reflexivity. }
    { split; first done. apply withinBounds_true_iff; solve_addr. }
    iEval (rewrite /lload_word /lift_word /load_word /=) in "Hct0".
    (* Jne .Lread_busy ct0 0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".

    (* Block 1: take the lock *)
    focus_block (stats_block ".Lread_lock") "Hcode_stats" of stats_blocks at pc_b
      as a_lock Ha_lock "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 1 0 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    assert ((a_lock ^+ 1)%a = (pc_b ^+ stats_label ".Lread_load")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_stats".
  Qed.

  (** The load through the pointer of the caller, when it succeeds. *)
  Lemma stats_read_load_spec
    (pc_b pc_e : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (w : LWord) :
    stats_code_bounds pc_b pc_e ->
    readAllowed p = true ->
    withinBounds b e a = true ->
    is_shadow_address a = false ->
    is_heap_cap w.(lw) = false ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_load")%a ∗
    ca0 ↦ᵣ WCap true p g b e a ∗
    a ↦ₐ w ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_release")%a ∗
        ca0 ↦ᵣ lload_word p w ∗
        a ↦ₐ w ∗
        codefrag_pers pc_b stats_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hread Ha_bounds Ha_shadow Hw_nonheap)
      "(HPC & Hca0 & Ha & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.
    (* Block 2: the load *)
    focus_block (stats_block ".Lread_load") "Hcode_stats" of stats_blocks at pc_b
      as a_load Ha_load "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* CLoad ca0 ca0 0 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    assert ((a_load ^+ 1)%a = (pc_b ^+ stats_label ".Lread_release")%a) as ->
      by (offsets_compute; solve_addr).
    iApply "Hpost"; iFrame "∗ Hcode_stats".
  Qed.

  (** Release the lock, and return. *)
  Lemma stats_read_release_spec
    (pc_b pc_e cgp_b cgp_e : Addr)
    (wlock wca1 wcra : LWord) :
    stats_code_bounds pc_b pc_e ->
    (cgp_b < cgp_e)%a ->
    is_shadow_address cgp_b = false ->
    jalr_target_ok cnull cra wcra.(lw) = true ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lread_release")%a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    ca1 ↦ᵣ wca1 ∗
    cra ↦ᵣ wcra ∗
    cgp_b ↦ₐ wlock ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wcra ∗
        cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
        ca1 ↦ᵣ WInt 0 ∗
        cra ↦ᵣ wcra ∗
        cgp_b ↦ₐ WInt 0 ∗
        codefrag_pers pc_b stats_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hcgp_bounds Hcgp_shadow Htgt)
      "(HPC & Hcgp & Hca1 & Hcra & Hlock & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    stats_unfold_code.

    (* Block 3: release the lock, return *)
    focus_block (stats_block ".Lread_release") "Hcode_stats" of stats_blocks at pc_b
      as a_release Ha_release "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* Store cgp 0 0 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iApply "Hpost"; iFrame "∗ Hcode_stats".
  Qed.

End Error_Handling_Read_Blocks.
