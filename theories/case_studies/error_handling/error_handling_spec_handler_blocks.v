From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel proofmode.
From griotte Require Import error_handling_spec_states.

(** * The body of the error handler of [stats]

    The stackful handler of [stats] is called with [ca0] pointing to the
    [ErrorState] of the faulting context: word 0 holds the saved PC, an
    untagged capability, and words 1 to 15 the registers x1 to x15. It
    stores [EINVAL] in the [a0] slot (word [TrustedStack_offset_ca0]),
    moves the saved PC by one instruction, past the faulting load, puts 0
    (InstallContext) in [ca0], and returns to [cra].

    The specification is stated over plain points-to: it holds no
    invariant and no token, and frames whatever the caller holds. *)

Section Error_Handling_Handler_Blocks.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Lemma stats_handler_spec
    (pc_b pc_e : Addr)
    (p : Perm) (g : Locality) (b e a : Addr) (ws : list LWord)
    (p0 : Perm) (g0 : Locality) (b0 e0 a0 a0' : Addr)
    (wct0 wcra : LWord) :
    stats_code_bounds pc_b pc_e ->
    readAllowed p = true ->
    writeAllowed p = true ->
    isDL p = false ->
    isDRO p = false ->
    (b <= a)%a ->
    (a + ErrorState_size <= e)%Z ->
    disjoint_from_shadow a (a ^+ ErrorState_size)%a ->
    length ws = Z.to_nat ErrorState_size ->
    ws !! 0%nat = Some (lword_of_word (WCap false p0 g0 b0 e0 a0)) ->
    is_heap_address b0 = false ->
    (a0 + 1)%a = Some a0' ->
    jalr_target_ok cnull cra wcra.(lw) = true ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_b ^+ stats_label ".Lstats_handler")%a ∗
    ca0 ↦ᵣ WCap true p g b e a ∗
    ct0 ↦ᵣ wct0 ∗
    cra ↦ᵣ wcra ∗
    [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ [[ ws ]] ∗
    codefrag_pers pc_b stats_code ∗
    ▷ (PC ↦ₚ lupdatePcPerm wcra ∗
        ca0 ↦ᵣ WInt 0 ∗
        ct0 ↦ᵣ WCap false p0 g0 b0 e0 a0' ∗
        cra ↦ᵣ wcra ∗
        [[ a , (a ^+ ErrorState_size)%a ]] ↦ₐ
          [[ <[Z.to_nat TrustedStack_offset_ca0 := lword_of_word (WInt EINVAL)]>
               (<[0%nat := lword_of_word (WCap false p0 g0 b0 e0 a0')]> ws) ]] ∗
        codefrag_pers pc_b stats_code
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((HsubBounds & Hpc_shadow & Hpc_nonheap) Hread Hwrite Hdl Hdro Hb_a Ha_e
              Hes_shadow Hlen Hws0 Hb0_nonheap Ha0' Htgt)
      "(HPC & Hca0 & Hct0 & Hcra & Hes & Hcode_stats & Hpost)".
    iDestruct (codefrag_contiguous_region_pers with "Hcode_stats") as %Hpc_contiguous;
    cbn [length map encodeInstrsW] in Hpc_contiguous.
    rewrite /ErrorState_size in Ha_e Hes_shadow Hlen |- *.
    assert (is_shadow_address a = false) as Ha_shadow.
    { eapply disjoint_from_shadow_not_in; first exact Hes_shadow.
      apply withinBounds_true_iff; solve_addr. }
    assert ((a + 10)%a = Some (a ^+ 10%nat)%a) as Ha10 by solve_addr.
    assert (is_shadow_address (a ^+ 10%nat)%a = false) as Ha10_shadow.
    { eapply disjoint_from_shadow_not_in; first exact Hes_shadow.
      apply withinBounds_true_iff; solve_addr. }
    assert (∃ w10, ws !! 10%nat = Some w10) as [w10 Hws10].
    { apply lookup_lt_is_Some_2. rewrite Hlen. lia. }
    rewrite (region_pointsto_cells a); last (rewrite Hlen; solve_addr).
    stats_unfold_code.
    focus_block (stats_block ".Lstats_handler") "Hcode_stats" of stats_blocks at pc_b
      as a_handler Ha_handler "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iDestruct (big_sepL_insert_acc with "Hes") as "[Hes10 Hes]"; first exact Hws10.
    (* Store ca0 EINVAL 10 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    iDestruct ("Hes" with "Hes10") as "Hes".
    iDestruct (big_sepL_insert_acc with "Hes") as "[Hes0 Hes]".
    { rewrite list_lookup_insert_ne; [exact Hws0|lia]. }
    rewrite (_ : (a ^+ 0%nat)%a = a); last solve_addr.
    (* CLoad ct0 ca0 0 *)
    iInstr "Hcode".
    { by rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb0_nonheap. }
    { split; first done. apply withinBounds_true_iff; solve_addr. }
    rewrite /lload_word /lift_word /= load_word_no_dl_dro //.
    (* Lea ct0 ct0 1 *)
    iInstr "Hcode".
    (* Store ca0 ct0 0 *)
    iInstr "Hcode".
    { apply withinBounds_true_iff; solve_addr. }
    (* The saved PC is untagged: it is stored as is *)
    iEval (rewrite /lstore_word /lift_word /= /store_word) in "Hes0".
    iAssert (a ↦ₐ WCap false p0 g0 b0 e0 a0')%I with "[Hes0]" as "Hes0".
    { by destruct (canStore p (WCap false p0 g0 b0 e0 a0')). }
    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_stats".
    iDestruct ("Hes" with "Hes0") as "Hes".
    iApply "Hpost"; iFrame "∗ Hcode_stats".
    rewrite (region_pointsto_cells a); last (rewrite !length_insert Hlen; solve_addr).
    rewrite /TrustedStack_offset_ca0 /= list_insert_insert_ne //.
  Qed.

End Error_Handling_Handler_Blocks.
