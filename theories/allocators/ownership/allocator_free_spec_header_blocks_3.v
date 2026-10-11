From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, blocks 3 and 4: the local check of the header

    Block 3 fetches the shadow capability from the imports. Block 4 reads the
    shadow entries of the word below the requested base, which must be
    painted (the last header word), and of the base, which must be unpainted;
    then the end recorded in the header three words below the base, which
    must match the requested end, and the owner recorded in the next header
    word, which must match the owner [o] of the allocator capability, in
    [ca0]. The header is read only when both shadow checks pass. On success, the shadow cursor is at the base, the count of
    addresses to paint is in [ca2], and the group ends at block 5; otherwise
    at block 11. *)

Section AllocatorFreeHeaderBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_free_header_spec
    (E : coPset) (pc_b pc_e pc_a next b e eh : Addr) (o oh : Z) (s1 s2 : AllocStatus)
    (wctp w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    (s1 = ShadowQuarantined -> s2 = ShadowLive ->
      (heap_b + allocator_header_words < b)%Z) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 3)%a ∗
    ctp ↦ᵣ wctp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    (pc_b ^+ allocator_shadow_import_off)%a ↦ₐ
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    (b ^+ (-1))%a ↦ₛ s1 ∗
    b ↦ₛ s2 ∗
    (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
     then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
         ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
    else emp) ∗
    ca0 ↦ᵣ WInt o ∗
    codefrag pc_a allocator_free_code ∗
    ▷ ((pc_b ^+ allocator_shadow_import_off)%a ↦ₐ
         WCap true RW Global shadow_b shadow_e shadow_b ∗
       (b ^+ (-1))%a ↦ₛ s1 ∗
       b ↦ₛ s2 ∗
       (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
        then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
             ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
        else emp) ∗
       ca0 ↦ᵣ WInt o ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ct4 ↦ᵣ - ∗
       codefrag pc_a allocator_free_code ∗
       ((⌜s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 5)%a ∗
         ct3 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (b - heap_b))%a)
        ∨
        (⌜¬ (s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o)⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 11)%a ∗
         ct3 ↦ᵣ - ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ -))
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hbounds Hheader.
    iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca2 & Hct0 & Hct1 & Hct2 & Himport & Hs1 & Hs2 & Hhdr &
      Hca0 & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sb := (shadow_b ^+ (b - heap_b))%a).
    assert (Htr1 : heap_to_shadow (b ^+ -1)%a = Some (sb ^+ -1)%a).
    { rewrite allocator_heap_to_shadow; last solve_addr. f_equal. subst sb. solve_addr. }
    assert (Htr2 : heap_to_shadow b = Some sb).
    { rewrite allocator_heap_to_shadow; last solve_addr. done. }
    assert (Henc : ∀ s s', s ≠ s' → encodeAllocStatus s ≠ encodeAllocStatus s').
    { intros s s' Hne Heq. apply Hne.
      rewrite -(decode_encode_alloc_status_inv s) -(decode_encode_alloc_status_inv s') Heq //. }

    (* Block 3: fetch the shadow capability *)
    focus_block 3 "Hcode_main" of allocator_free_blocks at pc_a as a_fetch Ha_fetch
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_fetch_spec with "[- $HPC $Hctp $Hct3 $Hca2 $Hcode $Himport]");
      [done|solve_addr| |done|apply allocator_shadow_import_not_heap|done|done|done|].
    { apply withinBounds_true_iff. rewrite /allocator_shadow_import_off. solve_addr. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hcode)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: the local check of the header *)
    focus_block 4 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    replace (b - heap_b - 1)%Z with ((sb ^+ -1)%a - shadow_b)%Z by (subst sb; solve_addr).
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    { transitivity (Some (sb ^+ -1)%a); subst sb; solve_addr. }
    unfold lword_of_word.
    (* Load ct3 ctp: the shadow entry of the word below the base. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hs1]");
      try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    { apply heap_shadow_inverse. exact Htr1. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hs1)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowQuarantined). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowQuarantined)
      with (encodeAllocStatus ShadowQuarantined).
    destruct (decide (s1 = ShadowQuarantined)) as [->|Hs1q]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s1 - encodeAllocStatus ShadowQuarantined) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs1q). lia. }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_block_offset 11)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iApply "Hφ". iFrame. iRight. iSplit; first (iPureIntro; intros (? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. iSplitL "Hca2"; [by iExists _|].
      by iExists _. }
    rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Lea ctp 1. *)
    iInstr "Hcode".
    { transitivity (Some (sb ^+ 0)%a); subst sb; solve_addr. }
    replace ((sb ^+ -1) ^+ 1)%a with sb by (subst sb; solve_addr).
    (* Load ct3 ctp: the shadow entry of the base. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hs2]");
      try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    { apply heap_shadow_inverse. exact Htr2. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hs2)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowLive). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowLive)
      with (encodeAllocStatus ShadowLive).
    destruct (decide (s2 = ShadowLive)) as [->|Hs2l]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s2 - encodeAllocStatus ShadowLive) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs2l). lia. }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_block_offset 11)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iApply "Hφ". iFrame. iRight. iSplit; first (iPureIntro; intros (_ & ? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _. }
    rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    specialize (Hheader eq_refl eq_refl).
    iDestruct "Hhdr" as "[Hhdr Hown]".
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    unfold allocator_header_words in *.
    change (Z.opp 3) with (-3)%Z in *.
    replace (b - next - 3)%Z with ((b ^+ -3)%a - next)%Z by solve_addr.
    (* Lea ct4 ct3. *)
    iInstr "Hcode".
    { transitivity (Some (b ^+ -3)%a); solve_addr. }
    (* Load ca2 ct4: the recorded end. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_notinstr _ ca2 ct4 with "[$HPC $Hi $Hca2 $Hct4 $Hhdr]");
      try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e (b ^+ -3)%a);
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { reflexivity. }
    { split; first done. apply withinBounds_true_iff. solve_addr. }
    iIntros "!> (HPC & Hca2 & Hi & Hct4 & Hhdr)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hca2".
    (* Sub ct3 ca2 ct2. *)
    iInstr "Hcode".
    destruct (decide (eh = e)) as [->|Hne].
    - rewrite Z.sub_diag.
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      (* Load ct3 ct4 1: the recorded owner. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_success_notinstr_imm _ ct3 ct4 with "[$HPC $Hi $Hct3 $Hct4 $Hown]");
        try solve_pure.
      { eapply (disjoint_from_shadow_not_in heap_b heap_e ((b ^+ -3) ^+ 1)%a);
          first exact heap_shadow_disjoint.
        apply withinBounds_true_iff. solve_addr. }
      { reflexivity. }
      { split; first done. apply withinBounds_true_iff. solve_addr. }
      { solve_addr. }
      iIntros "!> (HPC & Hct3 & Hi & Hct4 & Hown)".
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      iEval (rewrite /lload_word /lift_word /=) in "Hct3".
      (* Sub ct3 ct3 ca0. *)
      iInstr "Hcode".
      destruct (decide (oh = o)) as [->|Hneo].
      + rewrite Z.sub_diag.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        (* Sub ca2 ct2 ct1. *)
        iInstr "Hcode".
        subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
        change_pc_to (pc_a ^+ allocator_free_block_offset 5)%a.
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame. iLeft. iFrame. done.
      + assert (Hneq : WInt (oh - o) ≠ WInt 0) by (intros [=]; apply Hneo; lia).
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        { transitivity (Some (pc_a ^+ allocator_free_block_offset 11)%a);
            offsets_compute; solve_addr. }
        subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame. iRight. iSplit; first (iPureIntro; intros (_ & _ & _ & ?); done).
        iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
    - assert (Hneq : WInt (eh - e) ≠ WInt 0) by (intros [=]; apply Hne; solve_addr).
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_block_offset 11)%a);
          offsets_compute; solve_addr. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
      iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
      iFrame. iRight. iSplit; first (iPureIntro; intros (_ & _ & ? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
  Qed.

End AllocatorFreeHeaderBlocks3.
