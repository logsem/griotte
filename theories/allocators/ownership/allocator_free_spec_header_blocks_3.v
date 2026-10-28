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
    [ca0]. The header is read only when both shadow checks pass. On success,
    it fetches the revoker capability from the imports for the tail: the
    shadow cursor is at the base, the count of addresses to paint is in
    [ca2], the revoker capability in [ca3], and the group ends at block 5,
    the tail; otherwise at the rejection in the tail. *)

Section AllocatorFreeHeaderBlocks3.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  Lemma allocator_free_header_spec
    (E : coPset) (pc_b pc_e pc_a next b e eh : Addr) (o oh : Z) (s1 s2 : AllocStatus)
    (wctp w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (pc_b + allocator_free_pcc_off)%a = Some pc_a ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    (s1 = ShadowQuarantined -> s2 = ShadowLive ->
      (heap_b + allocator_header_words < b)%Z) ->
    PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 3) ∗
    ctp ↦ᵣ wctp ∗
    ca3 ↦ᵣ w3 ∗
    ca4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    (pc_b ^+ allocator_shadow_import_off) ↦ₐ□
      Cap RW Global shadow_b shadow_e shadow_b ∗
    (pc_b ^+ allocator_revoker_import_off) ↦ₐ□ allocator_revoker_cap ∗
    (b ^+ (-1)) ↦ₛ s1 ∗
    b ↦ₛ s2 ∗
    (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
     then (b ^+ (- allocator_header_words)) ↦ₐ WInt eh ∗
         ((b ^+ (- allocator_header_words)) ^+ 1) ↦ₐ WInt oh
    else emp) ∗
    ca0 ↦ᵣ WInt o ∗
    codefrag_pers pc_a allocator_free_code ∗
    ▷ ((pc_b ^+ allocator_shadow_import_off) ↦ₐ□
         Cap RW Global shadow_b shadow_e shadow_b ∗
       (pc_b ^+ allocator_revoker_import_off) ↦ₐ□ allocator_revoker_cap ∗
       (b ^+ (-1)) ↦ₛ s1 ∗
       b ↦ₛ s2 ∗
       (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
        then (b ^+ (- allocator_header_words)) ↦ₐ WInt eh ∗
             ((b ^+ (- allocator_header_words)) ^+ 1) ↦ₐ WInt oh
        else emp) ∗
       ca0 ↦ᵣ WInt o ∗
       ct0 ↦ᵣ Cap RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ca4 ↦ᵣ - ∗
       codefrag_pers pc_a allocator_free_code ∗
       ((⌜s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o⌝ ∗
         PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 5) ∗
         ca3 ↦ᵣ allocator_revoker_cap ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ctp ↦ᵣ Cap RW Global shadow_b shadow_e (shadow_b ^+ (b - heap_b)))
        ∨
        (⌜¬ (s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o)⌝ ∗
         PC ↦ₚ Cap RX Global pc_b pc_e (pc_a ^+ allocator_free_invalid_offset) ∗
         ca3 ↦ᵣ - ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ -))
       -∗ WP Exec @ E {{ φ }})
    ⊢ WP Exec @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hpcc Hbounds Hheader.
    iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca2 & Hct0 & Hct1 & Hct2 & #Himport & #Hrevoker_import &
      Hs1 & Hs2 & Hhdr &
      Hca0 & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sb := shadow_b ^+ (b - heap_b)).
    assert (Htr1 : heap_to_shadow (b ^+ -1) = Some (sb ^+ -1)).
    { rewrite allocator_heap_to_shadow; last solve_addr. f_equal. subst sb. solve_addr. }
    assert (Htr2 : heap_to_shadow b = Some sb).
    { rewrite allocator_heap_to_shadow; last solve_addr. done. }
    assert (Henc : ∀ s s', s ≠ s' → encodeAllocStatus s ≠ encodeAllocStatus s').
    { intros s s' Hne Heq. apply Hne.
      rewrite -(decode_encode_alloc_status_inv s) -(decode_encode_alloc_status_inv s') Heq //. }

    (* Block 3: fetch the shadow capability *)
    focus_block 3 "Hcode_main" of allocator_free_blocks at pc_a as a_fetch Ha_fetch
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    rewrite allocator_free_pcc_off_eq /allocator_malloc_pcc_off in Hpcc.
    let v := eval vm_compute in (length allocator_malloc_instrs) in
    change (length allocator_malloc_instrs) with v in Hpcc.
    pose proof allocator_shadow_import_not_heap.
    pose proof allocator_revoker_import_not_heap.
    (* Auipcc ctp ".Limport_shadow". *)
    iInstr "Hcode".
    { instantiate (1 := pc_b ^+ allocator_shadow_import_off).
      rewrite /allocator_shadow_import_off. offsets_compute; solve_addr. }
    (* CLoad ctp ctp 0. *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact Hpc_shadow.
      apply withinBounds_true_iff. offsets_compute; solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iEval (cbn [load_word]) in "Hctp".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 4: the local check of the header *)
    focus_block 4 "Hcode_main" of allocator_free_blocks at pc_a as a_check Ha_check
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* GetB ca3 ct0. *)
    iInstr "Hcode".
    (* Sub ca3 ct1 ca3. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 1. *)
    iInstr "Hcode".
    replace (b - heap_b - 1)%Z with ((sb ^+ -1) - shadow_b)%Z by (subst sb; solve_addr).
    (* Lea ctp ctp ca3. *)
    iInstr "Hcode".
    { transitivity (Some (sb ^+ -1)); subst sb; solve_addr. }
    unfold lword_of_word.
    (* CLoad ca3 ctp: the shadow entry of the word below the base. *)
    iInstrApply "Hcode" (wp_load_success_from_shadow _ ca3 ctp)
      with "[$HPC $Hct3 $Hctp $Hs1]"
      as "(HPC & Hct3 & Hctp & Hs1)".
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    { apply heap_shadow_inverse. exact Htr1. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    (* Sub ca3 ca3 (encodeAllocStatus ShadowQuarantined). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowQuarantined)
      with (encodeAllocStatus ShadowQuarantined).
    destruct (decide (s1 = ShadowQuarantined)) as [->|Hs1q]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s1 - encodeAllocStatus ShadowQuarantined) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs1q). lia. }
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iApply "Hφ". iFrame "∗ Hcode_main Himport Hrevoker_import". iRight. iSplit; first (iPureIntro; intros (? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. iSplitL "Hca2"; [by iExists _|].
      by iExists _. }
    rewrite Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    (* Lea ctp ctp 1. *)
    iInstr "Hcode".
    { transitivity (Some (sb ^+ 0)); subst sb; solve_addr. }
    replace ((sb ^+ -1) ^+ 1) with sb by (subst sb; solve_addr).
    (* CLoad ca3 ctp: the shadow entry of the base. *)
    iInstrApply "Hcode" (wp_load_success_from_shadow _ ca3 ctp)
      with "[$HPC $Hct3 $Hctp $Hs2]"
      as "(HPC & Hct3 & Hctp & Hs2)".
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    { apply heap_shadow_inverse. exact Htr2. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    (* Sub ca3 ca3 (encodeAllocStatus ShadowLive). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowLive)
      with (encodeAllocStatus ShadowLive).
    destruct (decide (s2 = ShadowLive)) as [->|Hs2l]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s2 - encodeAllocStatus ShadowLive) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs2l). lia. }
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iApply "Hφ". iFrame "∗ Hcode_main Himport Hrevoker_import". iRight. iSplit; first (iPureIntro; intros (_ & ? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _. }
    rewrite Z.sub_diag.
    (* Jne .free_invalid ca3 0. *)
    iInstr "Hcode".
    specialize (Hheader eq_refl eq_refl).
    iDestruct "Hhdr" as "[Hhdr Hown]".
    (* Mov ca4 ct0. *)
    iInstr "Hcode".
    (* GetA ca3 ct0. *)
    iInstr "Hcode".
    (* Sub ca3 ct1 ca3. *)
    iInstr "Hcode".
    (* Sub ca3 ca3 allocator_header_words. *)
    iInstr "Hcode".
    unfold allocator_header_words in *.
    change (Z.opp 3) with (-3)%Z in *.
    replace (b - next - 3)%Z with ((b ^+ -3) - next)%Z by solve_addr.
    (* Lea ca4 ca4 ca3. *)
    iInstr "Hcode".
    { transitivity (Some (b ^+ -3)); solve_addr. }
    iPoseProof deref_res_none as "-#Hdw".
    (* CLoad ca2 ca4: the recorded end. *)
    iInstrApply "Hcode" (wp_load_success_notinstr _ ca2 ca4)
      with "[$HPC $Hca2 $Hct4 $Hhdr $Hdw]"
      as "(HPC & Hca2 & Hct4 & Hhdr & _)".
    { eapply (disjoint_from_shadow_not_in heap_b heap_e (b ^+ -3));
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { reflexivity. }
    { split; first done. apply withinBounds_true_iff. solve_addr. }
    iEval (rewrite /lload_word /lift_word /=) in "Hca2".
    (* Sub ca3 ca2 ct2. *)
    iInstr "Hcode".
    destruct (decide (eh = e)) as [->|Hne].
    - rewrite Z.sub_diag.
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      iPoseProof deref_res_none as "-#Hdw".
      (* CLoad ca3 ca4 1: the recorded owner. *)
      iInstrApply "Hcode" (wp_load_success_notinstr_imm _ ca3 ca4)
        with "[$HPC $Hct3 $Hct4 $Hown $Hdw]"
        as "(HPC & Hct3 & Hct4 & Hown & _)".
      { eapply (disjoint_from_shadow_not_in heap_b heap_e ((b ^+ -3) ^+ 1));
          first exact heap_shadow_disjoint.
        apply withinBounds_true_iff. solve_addr. }
      { reflexivity. }
      { split; first done. apply withinBounds_true_iff. solve_addr. }
      { solve_addr. }
      iEval (rewrite /lload_word /lift_word /=) in "Hct3".
      (* Sub ca3 ca3 ca0. *)
      iInstr "Hcode".
      destruct (decide (oh = o)) as [->|Hneo].
      + rewrite Z.sub_diag.
        (* Jne .free_invalid ca3 0. *)
        iInstr "Hcode".
        (* Sub ca2 ct2 ct1. *)
        iInstr "Hcode".
        (* Auipcc ca3 ".Limport_revoker". *)
        iInstr "Hcode".
        { instantiate (1 := pc_b ^+ allocator_revoker_import_off).
          rewrite /allocator_revoker_import_off. offsets_compute; solve_addr. }
        (* CLoad ca3 ca3 0. *)
        iInstr "Hcode".
        { eapply disjoint_from_shadow_not_in; first exact Hpc_shadow.
          apply withinBounds_true_iff. rewrite /allocator_revoker_import_off.
          offsets_compute; solve_addr. }
        { apply withinBounds_true_iff. rewrite /allocator_revoker_import_off.
          offsets_compute; solve_addr. }
        iEval (rewrite /lload_word /lift_word /=) in "Hct3".
        iEval (cbn [load_word]) in "Hct3".
        unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
        change_pc_to (pc_a ^+ allocator_free_block_offset 5).
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame "∗ Hcode_main Himport Hrevoker_import". iLeft. iFrame "∗". done.
      + assert (Hneq : WInt (oh - o) ≠ WInt 0) by (intros [=]; apply Hneo; lia).
        (* Jne .free_invalid ca3 0. *)
        iInstr "Hcode".
        { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
            offsets_compute; solve_addr. }
        unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame "∗ Hcode_main Himport Hrevoker_import". iRight. iSplit; first (iPureIntro; intros (_ & _ & _ & ?); done).
        iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
    - assert (Hneq : WInt (eh - e) ≠ WInt 0) by (intros [=]; apply Hne; solve_addr).
      (* Jne .free_invalid ca3 0. *)
      iInstr "Hcode".
      { transitivity (Some (pc_a ^+ allocator_free_invalid_offset));
          offsets_compute; solve_addr. }
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
      iFrame "∗ Hcode_main Himport Hrevoker_import". iRight. iSplit; first (iPureIntro; intros (_ & _ & ? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
  Qed.

End AllocatorFreeHeaderBlocks3.
