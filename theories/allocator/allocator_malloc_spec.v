From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_resource_spec.

(** Address of an assembled block relative to the entry point. *)
Definition allocator_malloc_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_malloc)))%a.

Section AllocatorMallocBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_malloc_size_check_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 0 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_positive_size wreq ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ct3 ↦ᵣ wtmp
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (ca0 ↦ᵣ wreq
         ∗ ct3 ↦ᵣ -
         ∗ codefrag pc_a code
         ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 1)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hcont Hpc Hdisjoint (n & -> & Hpositive); subst code.
    iIntros "(>HPC & >Hca0 & >Hct3 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_int n 0) /wt_int Z.sub_diag.
    (* Jnz .malloc_invalid ct3 falls through for an integer. *)
    iInstr "Hcode".
    (* Lt ct3 0 ca0. *)
    iInstr "Hcode".
    replace (0 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_size_ok ct3. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_size_check_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 0 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    ¬ allocator_positive_size wreq ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ct3 ↦ᵣ wtmp
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (ca0 ↦ᵣ wreq
         ∗ ct3 ↦ᵣ -
         ∗ codefrag pc_a code
         ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 7)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hcont Hpc Hdisjoint Hinvalid; subst code.
    iIntros "(>HPC & >Hca0 & >Hct3 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    destruct (is_z wreq) eqn:Hreq_z.
    - destruct wreq; cbn in *; try done.
      rewrite (encodeWordType_correct_int z 0) /wt_int Z.sub_diag.
      (* Jnz .malloc_invalid ct3 falls through for an integer. *)
      iInstr "Hcode".
      (* Lt ct3 0 ca0. *)
      iInstr "Hcode".
      destruct (decide (0 < z)%Z) as [Hzpos|Hznonpos].
      { exfalso. apply Hinvalid. exists z. split; [reflexivity|exact Hzpos]. }
      replace (0 <? z)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      (* Jnz .malloc_size_ok ct3 falls through. *)
      iInstr "Hcode".
      (* Jmp .malloc_invalid leaves this block's code fragment. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame.
    - assert (Hnonzero : WInt (encodeWordType wreq - encodeWordType (WInt 0)) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq (WInt 0)) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType (WInt 0)) by lia.
        destruct wreq; cbn in Hreq_z, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hencode); contradiction. }
      (* Jnz .malloc_invalid ct3 leaves this block's code fragment. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_reject_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 7 in
    let code := allocator_malloc_instrs_n 7 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ca1 ↦ᵣ wstatus
    ∗ ▷ codefrag start code
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 9)
         ∗ ca0 ↦ᵣ WInt 0
         ∗ ca1 ↦ᵣ WInt ALLOC_INVALID
         ∗ codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(>HPC & >Hca0 & >Hca1 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 44)%a =
      ((allocator_malloc_block_addr pc_a 7) ^+ 1)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_INVALID. *)
    iInstr "Hcode".
    iEval (simpl) in "Hca1".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    assert (Hca1val :
      (if decide (ca1 = cnull) then 0%Z else (-1)%Z) = ALLOC_INVALID).
    { unfold ALLOC_INVALID.
      destruct (decide (ca1 = cnull)); [discriminate|done]. }
    iEval (rewrite Hca1val) in "Hca1".
    assert (Hret : (allocator_malloc_block_addr pc_a 7 ^+ 5)%a =
      allocator_malloc_block_addr pc_a 9).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_oom_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 8 in
    let code := allocator_malloc_instrs_n 8 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ca1 ↦ᵣ wstatus
    ∗ ▷ codefrag start code
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 9)
         ∗ ca0 ↦ᵣ WInt 0
         ∗ ca1 ↦ᵣ WInt ALLOC_NO_MEMORY
         ∗ codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(>HPC & >Hca0 & >Hca1 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 47)%a =
      ((allocator_malloc_block_addr pc_a 8) ^+ 1)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_NO_MEMORY. *)
    iInstr "Hcode".
    assert (Hca1val :
      (if decide (ca1 = cnull) then 0%Z else (-2)%Z) = ALLOC_NO_MEMORY).
    { unfold ALLOC_NO_MEMORY.
      destruct (decide (ca1 = cnull)); [discriminate|done]. }
    iEval (rewrite Hca1val) in "Hca1".
    assert (Hret : (allocator_malloc_block_addr pc_a 8 ^+ 2)%a =
      allocator_malloc_block_addr pc_a 9).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_prepare_success_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (n : Z)
    (w0 w1 w2 w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (0 < n)%Z ->
    (n <= heap_e - next)%Z ->

    allocator_ctx
    ∗ allocator_service_data next
    ∗ ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b
    ∗ ▷ ca0 ↦ᵣ WInt n
    ∗ ▷ ct0 ↦ᵣ w0
    ∗ ▷ ct1 ↦ᵣ w1
    ∗ ▷ ct2 ↦ᵣ w2
    ∗ ▷ ct3 ↦ᵣ w3
    ∗ ▷ ct4 ↦ᵣ w4
    ∗ ▷ ca2 ↦ᵣ wa2
    ∗ ▷ codefrag start code
    ∗ ▷ (allocator_service_data next
         ∗ cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b
         ∗ ca0 ↦ᵣ WInt n
         ∗ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
         ∗ ct1 ↦ᵣ WInt next
         ∗ codefrag start code
         ∗ (∃ finish : Addr,
             ⌜(next + n)%a = Some finish
               ∧ (next < finish /\ finish <= heap_e)%a⌝
             ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
                 (allocator_malloc_block_addr pc_a 2)
             ∗ ct2 ↦ᵣ WInt finish
             ∗ ct3 ↦ᵣ WInt 0
             ∗ ct4 ↦ᵣ WCap true RW Global next finish next
             ∗ ca2 ↦ᵣ WCap true RW Global next finish next)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout HE Hcont Hpc Hdisjoint Hpositive Hroom; subst start code.
    iIntros "(#Hctx & Hdata & >HPC & >Hcgp & >Hca0 & >Hct0 & >Hct1 & >Hct2 & >Hct3 & >Hct4 & >Hca2 & >Hcode & Hφ)".
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 1 = (pc_a ^+ 6)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.

    (* Load ct0 cgp: the reserved root token proves the stored heap
       capability's shadow bit is clear, so the load preserves its tag. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup heap_b with "Hbody") as (s) "[Hentry Hput]".
    { apply elem_of_heap_addresses. apply withinBounds_true_iff.
      pose proof heap_valid. solve_addr. }
    iDestruct (allocator_entry_free_token with "Hentry Hroot") as %->.
    iDestruct "Hentry" as "[Hs Hres]".
    iApply (wp_load_success_heap with "[$HPC $Hi $Hct0 $Hcgp $Hslot $Hs]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff.
        pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
        cbn in Hsize. solve_addr. } }
    { unfold is_heap_address. apply withinBounds_true_iff.
      pose proof heap_valid. solve_addr. }
    { split; first done. apply withinBounds_true_iff.
      pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
      cbn in Hsize. solve_addr. }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hslot & Hs)".
    iMod ("Hclose" with "[Hs Hres Hput]").
    { iNext. iApply ("Hput" $! Free). iFrame. }
    iModIntro. wp_pure.
    iSpecialize ("Hcode" with "Hi").
    codefrag_facts "Hcode".
    assert (Hstep : (pc_a ^+ 7)%a = ((pc_a ^+ 6)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    iEval (simpl) in "Hct0".

    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1 computes remaining capacity. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca0 tests whether the request exceeds capacity. *)
    iInstr "Hcode".
    replace (heap_e - next <? n)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    (* Jnz .malloc_no_memory ct3 falls through. *)
    iInstr "Hcode".
    (* Add ct2 ct1 ca0 computes the end. *)
    iInstr "Hcode".
    (* Mov ct4 ct0 copies the heap capability. *)
    iInstr "Hcode".
    (* Subseg ct4 ct1 ct2 narrows it to the requested interval. *)
    iInstr "Hcode".
    (* Mov ca2 ct4 copies the bounded capability for zeroing. *)
    iInstr "Hcode".
    assert (Hfinish : (next + n)%a = Some (next ^+ n)%a) by solve_addr.
    assert (Hnew : (next < (next ^+ n)%a /\ (next ^+ n)%a <= heap_e)%a) by solve_addr.
    iApply "Hφ".
    iSplitL "Hslot Hroot Hfree".
    { iFrame. done. }
    iFrame "Hcgp Hca0 Hct0 Hct1 Hcode".
    iExists (next ^+ n)%a.
    iSplit; first (iPureIntro; split; [exact Hfinish|exact Hnew]).
    replace (allocator_malloc_block_addr pc_a 2) with (pc_a ^+ 16)%a by reflexivity.
    assert (Hnextpc : ((pc_a ^+ 6)%a ^+ 10)%a = (pc_a ^+ 16)%a) by solve_addr.
    iEval (rewrite Hnextpc) in "HPC".
    replace (next ^+ (0 + n))%a with (next ^+ n)%a by solve_addr.
    iFrame.
    assert (Hword : WInt (next + n) = WInt (next ^+ n)%a) by (f_equal; solve_addr).
    iEval (rewrite Hword) in "Hct2". iFrame.
  Qed.

  Lemma allocator_malloc_prepare_oom_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (n : Z)
    (w0 w1 w2 w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (0 < n)%Z ->
    (heap_e - next < n)%Z ->

    allocator_ctx
    ∗ allocator_service_data next
    ∗ ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b
    ∗ ▷ ca0 ↦ᵣ WInt n
    ∗ ▷ ct0 ↦ᵣ w0
    ∗ ▷ ct1 ↦ᵣ w1
    ∗ ▷ ct2 ↦ᵣ w2
    ∗ ▷ ct3 ↦ᵣ w3
    ∗ ▷ ct4 ↦ᵣ w4
    ∗ ▷ ca2 ↦ᵣ wa2
    ∗ ▷ codefrag start code
    ∗ ▷ (allocator_service_data next
         ∗ cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b
         ∗ ca0 ↦ᵣ WInt n
         ∗ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
         ∗ ct1 ↦ᵣ WInt next
         ∗ codefrag start code
         ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 8)
         ∗ ct2 ↦ᵣ WInt heap_e
         ∗ ct3 ↦ᵣ WInt 1
         ∗ ct4 ↦ᵣ w4
         ∗ ca2 ↦ᵣ wa2
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout HE Hcont Hpc Hdisjoint Hpositive Hoom; subst start code.
    iIntros "(#Hctx & Hdata & >HPC & >Hcgp & >Hca0 & >Hct0 & >Hct1 & >Hct2 & >Hct3 & >Hct4 & >Hca2 & >Hcode & Hφ)".
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 1 = (pc_a ^+ 6)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.

    (* Load ct0 cgp: the reserved root token proves the stored heap
       capability's shadow bit is clear, so the load preserves its tag. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup heap_b with "Hbody") as (s) "[Hentry Hput]".
    { apply elem_of_heap_addresses. apply withinBounds_true_iff.
      pose proof heap_valid. solve_addr. }
    iDestruct (allocator_entry_free_token with "Hentry Hroot") as %->.
    iDestruct "Hentry" as "[Hs Hres]".
    iApply (wp_load_success_heap with "[$HPC $Hi $Hct0 $Hcgp $Hslot $Hs]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff.
        pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
        cbn in Hsize. solve_addr. } }
    { unfold is_heap_address. apply withinBounds_true_iff.
      pose proof heap_valid. solve_addr. }
    { split; first done. apply withinBounds_true_iff.
      pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
      cbn in Hsize. solve_addr. }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hslot & Hs)".
    iMod ("Hclose" with "[Hs Hres Hput]").
    { iNext. iApply ("Hput" $! Free). iFrame. }
    iModIntro. wp_pure.
    iSpecialize ("Hcode" with "Hi").
    codefrag_facts "Hcode".
    assert (Hstep : (pc_a ^+ 7)%a = ((pc_a ^+ 6)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    iEval (simpl) in "Hct0".

    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1 computes remaining capacity. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca0 tests whether the request exceeds capacity. *)
    iInstr "Hcode".
    replace (heap_e - next <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz to the out-of-memory block. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct3]"); try solve_pure.
    { instantiate (1 := (pc_a ^+ 46)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hct3)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply "Hφ". iFrame.
    done.
  Qed.

  Lemma allocator_malloc_publish_spec
    (E : coPset)
    (pc_b pc_e pc_a next finish : Addr) (n : Z) (wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 6 in
    let code := allocator_malloc_instrs_n 6 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (next + n)%a = Some finish ->
    (heap_b < next /\ next < finish /\ finish <= heap_e)%a ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b
    ∗ ▷ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
    ∗ ▷ ct4 ↦ᵣ WCap true RW Global next finish next
    ∗ ▷ ca0 ↦ᵣ WInt n
    ∗ ▷ ca1 ↦ᵣ wstatus
    ∗ ▷ allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next
    ∗ ▷ codefrag start code
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 9)
         ∗ cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b
         ∗ ct0 ↦ᵣ WCap true RW Global heap_b heap_e finish
         ∗ ct4 ↦ᵣ WCap true RW Global next finish next
         ∗ ca0 ↦ᵣ WCap true RW Global next finish next
         ∗ ca1 ↦ᵣ WInt ALLOC_OK
         ∗ allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e finish
         ∗ codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hfinish Hrange; subst start code.
    iIntros "(>HPC & >Hcgp & >Hct0 & >Hct4 & >Hca0 & >Hca1 & >Hslot & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Lea ct0 ca0 computes the new bump cursor. *)
    iInstr "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 6 = (pc_a ^+ 38)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    rewrite Hstart in H.
    assert (Hstep : (pc_a ^+ 39)%a = ((pc_a ^+ 38)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    (* Store cgp ct0 publishes the new cursor. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ _ _
      (WCap true RW Global heap_b heap_e next)
      with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff.
        pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
        cbn in Hsize. solve_addr. } }
    { rewrite <- Hstep. constructor; [solve_addr|done]. }
    { apply withinBounds_true_iff.
      pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
      cbn in Hsize. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Mov ca0 ct4. *)
    iInstr "Hcode".
    (* Mov ca1 ALLOC_OK. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
    replace (allocator_malloc_block_addr pc_a 9) with (pc_a ^+ 48)%a by reflexivity.
    assert (Hret : ((pc_a ^+ 38)%a ^+ 10)%a = (pc_a ^+ 48)%a) by solve_addr.
    iEval (rewrite Hret) in "HPC". iFrame.
  Qed.
End AllocatorMallocBlocks.

Section AllocatorMallocProof.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {allocatorg : allocatorG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}
    {layout_wf : allocatorLayoutWf}
  .

  (** A noninteger or nonpositive size is rejected before the heap is read.
      Other registers and resources can be framed. *)
  Lemma allocator_malloc_invalid_correct
    (E : coPset) (wreq wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ⊢ (⌜↑Nallocator ⊆ E⌝ -∗
       ⌜↑Nallocator_service ⊆ E⌝ -∗
       ⌜¬ allocator_positive_size wreq⌝ -∗

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ wreq ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ WInt ALLOC_INVALID ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    iIntros "%HEheap %HEservice %Hinvalid".
    iIntros "(#Hctx & #Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    (* Check the requested size. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Hcheck_code" "Hmalloc_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app in Hsize_code.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    assert (Hstart : allocator_code_b = allocator_malloc_pcc_addr).
    { pose proof allocator_size_imports as Hsize.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    iDestruct "Hct3" as (w3) "Hct3".
    rewrite Hstart in H0.
    iEval (rewrite Hstart) in "Hcheck_code".
    iApply (allocator_malloc_size_check_invalid_spec with
      "[- $HPC $Hca0 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca0 & Hct3 & Hcheck_code & HPC)".
    iEval (rewrite -Hstart) in "Hcheck_code".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    (* The size check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit7 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 7 ++
       concat (encodeInstrsW <$> drop 8 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit7) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_reject Ha_reject
      "Hreject_code" "Hmalloc_cont".
    assert (Haddr7 : a_reject =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 7).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_reject.
    iDestruct "Hca1" as (wca1) "Hca1".
    iApply (allocator_malloc_reject_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hreject_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hreject_code)".
    iDestruct ("Hmalloc_cont" with "Hreject_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit7) in "Hmalloc_code".
    (* Return to the caller and restore the service invariant. *)
    assert (Hsplit9 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
      allocator_malloc_instrs_n 9) by reflexivity.
    iEval (rewrite Hsplit9) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
      "Hret_code" "Hmalloc_cont".
    assert (Haddr9 : a_ret =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_ret.
    assert (Hret_eq : allocator_malloc_instrs_n 9 =
      encodeInstrsW [Jalr cnull cra]) by reflexivity.
    iEval (rewrite Hret_eq) in "Hret_code".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hcnull $Hret_code]"); eauto.
    { unfold allocator_malloc_block_addr in *. cbn. solve_addr. }
    iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code)".
    iEval (rewrite -Hret_eq) in "Hret_code".
    iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit9) in "Hmalloc_code".
    iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next. iFrame. }
    iApply "Hpost". iFrame "∗".
  Qed.

  (** A positive integer size either exceeds the remaining suffix or obtains
      a fresh, exactly bounded, zeroed range. The bump cursor stays hidden in
      the service invariant. *)
  Lemma allocator_malloc_valid_correct
    (E : coPset) (n : Z) (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ⊢ (⌜↑Nallocator ⊆ E⌝ -∗
       ⌜↑Nallocator_service ⊆ E⌝ -∗
       ⌜(0 < n)%Z⌝ -∗

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt n ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0 ∗

          ((ca0 ↦ᵣ WInt 0 ∗
            ca1 ↦ᵣ WInt ALLOC_NO_MEMORY)
           ∨ (∃ (b e : Addr),
                ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧
                  (e - b = n)%Z⌝ ∗
                ca0 ↦ᵣ WCap true RW Global b e b ∗
                ca1 ↦ᵣ WInt ALLOC_OK ∗
                allocator_zeroed b e))

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    iIntros "%HEheap %HEservice %Hpositive".
    iIntros "(#Hctx & #Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    (* Check the requested size. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Hcheck_code" "Hmalloc_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr
      (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      pose proof allocator_size_imports as Himports_size.
      rewrite /allocator_code length_app in Hsize_code.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    assert (Hstart : allocator_code_b = allocator_malloc_pcc_addr).
    { pose proof allocator_size_imports as Hsize.
      unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *.
      solve_addr. }
    iDestruct "Hct3" as (w3) "Hct3".
    rewrite Hstart in H0.
    iEval (rewrite Hstart) in "Hcheck_code".
    assert (Hsize : allocator_positive_size (WInt n)).
    { exists n. split; [reflexivity|exact Hpositive]. }
    iApply (allocator_malloc_size_check_valid_spec with
      "[- $HPC $Hca0 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca0 & Hct3 & Hcheck_code & HPC)".
    iEval (rewrite -Hstart) in "Hcheck_code".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    (* Prepare the allocation, branching on the remaining capacity. *)
    assert (Hsplit1 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 1 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 1 ++
       concat (encodeInstrsW <$> drop 2 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit1) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_prepare Ha_prepare
      "Hprepare_code" "Hmalloc_cont".
    assert (Haddr1 : a_prepare =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1).
    { rewrite -Hstart. unfold allocator_malloc_block_addr. solve_addr. }
    subst a_prepare.
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3b) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hca2" as (wa2) "Hca2".
    destruct (decide (n <= heap_e - next)%Z) as [Hroom|Hoom].
    - iApply (allocator_malloc_prepare_success_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hprepare_code]"); eauto.
      { rewrite -Hstart. exact H. }
      iNext. iIntros
        "(Hdata & Hcgp & Hca0 & Hct0 & Hct1 & Hprepare_code & Hroom)".
      iDestruct "Hroom" as (finish)
        "(%Hfinish & HPC & Hct2 & Hct3 & Hct4 & Hca2)".
      destruct Hfinish as [Hfinish Hrange].
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit1) in "Hmalloc_code".
      iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
      (* Take ownership of the requested range from the free suffix. *)
      assert (Hsplit_range : (next <= finish /\ finish <= heap_e)%a)
        by solve_addr.
      iEval (rewrite /free_cells
        (finz_seq_between_split next finish heap_e Hsplit_range)
        big_sepL_app) in "Hfree".
      iDestruct "Hfree" as "[Hrange_free Hfree]".
      iPoseProof (allocator_take_range_correct E next finish) as "Htake".
      iSpecialize ("Htake" with
        "[] [] Hctx Hrange_free").
      { iPureIntro. exact HEheap. }
      { iPureIntro. solve_addr. }
      iMod "Htake" as "Hrange_mem".
      (* Zero the newly allocated cells. *)
      assert (Hsplit2 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 2 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 2 ++
         concat (encodeInstrsW <$> drop 3 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit2) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_zero Ha_zero
        "Hzero_code" "Hmalloc_cont".
      assert (Haddr2 : a_zero =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 2).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_zero. cbn [take concat fmap] in *. solve_addr. }
      subst a_zero.
      assert (Hzero_eq : allocator_malloc_instrs_n 2 =
        allocator_zero_instrs ca2 ct2 ct3) by reflexivity.
      iEval (rewrite Hzero_eq) in "Hzero_code".
      iApply (allocator_zero_spec ca2 ct2 ct3 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 2)
        RW Global next finish (WInt 0)
        with "[- $HPC $Hca2 $Hct2 $Hct3 $Hzero_code $Hrange_mem]").
      { reflexivity. }
      { unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { exact Hdisjoint. }
      { reflexivity. }
      { solve_addr. }
      { vm_compute;
        repeat (constructor;
          [rewrite !elem_of_cons elem_of_nil; intuition congruence|]);
        constructor.
        { apply not_elem_of_nil. }
        { constructor. } }
      iNext. iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hzero_code & Hzeros)".
      iEval (rewrite -Hzero_eq) in "Hzero_code".
      iDestruct ("Hmalloc_cont" with "Hzero_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit2) in "Hmalloc_code".
      (* Fetch the shadow capability and translate the allocated bounds. *)
      assert (Hsplit3 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 3 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 3 ++
         concat (encodeInstrsW <$> drop 4 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit3) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_fetch Ha_fetch
        "Hfetch_code" "Hmalloc_cont".
      assert (Haddr3 : a_fetch =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 3).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_fetch. cbn [take concat fmap] in *. solve_addr. }
      subst a_fetch.
      assert (Hpc3 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 2 ^+
        length (allocator_zero_instrs ca2 ct2 ct3))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 3).
      { unfold allocator_malloc_block_addr. clear -Hpc. solve_addr. }
      iEval (rewrite Hpc3) in "HPC".
      pose proof allocator_size_imports as Himports_size.
      iDestruct (region_pointsto_single with "Himports") as (v)
        "[Himport %Hentry]"; first exact Himports_size.
      cbn in Hentry. inversion Hentry; subst v.
      assert (Hfetch_eq : allocator_malloc_instrs_n 3 =
        fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
        by reflexivity.
      iEval (rewrite Hfetch_eq) in "Hfetch_code".
      iDestruct "Hctp" as (wctp) "Hctp".
      assert (Himpaddr : (allocator_pcc_b ^+ allocator_shadow_import_off)%a =
        allocator_pcc_b)
        by (unfold allocator_shadow_import_off; solve_addr).
      iEval (rewrite -Himpaddr) in "Himport".
      iApply (allocator_fetch_spec with
        "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Himport]").
      { reflexivity. }
      { rewrite -Hfetch_eq;
        unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { apply withinBounds_true_iff; solve_addr. }
      { exact Hdisjoint. }
      { cbn [is_heap_cap]; unfold is_heap_address;
        apply not_true_is_false; intro Hheap;
        apply withinBounds_true_iff in Hheap;
        pose proof heap_shadow_disjoint as Hd;
        rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
        apply (Hd shadow_b); apply elem_of_finz_seq_between;
        try exact Hheap;
        pose proof shadow_valid; solve_addr. }
      { discriminate. }
      { discriminate. }
      { discriminate. }
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hfetch_code & Himport)".
      iEval (cbn) in "Hctp".
      iEval (rewrite Himpaddr) in "Himport".
      iAssert ([[allocator_pcc_b,allocator_code_b]] ↦ₐ [[allocator_imports]])%I
        with "[Himport]" as "Himports".
      { rewrite /allocator_imports /region_pointsto
          (finz_seq_between_singleton allocator_pcc_b allocator_code_b Himports_size) /=.
        iFrame. }
      iEval (rewrite -Hfetch_eq) in "Hfetch_code".
      iDestruct ("Hmalloc_cont" with "Hfetch_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit3) in "Hmalloc_code".
      assert (Hsplit4 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 4 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 4 ++
         concat (encodeInstrsW <$> drop 5 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit4) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_translate Ha_translate
        "Htranslate_code" "Hmalloc_cont".
      assert (Haddr4 : a_translate =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_translate. cbn [take concat fmap] in *. solve_addr. }
      subst a_translate.
      assert (Hpc4 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 3 ^+
        length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc4) in "HPC".
      iApply (allocator_translate_spec with
        "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code]");
        eauto; try solve_addr.
      iNext. iIntros
        "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hctp & Hca2 & Htranslate_code)".
      iDestruct ("Hmalloc_cont" with "Htranslate_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit4) in "Hmalloc_code".
      iAssert ([[next, finish]] ↦ₐ
        [[replicate (length (finz.seq_between next finish)) (WInt 0)]])%I
        with "[Hzeros]" as "Hzeros".
      { rewrite /region_pointsto big_sepL2_replicate_r; last reflexivity.
        iFrame. }
      (* Clear the shadow bits for the allocated range. *)
      assert (Hsplit5 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 5 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 5 ++
         concat (encodeInstrsW <$> drop 6 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit5) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_paint Ha_paint
        "Hpaint_code" "Hmalloc_cont".
      assert (Haddr5 : a_paint =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_paint. cbn [take concat fmap] in *. solve_addr. }
      subst a_paint.
      assert (Hpc5 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 4 ^+
        length (allocator_malloc_instrs_n 4))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc5) in "HPC".
      pose (sb := (shadow_b ^+ (next - heap_b))%a).
      pose (se := (shadow_b ^+ (finish - heap_b))%a).
      assert (Hshadow : (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a).
      { pose proof heap_shadow_same_size. unfold sb, se. solve_addr. }
      assert (Hlen_shadow : (se - sb = finish - next)%Z).
      { unfold sb, se. pose proof heap_shadow_same_size. solve_addr. }
      assert (Htranslation : ∀ x, (next <= x /\ x < finish)%a ->
        heap_to_shadow x = Some (sb ^+ (x - next))%a).
      { intros x Hx. rewrite allocator_translation_affine.
        unfold translate_region.
        assert (Hxheap : withinBounds heap_b heap_e x = true).
        { apply withinBounds_true_iff. solve_addr. }
        rewrite Hxheap. unfold sb.
        pose proof heap_shadow_same_size. solve_addr. }
      assert (Hpaint_eq : allocator_malloc_instrs_n 5 =
        allocator_paint_instrs ctp ca2 false) by reflexivity.
      iEval (rewrite Hpaint_eq) in "Hpaint_code".
      iApply (allocator_paint_spec false ctp ca2 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 5)
        next finish sb se
        (replicate (length (finz.seq_between next finish)) (WInt 0))
        with "[- $Hctx $HPC $Hctp $Hca2 $Hpaint_code $Hzeros]").
      { reflexivity. }
      { rewrite -Hpaint_eq;
        unfold allocator_malloc_block_addr; cbn; solve_addr. }
      { exact Hdisjoint. }
      { exact HEheap. }
      { solve_addr. }
      { exact Hshadow. }
      { exact Hlen_shadow. }
      { exact Htranslation. }
      { vm_compute;
        repeat (constructor;
          [rewrite !elem_of_cons elem_of_nil; intuition congruence|]);
        try apply not_elem_of_nil; constructor.
        { apply not_elem_of_nil. }
        { constructor. } }
      iNext. iIntros "(HPC & Hctp & Hca2 & Hpaint_code & Hzeros)".
      iEval (rewrite -Hpaint_eq) in "Hpaint_code".
      iDestruct ("Hmalloc_cont" with "Hpaint_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit5) in "Hmalloc_code".
      (* Publish the new bump cursor and set ALLOC_OK. *)
      assert (Hsplit6 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 6 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 6 ++
         concat (encodeInstrsW <$> drop 7 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit6) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_publish Ha_publish
        "Hpublish_code" "Hmalloc_cont".
      assert (Haddr6 : a_publish =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_publish. cbn [take concat fmap] in *. solve_addr. }
      subst a_publish.
      assert (Hoff5 : allocator_malloc_block_addr allocator_malloc_pcc_addr 5 =
        (allocator_malloc_pcc_addr ^+ 34)%a) by reflexivity.
      assert (Hoff6 : allocator_malloc_block_addr allocator_malloc_pcc_addr 6 =
        (allocator_malloc_pcc_addr ^+ 38)%a) by reflexivity.
      assert (Hlenpaint : length (allocator_paint_instrs ctp ca2 false) = 4)
        by reflexivity.
      assert (Hpc6 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 5 ^+
        length (allocator_paint_instrs ctp ca2 false))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { clear -Hoff5 Hoff6 Hlenpaint.
        rewrite Hoff5 Hoff6 Hlenpaint.
        rewrite incr_addr_opt_add_twice.
        { replace (34 + 4)%Z with 38%Z by lia; reflexivity. }
        all: lia. }
      iEval (rewrite Hpc6) in "HPC".
      iDestruct "Hca1" as (wca1) "Hca1".
      iApply (allocator_malloc_publish_spec with
        "[- $HPC $Hcgp $Hct0 $Hct4 $Hca0 $Hca1 $Hslot $Hpublish_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      { exact Hfinish. }
      { split; [exact (proj1 Hnext)|exact Hrange]. }
      iNext. iIntros
        "(HPC & Hcgp & Hct0 & Hct4 & Hca0 & Hca1 & Hslot & Hpublish_code)".
      iDestruct ("Hmalloc_cont" with "Hpublish_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit6) in "Hmalloc_code".
      (* Return the allocation and restore the service invariant. *)
      assert (Hsplit9 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 9) by reflexivity.
      iEval (rewrite Hsplit9) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr9 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 9 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { unfold allocator_malloc_block_addr in *; cbn; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit9) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[Himports Hcode Hslot Hroot Hfree Hna]") as "Hna".
      { iSplitR "Hna"; last iFrame.
        iNext. iSplitL "Himports Hcode"; first iFrame.
        iExists finish. iFrame. iPureIntro.
        clear -Hnext Hrange. solve_addr. }
      iApply "Hpost". iFrame "∗".
      iRight. iExists next, finish.
      iSplit.
      { iPureIntro. split.
        { split; [exact (proj1 Hnext)|exact Hrange]. }
        { clear -Hfinish. solve_addr. } }
      iFrame.
      rewrite /allocator_zeroed /region_pointsto big_sepL2_replicate_r;
        last reflexivity.
      iFrame.
    - assert (Hcapacity : (heap_e - next < n)%Z) by lia.
      iApply (allocator_malloc_prepare_oom_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hprepare_code]"); eauto.
      { rewrite -Hstart. exact H. }
      iNext. iIntros
        "(Hdata & Hcgp & Hca0 & Hct0 & Hct1 & Hprepare_code & HPC & Hct2 & Hct3 & Hct4 & Hca2)".
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit1) in "Hmalloc_code".
      (* Capacity is exhausted; return ALLOC_NO_MEMORY without changing the state. *)
      assert (Hsplit8 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 8 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 8 ++ allocator_malloc_instrs_n 9))
        by reflexivity.
      iEval (rewrite Hsplit8) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_oom Ha_oom
        "Hoom_code" "Hmalloc_cont".
      assert (Haddr8 : a_oom =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 8).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_oom. cbn [take concat fmap] in *. solve_addr. }
      subst a_oom.
      iDestruct "Hca1" as (wca1) "Hca1".
      iApply (allocator_malloc_oom_block_spec with
        "[- $HPC $Hca0 $Hca1 $Hoom_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hca0 & Hca1 & Hoom_code)".
      iDestruct ("Hmalloc_cont" with "Hoom_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit8) in "Hmalloc_code".
      assert (Hsplit9 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 9) by reflexivity.
      iEval (rewrite Hsplit9) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr9 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
      { rewrite -Hstart. unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 9 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { unfold allocator_malloc_block_addr in *; cbn; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit9) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
      { iSplitR "Hna"; last iFrame.
        iNext. iSplitL "Himports Hcode"; first iFrame.
        iExists next. iFrame. }
      iApply "Hpost". iFrame "∗". iLeft. iFrame.
  Qed.
End AllocatorMallocProof.
