From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_resource_spec allocator_header_spec.

(** Address of an assembled block relative to the entry point. *)

Definition allocator_malloc_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_malloc)))%a.

Section AllocatorMallocBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Local Lemma allocator_malloc_size_check_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_positive_size wreq ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca1 ↦ᵣ wreq ∗
    ct3 ↦ᵣ wtmp ∗
    codefrag start code ∗
    ▷ (ca1 ↦ᵣ wreq ∗
         ct3 ↦ᵣ - ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 2)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hdisjoint (n & -> & Hpositive); subst start code.
    iIntros "(HPC & Hca1 & Hct3 & Hcode & Hφ)".
    assert (Hnext : allocator_malloc_block_addr pc_a 2 =
      (allocator_malloc_block_addr pc_a 1 ^+ 6)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    assert (Hsub : SubBounds pc_b pc_e (allocator_malloc_block_addr pc_a 1)
      (allocator_malloc_block_addr pc_a 1 ^+ length (allocator_malloc_instrs_n 1))%a).
    { unfold allocator_malloc_block_addr. cbn. solve_addr. }
    rewrite Hnext.
    generalize dependent (allocator_malloc_block_addr pc_a 1); intros start Hnext Hsub.
    codefrag_facts "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_int n 0) /wt_int Z.sub_diag.
    (* Jnz .malloc_invalid ct3. *)
    iInstr "Hcode".
    (* Lt ct3 0 ca1. *)
    iInstr "Hcode".
    replace (0 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_size_ok ct3. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_malloc_size_check_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    ¬ allocator_positive_size wreq ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca1 ↦ᵣ wreq ∗
    ct3 ↦ᵣ wtmp ∗
    codefrag start code ∗
    ▷ (ca1 ↦ᵣ wreq ∗
         ct3 ↦ᵣ - ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 8)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hdisjoint Hinvalid; subst start code.
    iIntros "(HPC & Hca1 & Hct3 & Hcode & Hφ)".
    assert (Hnext : allocator_malloc_block_addr pc_a 8 =
      (allocator_malloc_block_addr pc_a 1 ^+ 50)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    assert (Hsub : SubBounds pc_b pc_e (allocator_malloc_block_addr pc_a 1)
      (allocator_malloc_block_addr pc_a 1 ^+ length (allocator_malloc_instrs_n 1))%a).
    { unfold allocator_malloc_block_addr. cbn. solve_addr. }
    assert (Htarget : (allocator_malloc_block_addr pc_a 1 + 50)%a =
      Some (allocator_malloc_block_addr pc_a 1 ^+ 50)%a).
    { unfold allocator_malloc_block_addr. cbn. solve_addr. }
    rewrite Hnext.
    generalize dependent (allocator_malloc_block_addr pc_a 1); intros start Hnext Hsub Htarget.
    codefrag_facts "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_int). *)
    iInstr "Hcode".
    destruct (is_z wreq) eqn:Hreq_z.
    - destruct wreq; cbn in *; try done.
      rewrite (encodeWordType_correct_int z 0) /wt_int Z.sub_diag.
      (* Jnz .malloc_invalid ct3. *)
      iInstr "Hcode".
      (* Lt ct3 0 ca1. *)
      iInstr "Hcode".
      destruct (decide (0 < z)%Z) as [Hzpos|Hznonpos].
      { exfalso. apply Hinvalid. exists z. split; [reflexivity|exact Hzpos]. }
      replace (0 <? z)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      (* Jnz .malloc_size_ok ct3. *)
      iInstr "Hcode".
      (* Jmp .malloc_invalid. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame.
    - assert (Hnonzero : WInt (encodeWordType wreq - encodeWordType (WInt 0)) ≠ WInt 0).
      { pose proof (encodeWordType_correct wreq (WInt 0)) as Hencode.
        intro Hzero. injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType (WInt 0)) by lia.
        destruct wreq; cbn in Hreq_z, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hencode); contradiction. }
      (* Jnz .malloc_invalid ct3. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_malloc_reject_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 8 in
    let code := allocator_malloc_instrs_n 8 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wstatus ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 10) ∗
         ca0 ↦ᵣ WInt ALLOC_INVALID ∗
         ca1 ↦ᵣ WInt 0 ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 ALLOC_INVALID. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 62)%a =
      ((allocator_malloc_block_addr pc_a 8) ^+ 1)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    assert (Hca0val :
      (if decide (ca0 = cnull) then 0%Z else (-1)%Z) = ALLOC_INVALID).
    { unfold ALLOC_INVALID.
      destruct (decide (ca0 = cnull)); [discriminate|done]. }
    iEval (rewrite Hca0val) in "Hca0".
    assert (Hret : (allocator_malloc_block_addr pc_a 8 ^+ 5)%a =
      allocator_malloc_block_addr pc_a 10).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_malloc_oom_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 9 in
    let code := allocator_malloc_instrs_n 9 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wstatus ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 10) ∗
         ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
         ca1 ↦ᵣ WInt 0 ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 ALLOC_NO_MEMORY. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 65)%a =
      ((allocator_malloc_block_addr pc_a 9) ^+ 1)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    assert (Hca0val :
      (if decide (ca0 = cnull) then 0%Z else (-2)%Z) = ALLOC_NO_MEMORY).
    { unfold ALLOC_NO_MEMORY.
      destruct (decide (ca0 = cnull)); [discriminate|done]. }
    iEval (rewrite Hca0val) in "Hca0".
    assert (Hret : (allocator_malloc_block_addr pc_a 9 ^+ 2)%a =
      allocator_malloc_block_addr pc_a 10).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_malloc_prepare_success_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (n o : Z)
    (w0 w1 w2 w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 2 in
    let code := allocator_malloc_instrs_n 2 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (0 < n)%Z ->
    (n + allocator_header_words <= heap_e - next)%Z ->

    allocator_ctx ∗
    allocator_service_data next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca1 ↦ᵣ WInt n ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ ((∃ b finish : Addr,
         ⌜(next + allocator_header_words)%a = Some b ∧
           (b + n)%a = Some finish ∧
           (b < finish /\ finish <= heap_e)%a⌝ ∗
         allocator_service_pending next b finish o ∗
         allocator_range_memory b finish ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca1 ↦ᵣ WInt n ∗
         ctp ↦ᵣ WInt o ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 3) ∗
         ct2 ↦ᵣ WInt finish ∗
         ct3 ↦ᵣ WInt 0 ∗
         ct4 ↦ᵣ WCap true RW Global b finish b ∗
         ca2 ↦ᵣ WCap true RW Global b finish b)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout HE Hcont Hpc Hdisjoint Hpositive Hroom; subst start code.
    iIntros "(#Hctx & Hdata & HPC & Hcgp & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iDestruct "Hdata" as (allocations)
      "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory & Howners)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 2 = (pc_a ^+ 17)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.

    (* Load ct0 cgp: the reserved root token proves the stored heap
       capability's shadow bit is clear, so the load preserves its tag. *)
    (* Load ct0 cgp. *)
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
    assert (Hstep : (pc_a ^+ 18)%a = ((pc_a ^+ 17)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    iEval (cbn [load_word]) in "Hct0".
    unfold allocator_header_words in Hroom.
    pose (b := (next ^+ 3)%a).
    pose (finish := (b ^+ n)%a).
    assert (Hbase : (next + 3)%a = Some b) by (unfold b; solve_addr).
    assert (Hfinish : (b + n)%a = Some finish) by (unfold b, finish; solve_addr).
    assert (Hrange : (next < b /\ b < finish /\ finish <= heap_e)%a)
      by (unfold b, finish; solve_addr).
    (* Read the bump bounds and reserve space for the header. *)

    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca1. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with false
      by (symmetry; apply Z.ltb_ge; lia).
    (* Jnz .malloc_no_memory ct3. *)
    iInstr "Hcode".
    (* Compute the payload bounds and restrict its capability. *)
    (* Add ct1 ct1 allocator_header_words. *)
    iInstr "Hcode".
    assert (Hbword : WInt (next + 3) = WInt b) by (f_equal; solve_addr).
    iEval (rewrite Hbword) in "Hct1".
    (* Add ct2 ct1 ca1. *)
    iInstr "Hcode".
    assert (Heword : WInt (b + n) = WInt finish) by (f_equal; solve_addr).
    iEval (rewrite Heword) in "Hct2".
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    (* Lea ct4 allocator_header_words. *)
    iInstr "Hcode".
    (* Subseg ct4 ct1 ct2. *)
    iInstr "Hcode".
    (* Take the header and payload from the free suffix before writing. *)
    assert (Hsplit_range : (next <= finish /\ finish <= heap_e)%a) by solve_addr.
    iEval (rewrite /free_addrs
      (finz_seq_between_split next finish heap_e Hsplit_range)
      big_sepL_app) in "Hfree".
    iDestruct "Hfree" as "[Hchunk Hfree]".
    assert (Htake : (heap_b <= next /\ next <= finish /\ finish <= heap_e)%a)
      by solve_addr.
    iMod (allocator_take_range_correct E next finish HE Htake with "Hctx Hchunk")
      as "Hchunk".
    assert (Hnextfinish : (next < finish)%a) by solve_addr.
    assert (Hsecondfinish : (next ^+ 1 < finish)%a) by solve_addr.
    assert (Hthirdfinish : (next ^+ 2 < finish)%a) by solve_addr.
    assert (Hthirdaddr : ((next ^+ 1)%a ^+ 1)%a = (next ^+ 2)%a) by solve_addr.
    iEval (rewrite /allocator_range_memory
      (finz_seq_between_cons next finish Hnextfinish) big_sepL_cons
      (finz_seq_between_cons (next ^+ 1)%a finish Hsecondfinish) big_sepL_cons
      Hthirdaddr
      (finz_seq_between_cons (next ^+ 2)%a finish Hthirdfinish) big_sepL_cons)
      in "Hchunk".
    iDestruct "Hchunk" as "(Hend & Hreserved1 & Hreserved2 & Hpayload)".
    iDestruct "Hend" as (wend) "Hend".
    iDestruct "Hreserved1" as (wreserved1) "Hreserved1".
    iDestruct "Hreserved2" as (wreserved2) "Hreserved2".
    (* Write the end field. *)
    (* Store ct0 ct2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
     wp_instr.
    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ ct0 ct2 wend
      with "[$HPC $Hi $Hct2 $Hct0 $Hend]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e next);
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    iIntros "!> (HPC & Hi & Hct2 & Hct0 & Hend)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Record the owner at offset one. *)
    assert (Hsecond_shadow : is_shadow_address (next ^+ 1)%a = false).
    { eapply (disjoint_from_shadow_not_in heap_b heap_e);
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    assert (Hsecond_bounds : withinBounds heap_b heap_e (next ^+ 1)%a = true)
      by (apply withinBounds_true_iff; solve_addr).
    (* Store ct0 ctp 1. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
     wp_instr.
    iApply (wp_store_success_reg_imm _ _ _ _ _ _ _ _ ct0 ctp wreserved1
      _ _ _ _ _ (next ^+ 1)%a 1 (WInt o) with "[$HPC $Hi $Hctp $Hct0 $Hreserved1]");
      try solve_pure.
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hctp & Hct0 & Hreserved1)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Initialize the reserved field at offset two. *)
    assert (Hthird_shadow : is_shadow_address (next ^+ 2)%a = false).
    { eapply (disjoint_from_shadow_not_in heap_b heap_e);
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    assert (Hthird_bounds : withinBounds heap_b heap_e (next ^+ 2)%a = true)
      by (apply withinBounds_true_iff; solve_addr).
    (* Store ct0 0 2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
     wp_instr.
    iApply (wp_store_success_z_imm _ _ _ _ _ _ _ _ ct0 0 wreserved2
      _ _ _ _ _ (next ^+ 2)%a 2 with "[$HPC $Hi $Hct0 $Hreserved2]"); try solve_pure.
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hreserved2)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Copy the bounded payload capability for the zeroing loop. *)
    (* Mov ca2 ct4. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
     wp_instr.
    iApply (wp_move_success_reg with "[$HPC $Hi $Hca2 $Hct4]"); try solve_pure.
    iIntros "!> (HPC & Hi & Hca2 & Hct4)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply "Hφ". iExists b, finish.
    iSplit; first (iPureIntro; unfold allocator_header_words; naive_solver).
    iSplitL "Hslot Hroot Hfree Hheaders Hhistory Howners Hend Hreserved1 Hreserved2".
    { iExists allocations. iFrame "Hslot Hroot Hfree Hheaders Hhistory Howners".
      iSplit; first done. iSplit.
      { iPureIntro. unfold allocator_header_bounds, allocator_header_words. naive_solver. }
      rewrite /allocator_header. iFrame "Hend Hreserved1 Hreserved2". done. }
    iFrame "Hcgp Hca1 Hctp Hct0 Hct1 Hct2 Hct3 Hcode".
    replace (allocator_malloc_block_addr pc_a 3) with (pc_a ^+ 33)%a by reflexivity.
    assert (Hnextpc : ((pc_a ^+ 17)%a ^+ 16)%a = (pc_a ^+ 33)%a) by solve_addr.
    iEval (rewrite Hnextpc) in "HPC". iFrame "HPC".
    iFrame "Hct4 Hca2".
    assert (Hbmem : ((next ^+ 2)%a ^+ 1)%a = b) by solve_addr.
    iEval (rewrite Hbmem) in "Hpayload". iExact "Hpayload".
  Qed.

  Local Lemma allocator_malloc_prepare_oom_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (n : Z)
    (w0 w1 w2 w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 2 in
    let code := allocator_malloc_instrs_n 2 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (0 < n)%Z ->
    (heap_e - next - allocator_header_words < n)%Z ->

    allocator_ctx ∗
    allocator_service_data next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca1 ↦ᵣ WInt n ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (allocator_service_data next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca1 ↦ᵣ WInt n ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt next ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 9) ∗
         ct2 ↦ᵣ WInt heap_e ∗
         ct3 ↦ᵣ WInt 1 ∗
         ct4 ↦ᵣ w4 ∗
         ca2 ↦ᵣ wa2
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout HE Hcont Hpc Hdisjoint Hpositive Hoom; subst start code.
    iIntros "(#Hctx & Hdata & HPC & Hcgp & Hca1 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iDestruct "Hdata" as (allocations)
      "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory & Howners)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 2 = (pc_a ^+ 17)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.

    (* Load ct0 cgp: the reserved root token proves the stored heap
       capability's shadow bit is clear, so the load preserves its tag. *)
    (* Load ct0 cgp. *)
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
    assert (Hstep : (pc_a ^+ 18)%a = ((pc_a ^+ 17)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    iEval (cbn [load_word]) in "Hct0".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Reserve the two header addresses. *)
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    unfold allocator_header_words in Hoom.
    (* Lt ct3 ct3 ca1. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz to the out-of-memory block. *)
    (* Jnz .malloc_no_memory ct3. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct3]"); try solve_pure.
    { instantiate (1 := (pc_a ^+ 64)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hct3)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply "Hφ". iFrame. done.
  Qed.

  Local Lemma allocator_malloc_publish_spec
    (E : coPset)
    (pc_b pc_e pc_a next b finish : Addr) (n : Z) (wres : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 7 in
    let code := allocator_malloc_instrs_n 7 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (next + allocator_header_words)%a = Some b ->
    (b + n)%a = Some finish ->
    (heap_b < next /\ b < finish /\ finish <= heap_e)%a ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct4 ↦ᵣ WCap true RW Global b finish b ∗
    ca0 ↦ᵣ wres ∗
    ca1 ↦ᵣ WInt n ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 10) ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e finish ∗
         ct4 ↦ᵣ WCap true RW Global b finish b ∗
         ca0 ↦ᵣ WCap true RW Global b finish b ∗
         ca1 ↦ᵣ WInt 0 ∗
         allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e finish ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hbase Hfinish Hrange; subst start code.
    iIntros "(HPC & Hcgp & Hct0 & Hct4 & Hca0 & Hca1 & Hslot & Hcode & Hφ)".
    codefrag_facts "Hcode".
    unfold allocator_header_words in Hbase.
    assert (Hstart : allocator_malloc_block_addr pc_a 7 = (pc_a ^+ 55)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode HPC". rewrite Hstart in H.
    (* Skip the header, then advance over the payload. *)
    (* Lea ct0 allocator_header_words. *)
    iInstr "Hcode".
    assert (Hstep1 : (pc_a ^+ 56)%a = ((pc_a ^+ 55)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep1) in "HPC".
    (* Lea ct0 ca1. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 57)%a = ((pc_a ^+ 55)%a ^+ 2)%a) by solve_addr.
    (* Store cgp ct0 publishes the new cursor. *)
    (* Store cgp ct0. *)
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
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
    replace (allocator_malloc_block_addr pc_a 10) with (pc_a ^+ 66)%a by reflexivity.
    assert (Hret : ((pc_a ^+ 55)%a ^+ 11)%a = (pc_a ^+ 66)%a) by solve_addr.
    iEval (rewrite Hret) in "HPC". iFrame.
  Qed.

  Context {layout_wf : allocatorLayoutWf}.

  (** The imports: the shadow capability and the unsealing key. *)

  Local Lemma allocator_imports_split :
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[allocator_imports]] ⊣⊢
    allocator_pcc_b ↦ₐ WCap true RW Global shadow_b shadow_e shadow_b ∗
    (allocator_pcc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key.
  Proof.
    pose proof allocator_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    rewrite /allocator_imports /allocator_unsealing_key_import_off.
    rewrite (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 1)%a allocator_code_b);
      [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    rewrite big_sepL2_nil right_id. done.
  Qed.

  (** Facts about the entry point shared by all public specifications. *)

  Local Lemma allocator_malloc_entry_facts :
    SubBounds allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr
      (allocator_malloc_pcc_addr ^+ length allocator_malloc_instrs)%a ∧
    disjoint_from_shadow allocator_pcc_b allocator_pcc_e ∧
    allocator_code_b = allocator_malloc_pcc_addr ∧
    withinBounds allocator_pcc_b allocator_pcc_e
      (allocator_pcc_b ^+ allocator_unsealing_key_import_off)%a = true.
  Proof.
    pose proof allocator_size_code as Hsize_code.
    pose proof allocator_size_imports as Himports_size.
    rewrite allocator_imports_length in Himports_size.
    rewrite /allocator_code length_app in Hsize_code.
    split; [ | split; [ | split] ].
    - unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *. solve_addr.
    - pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver.
    - unfold allocator_malloc_pcc_addr, allocator_malloc_pcc_off in *. solve_addr.
    - apply withinBounds_true_iff.
      unfold allocator_unsealing_key_import_off.
      solve_addr.
  Qed.

  (** A noninteger or nonpositive size is rejected before the heap is read.
      Other registers and resources can be framed. *)

  Lemma allocator_malloc_invalid_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (id : Z) (S : gset Addr)
    (wreq wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    ¬ allocator_positive_size wreq ->

    ⊢ (

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_owner_id id S ∗
       a_owner ↦ₐ WInt id ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ wreq ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          allocator_owner_id id S ∗
          a_owner ↦ₐ WInt id ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt ALLOC_INVALID ∗
          ca1 ↦ᵣ WInt 0 ∗
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
    intros HEheap HEservice Hshadow_a Hbounds_a Hinvalid.
    iIntros "(#Hctx & #Hservice & Hna & Howner & Ha & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    destruct allocator_malloc_entry_facts as (Hpc & Hdisjoint & Hstart & Hkey_bounds).
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iDestruct (allocator_imports_split with "Himports") as "[Himport Hkey]".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite Hstart) in "Hmalloc_code".
    (* Load the owner identifier of the allocator capability. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Howner_code" "Hmalloc_cont".
    iEval (rewrite allocator_malloc_owner_code) in "Howner_code".
    iDestruct "Hctp" as (wtp) "Hctp".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iApply (allocator_owner_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Hkey $Ha $Howner_code]"); eauto.
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Ha & Howner_code)".
    iEval (rewrite -allocator_malloc_owner_code) in "Howner_code".
    iDestruct ("Hmalloc_cont" with "Howner_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    assert (Haddr1 : (allocator_malloc_pcc_addr ^+
      length (allocator_owner_instrs ctp ca0 ct3 ct4))%a =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1) by reflexivity.
    iEval (rewrite Haddr1) in "HPC".
    (* Check the requested size. *)
    assert (Hsplit1 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 1 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 1 ++
       concat (encodeInstrsW <$> drop 2 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit1) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_check Ha_check
      "Hcheck_code" "Hmalloc_cont".
    assert (Ha_check_eq : a_check =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1).
    { unfold allocator_malloc_block_addr. solve_addr. }
    subst a_check.
    iApply (allocator_malloc_size_check_invalid_spec with
      "[- $HPC $Hca1 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca1 & Hct3 & Hcheck_code & HPC)".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit1) in "Hmalloc_code".
    (* The size check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit8 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 8 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 8 ++
       concat (encodeInstrsW <$> drop 9 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit8) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_reject Ha_reject
      "Hreject_code" "Hmalloc_cont".
    assert (Haddr8 : a_reject =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 8).
    { unfold allocator_malloc_block_addr. solve_addr. }
    subst a_reject.
    iApply (allocator_malloc_reject_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hreject_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hreject_code)".
    iDestruct ("Hmalloc_cont" with "Hreject_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit8) in "Hmalloc_code".
    (* Return to the caller and restore the service invariant. *)
    assert (Hsplit10 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 10 assembled_allocator_malloc) ++
      allocator_malloc_instrs_n 10) by reflexivity.
    iEval (rewrite Hsplit10) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
      "Hret_code" "Hmalloc_cont".
    assert (Haddr10 : a_ret =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 10).
    { unfold allocator_malloc_block_addr. solve_addr. }
    subst a_ret.
    assert (Hret_eq : allocator_malloc_instrs_n 10 =
      encodeInstrsW [Jalr cnull cra]) by reflexivity.
    iEval (rewrite Hret_eq) in "Hret_code".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hcnull $Hret_code]"); eauto.
    { rewrite -Hstart in H0. unfold allocator_malloc_block_addr in *. cbn in *. solve_addr. }
    iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
    iEval (rewrite -Hret_eq) in "Hret_code".
    iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit10 -Hstart) in "Hmalloc_code".
    iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himport Hkey Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himport Hkey Hcode".
      { iFrame "Hcode". iApply allocator_imports_split. iFrame. }
      iExists next. iFrame. }
    iApply "Hpost". iFrame "∗".
  Qed.

  (** A malformed allocator capability in [ca0] traps in block 0. *)

  Lemma allocator_malloc_invalid_capability_spec
    (E : coPset) (wsealed : Word) (P : iProp Σ) :

    ↑Nallocator_service ⊆ E ->
    (is_sealed_with_o wsealed AllocOtype = false \/ get_tag wsealed = false) ->

    allocator_service_ctx ∗
    na_own cerise_nais E ∗
    PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
      allocator_malloc_pcc_addr ∗
    ca0 ↦ᵣ wsealed ∗
    ctp ↦ᵣ - ∗
    ct3 ↦ᵣ - ∗
    ct4 ↦ᵣ -
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    iIntros (HEservice Hwsealed)
      "(#Hservice & Hna & HPC & Hca0 & [%wtp Hctp] & [%w3 Hct3] & [%w4 Hct4])".
    destruct allocator_malloc_entry_facts as (Hpc & Hdisjoint & Hstart & Hkey_bounds).
    (* Open the service invariant and recover the allocator code. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct (allocator_imports_split with "Himports") as "[Himport Hkey]".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite Hstart) in "Hmalloc_code".
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Howner_code" "Hmalloc_cont".
    iEval (rewrite allocator_malloc_owner_code) in "Howner_code".
    iApply (allocator_owner_invalid_spec with
      "[$HPC $Hctp $Hct3 $Hct4 $Hca0 $Hkey $Howner_code]"); eauto.
  Qed.

  (** A positive integer size either exceeds the remaining suffix or obtains
      a fresh, exactly bounded, zeroed range. The bump cursor stays hidden in
      the service invariant. *)

  Lemma allocator_malloc_valid_observe_correct
    (P : Addr → Addr → Prop)
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (n id : Z) (S : gset Addr)
    (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    (0 < n)%Z ->

    ⊢ (

       (□ (∀ next b e allocations,
          ⌜allocator_chain (heap_b ^+ 1)%a next allocations⌝ -∗
          ⌜allocator_header_bounds next heap_e b e⌝ -∗
          allocator_history allocations -∗
          allocator_history allocations ∗ ⌜P b e⌝)) ∗
       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_owner_id id S ∗
       a_owner ↦ₐ WInt id ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ WInt n ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt id ∗
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

          ((allocator_owner_id id S ∗
            ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
            ca1 ↦ᵣ WInt 0)
           ∨ (∃ (b e : Addr),
                ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧
                  (e - b = n)%Z⌝ ∗
                ca0 ↦ᵣ WCap true RW Global b e b ∗
                ca1 ↦ᵣ WInt 0 ∗
                ⌜P b e⌝ ∗
                allocator_owner_id id (S ∪ {[b]}) ∗
                free_right b ∗
                allocator_allocation b e (id, 0%Z) ∗
                allocator_zeroed b e))

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEheap HEservice Hshadow_a Hbounds_a Hpositive.
    iIntros "(#Hobserve & #Hctx & #Hservice & Hna & Howner & Ha & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    destruct allocator_malloc_entry_facts as (Hpc & Hdisjoint & Hstart & Hkey_bounds).
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iDestruct (allocator_imports_split with "Himports") as "[Himport Hkey]".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_0 "Hcode" as "Hmalloc_code" "Hcode_cont".
    iEval (rewrite Hstart) in "Hmalloc_code".
    (* Load the owner identifier of the allocator capability. *)
    assert (Hsplit : allocator_malloc_instrs =
      allocator_malloc_instrs_n 0 ++
      concat (encodeInstrsW <$> drop 1 assembled_allocator_malloc)) by reflexivity.
    iEval (rewrite Hsplit) in "Hmalloc_code".
    focus_block_0 "Hmalloc_code" as "Howner_code" "Hmalloc_cont".
    iEval (rewrite allocator_malloc_owner_code) in "Howner_code".
    iDestruct "Hctp" as (wtp) "Hctp".
    iDestruct "Hct3" as (w3) "Hct3".
    iDestruct "Hct4" as (w4) "Hct4".
    iApply (allocator_owner_spec with
      "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Hkey $Ha $Howner_code]"); eauto.
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Ha & Howner_code)".
    iEval (rewrite -allocator_malloc_owner_code) in "Howner_code".
    iDestruct ("Hmalloc_cont" with "Howner_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit) in "Hmalloc_code".
    assert (Haddr1 : (allocator_malloc_pcc_addr ^+
      length (allocator_owner_instrs ctp ca0 ct3 ct4))%a =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1) by reflexivity.
    iEval (rewrite Haddr1) in "HPC".
    (* Check the requested size. *)
    assert (Hsplit1 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 1 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 1 ++
       concat (encodeInstrsW <$> drop 2 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit1) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_check Ha_check
      "Hcheck_code" "Hmalloc_cont".
    assert (Ha_check_eq : a_check =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 1).
    { unfold allocator_malloc_block_addr. solve_addr. }
    subst a_check.
    assert (Hsize : allocator_positive_size (WInt n)).
    { exists n. split; [reflexivity|exact Hpositive]. }
    iApply (allocator_malloc_size_check_valid_spec with
      "[- $HPC $Hca1 $Hct3 $Hcheck_code]"); eauto.
    { rewrite -Hstart. exact H. }
    iNext. iIntros "(Hca1 & Hct3 & Hcheck_code & HPC)".
    iDestruct ("Hmalloc_cont" with "Hcheck_code") as "Hmalloc_code".
    iEval (rewrite -Hsplit1) in "Hmalloc_code".
    (* Prepare the allocation, branching on the remaining capacity. *)
    assert (Hsplit2 : allocator_malloc_instrs =
      concat (encodeInstrsW <$> take 2 assembled_allocator_malloc) ++
      (allocator_malloc_instrs_n 2 ++
       concat (encodeInstrsW <$> drop 3 assembled_allocator_malloc)))
      by reflexivity.
    iEval (rewrite Hsplit2) in "Hmalloc_code".
    focus_block_nochangePC 1 "Hmalloc_code" as a_prepare Ha_prepare
      "Hprepare_code" "Hmalloc_cont".
    assert (Haddr2 : a_prepare =
      allocator_malloc_block_addr allocator_malloc_pcc_addr 2).
    { unfold allocator_malloc_block_addr. solve_addr. }
    subst a_prepare.
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3b) "Hct3".
    iDestruct "Hca2" as (wa2) "Hca2".
    destruct (decide (n + allocator_header_words <= heap_e - next)%Z) as [Hroom|Hoom].
    - iApply (allocator_malloc_prepare_success_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca1 $Hctp $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hprepare_code]"); eauto.
      { rewrite -Hstart. exact H. }
      iNext. iIntros "(%b & %finish & %Hbounds & Hpending & Hrange_mem &
        Hcgp & Hca1 & Hctp & Hct0 & Hct1 & Hprepare_code & HPC & Hct2 & Hct3 & Hct4 & Hca2)".
      destruct Hbounds as (Hbase & Hfinish & Hrange).
      unfold allocator_header_words in Hbase.
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit2) in "Hmalloc_code".
      iDestruct "Hpending" as (allocations)
        "(%Hnext & %Hchunk & Hslot & Hroot & Hfree & Hheaders & Hhistory & Howners & Hhead)".
      iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
      iDestruct ("Hobserve" $! next b finish allocations with "[] [] Hhistory")
        as "[Hhistory %HP]"; [iPureIntro; exact Hchain|iPureIntro; exact Hchunk|].
      (* Zero the newly allocated addresses. *)
      assert (Hsplit3 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 3 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 3 ++
         concat (encodeInstrsW <$> drop 4 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit3) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_zero Ha_zero
        "Hzero_code" "Hmalloc_cont".
      assert (Haddr3 : a_zero =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 3).
      { unfold allocator_malloc_block_addr.
        clear -Ha_zero. cbn [take concat fmap] in *. solve_addr. }
      subst a_zero.
      assert (Hzero_eq : allocator_malloc_instrs_n 3 =
        allocator_zero_instrs ca2 ct2 ct3) by reflexivity.
      iEval (rewrite Hzero_eq) in "Hzero_code".
      iApply (allocator_zero_spec ca2 ct2 ct3 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 3)
        RW Global b finish (WInt 0)
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
      iNext. iIntros "(HPC & Hca2 & Hct2 & Hct3 & Hzeros & Hzero_code)".
      iEval (rewrite -Hzero_eq) in "Hzero_code".
      iDestruct ("Hmalloc_cont" with "Hzero_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit3) in "Hmalloc_code".
      (* Fetch the shadow capability and translate the allocated bounds. *)
      assert (Hsplit4 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 4 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 4 ++
         concat (encodeInstrsW <$> drop 5 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit4) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_fetch Ha_fetch
        "Hfetch_code" "Hmalloc_cont".
      assert (Haddr4 : a_fetch =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { unfold allocator_malloc_block_addr.
        clear -Ha_fetch. cbn [take concat fmap] in *. solve_addr. }
      subst a_fetch.
      assert (Hpc4 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 3 ^+
        length (allocator_zero_instrs ca2 ct2 ct3))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 4).
      { unfold allocator_malloc_block_addr. clear -Hpc. solve_addr. }
      iEval (rewrite Hpc4) in "HPC".
      pose proof allocator_size_imports as Himports_size.
      assert (Hfetch_eq : allocator_malloc_instrs_n 4 =
        fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
        by reflexivity.
      iEval (rewrite Hfetch_eq) in "Hfetch_code".
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
      { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
        destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
        exfalso. unfold is_heap_address in Hheap.
        apply withinBounds_true_iff in Hheap;
        pose proof heap_shadow_disjoint as Hd;
        rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
        apply (Hd shadow_b); apply elem_of_finz_seq_between;
        try exact Hheap;
        pose proof shadow_valid; solve_addr. }
      { discriminate. }
      { discriminate. }
      { discriminate. }
      iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hfetch_code)".
      iEval (cbn) in "Hctp".
      iEval (rewrite Himpaddr) in "Himport".
      iEval (rewrite -Hfetch_eq) in "Hfetch_code".
      iDestruct ("Hmalloc_cont" with "Hfetch_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit4) in "Hmalloc_code".
      assert (Hsplit5 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 5 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 5 ++
         concat (encodeInstrsW <$> drop 6 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit5) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_translate Ha_translate
        "Htranslate_code" "Hmalloc_cont".
      assert (Haddr5 : a_translate =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { unfold allocator_malloc_block_addr.
        clear -Ha_translate. cbn [take concat fmap] in *. solve_addr. }
      subst a_translate.
      assert (Hpc5 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 4 ^+
        length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 5).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc5) in "HPC".
      iApply (allocator_translate_spec with
        "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code]");
        eauto; try solve_addr.
      iNext. iIntros
        "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hctp & Hca2 & Htranslate_code)".
      iDestruct ("Hmalloc_cont" with "Htranslate_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit5) in "Hmalloc_code".
      iAssert ([[b, finish]] ↦ₐ
        [[replicate (length (finz.seq_between b finish)) (WInt 0)]])%I
        with "[Hzeros]" as "Hzeros".
      { rewrite /region_pointsto big_sepL2_replicate_r; last reflexivity.
        iFrame. }
      (* Clear the shadow bits for the allocated range. *)
      assert (Hsplit6 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 6 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 6 ++
         concat (encodeInstrsW <$> drop 7 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit6) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_paint Ha_paint
        "Hpaint_code" "Hmalloc_cont".
      assert (Haddr6 : a_paint =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { unfold allocator_malloc_block_addr.
        clear -Ha_paint. cbn [take concat fmap] in *. solve_addr. }
      subst a_paint.
      assert (Hpc6 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 5 ^+
        length (allocator_malloc_instrs_n 5))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 6).
      { unfold allocator_malloc_block_addr. solve_addr. }
      iEval (rewrite Hpc6) in "HPC".
      pose (sb := (shadow_b ^+ (b - heap_b))%a).
      pose (se := (shadow_b ^+ (finish - heap_b))%a).
      assert (Hshadow : (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a).
      { pose proof heap_shadow_same_size. unfold sb, se. solve_addr. }
      assert (Hlen_shadow : (se - sb = finish - b)%Z).
      { unfold sb, se. pose proof heap_shadow_same_size. solve_addr. }
      assert (Htranslation : ∀ x, (b <= x /\ x < finish)%a ->
        heap_to_shadow x = Some (sb ^+ (x - b))%a).
      { intros x Hx. rewrite allocator_translation_affine.
        unfold translate_region.
        assert (Hxheap : withinBounds heap_b heap_e x = true).
        { apply withinBounds_true_iff. solve_addr. }
        rewrite Hxheap. unfold sb.
        pose proof heap_shadow_same_size. solve_addr. }
      assert (Hpaint_eq : allocator_malloc_instrs_n 6 =
        allocator_paint_instrs ctp ca2 ShadowLive) by reflexivity.
      iEval (rewrite Hpaint_eq) in "Hpaint_code".
      iApply (allocator_paint_spec ShadowLive ctp ca2 E RX Global
        allocator_pcc_b allocator_pcc_e
        (allocator_malloc_block_addr allocator_malloc_pcc_addr 6)
        b finish sb se
        (replicate (length (finz.seq_between b finish)) (WInt 0))
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
      iNext. iIntros "(HPC & Hctp & Hca2 & Hzeros & Hpaint_code)".
      iEval (rewrite -Hpaint_eq) in "Hpaint_code".
      iDestruct ("Hmalloc_cont" with "Hpaint_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit6) in "Hmalloc_code".
      (* Publish the new bump cursor and set ALLOC_OK. *)
      assert (Hsplit7 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 7 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 7 ++
         concat (encodeInstrsW <$> drop 8 assembled_allocator_malloc)))
        by reflexivity.
      iEval (rewrite Hsplit7) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_publish Ha_publish
        "Hpublish_code" "Hmalloc_cont".
      assert (Haddr7 : a_publish =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 7).
      { unfold allocator_malloc_block_addr.
        clear -Ha_publish. cbn [take concat fmap] in *. solve_addr. }
      subst a_publish.
      assert (Hoff5 : allocator_malloc_block_addr allocator_malloc_pcc_addr 6 =
        (allocator_malloc_pcc_addr ^+ 51)%a) by reflexivity.
      assert (Hoff6 : allocator_malloc_block_addr allocator_malloc_pcc_addr 7 =
        (allocator_malloc_pcc_addr ^+ 55)%a) by reflexivity.
      assert (Hlenpaint : length (allocator_paint_instrs ctp ca2 ShadowLive) = 4)
        by reflexivity.
      assert (Hpc7 : (allocator_malloc_block_addr allocator_malloc_pcc_addr 6 ^+
        length (allocator_paint_instrs ctp ca2 ShadowLive))%a =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 7).
      { clear -Hoff5 Hoff6 Hlenpaint.
        rewrite Hoff5 Hoff6 Hlenpaint.
        rewrite incr_addr_opt_add_twice.
        { replace (51 + 4)%Z with 55%Z by lia; reflexivity. }
        all: lia. }
      iEval (rewrite Hpc7) in "HPC".
      iApply (allocator_malloc_publish_spec with
        "[- $HPC $Hcgp $Hct0 $Hct4 $Hca0 $Hca1 $Hslot $Hpublish_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      { exact Hbase. }
      { exact Hfinish. }
      { split; [exact (proj1 Hnext)|exact Hrange]. }
      iNext. iIntros
        "(HPC & Hcgp & Hct0 & Hct4 & Hca0 & Hca1 & Hslot & Hpublish_code)".
      iDestruct ("Hmalloc_cont" with "Hpublish_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit7) in "Hmalloc_code".
      (* Return the allocation and restore the service invariant. *)
      assert (Hsplit10 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 10 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 10) by reflexivity.
      iEval (rewrite Hsplit10) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr10 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 10).
      { unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 10 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { unfold allocator_malloc_block_addr in *; cbn; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit10 -Hstart) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod (allocator_service_commit_spec next b finish id 0%Z allocations S
        (proj1 Hnext) Hchunk
        with "Hslot Hroot Hfree Hheaders Hhistory Howners Howner Hhead")
        as "(Hdata & Hreceipt & Howner & Hright)".
      iMod ("Hclose" with "[Himport Hkey Hcode Hdata Hna]") as "Hna".
      { iSplitR "Hna"; last iFrame.
        iNext. iSplitL "Himport Hkey Hcode".
        { iFrame "Hcode". iApply allocator_imports_split. iFrame. }
        iExists finish. iExact "Hdata". }
      iApply "Hpost". iFrame "∗".
      iRight. iExists b, finish.
      iSplit.
      { iPureIntro. split.
        { solve_addr. }
        { clear -Hfinish. solve_addr. } }
      iFrame "Hca0 Hreceipt Howner Hright".
      iSplit; first (iPureIntro; exact HP).
      rewrite /allocator_zeroed /region_pointsto big_sepL2_replicate_r;
        last reflexivity.
      iFrame.
    - assert (Hcapacity : (heap_e - next - allocator_header_words < n)%Z) by lia.
      iApply (allocator_malloc_prepare_oom_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca1 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hprepare_code]"); eauto.
      { rewrite -Hstart. exact H. }
      iNext. iIntros
        "(Hdata & Hcgp & Hca1 & Hct0 & Hct1 & Hprepare_code & HPC & Hct2 & Hct3 & Hct4 & Hca2)".
      iDestruct ("Hmalloc_cont" with "Hprepare_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit2) in "Hmalloc_code".
      (* Capacity is exhausted; return ALLOC_NO_MEMORY without changing the state. *)
      assert (Hsplit9 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 9 assembled_allocator_malloc) ++
        (allocator_malloc_instrs_n 9 ++ allocator_malloc_instrs_n 10))
        by reflexivity.
      iEval (rewrite Hsplit9) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_oom Ha_oom
        "Hoom_code" "Hmalloc_cont".
      assert (Haddr9 : a_oom =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 9).
      { unfold allocator_malloc_block_addr.
        clear -Ha_oom. cbn [take concat fmap] in *. solve_addr. }
      subst a_oom.
      iApply (allocator_malloc_oom_block_spec with
        "[- $HPC $Hca0 $Hca1 $Hoom_code]").
      { rewrite -Hstart; exact H. }
      { exact Hpc. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hca0 & Hca1 & Hoom_code)".
      iDestruct ("Hmalloc_cont" with "Hoom_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit9) in "Hmalloc_code".
      assert (Hsplit10 : allocator_malloc_instrs =
        concat (encodeInstrsW <$> take 10 assembled_allocator_malloc) ++
        allocator_malloc_instrs_n 10) by reflexivity.
      iEval (rewrite Hsplit10) in "Hmalloc_code".
      focus_block_nochangePC 1 "Hmalloc_code" as a_ret Ha_ret
        "Hret_code" "Hmalloc_cont".
      assert (Haddr10 : a_ret =
        allocator_malloc_block_addr allocator_malloc_pcc_addr 10).
      { unfold allocator_malloc_block_addr.
        clear -Ha_ret. cbn [take concat fmap] in *. solve_addr. }
      subst a_ret.
      assert (Hret_eq : allocator_malloc_instrs_n 10 =
        encodeInstrsW [Jalr cnull cra]) by reflexivity.
      iEval (rewrite Hret_eq) in "Hret_code".
      iDestruct "Hcnull" as (wnull) "Hcnull".
      iApply (allocator_return_spec with
        "[- $HPC $Hcra $Hcnull $Hret_code]").
      { unfold allocator_malloc_block_addr in *; cbn; solve_addr. }
      { exact Hdisjoint. }
      iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code & _)".
      iEval (rewrite -Hret_eq) in "Hret_code".
      iDestruct ("Hmalloc_cont" with "Hret_code") as "Hmalloc_code".
      iEval (rewrite -Hsplit10 -Hstart) in "Hmalloc_code".
      iDestruct ("Hcode_cont" with "Hmalloc_code") as "Hcode".
      iEval (rewrite -/allocator_code) in "Hcode".
      iMod ("Hclose" with "[Himport Hkey Hcode Hdata Hna]") as "Hna".
      { iSplitR "Hna"; last iFrame.
        iNext. iSplitL "Himport Hkey Hcode".
        { iFrame "Hcode". iApply allocator_imports_split. iFrame. }
        iExists next. iFrame. }
      iApply "Hpost". iFrame "∗". iLeft. iFrame.
  Qed.

  Lemma allocator_malloc_valid_correct
    (E : coPset) (g_owner : Locality) (a_owner : Addr) (n id : Z) (S : gset Addr)
    (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    (0 < n)%Z ->

    ⊢ (

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_owner_id id S ∗
       a_owner ↦ₐ WInt id ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_malloc_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ allocator_capability g_owner a_owner ∗
       ca1 ↦ᵣ WInt n ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗

       ▷ (na_own cerise_nais E ∗
          a_owner ↦ₐ WInt id ∗
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

          ((allocator_owner_id id S ∗
            ca0 ↦ᵣ WInt ALLOC_NO_MEMORY ∗
            ca1 ↦ᵣ WInt 0)
           ∨ (∃ (b e : Addr),
                ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧
                  (e - b = n)%Z⌝ ∗
                ca0 ↦ᵣ WCap true RW Global b e b ∗
                ca1 ↦ᵣ WInt 0 ∗
                allocator_owner_id id (S ∪ {[b]}) ∗
                free_right b ∗
                allocator_allocation b e (id, 0%Z) ∗
                allocator_zeroed b e))

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEheap HEservice Hshadow_a Hbounds_a Hpositive.
    iIntros "(#Hctx & #Hservice & Hna & Howner & Ha & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    iApply (allocator_malloc_valid_observe_correct (fun _ _ => True)
      with "[-]"); eauto.
    iSplitR "Hna Howner Ha HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hpost".
    { iModIntro. iIntros (next b e allocations) "_ _ Hhistory".
      iFrame. }
    iFrame "Hctx Hservice Hna Howner Ha HPC Hcgp Hcra Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iNext. iIntros "(Hna & Ha & HPC & Hcgp & Hcra & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hresult)".
    iApply "Hpost". iFrame "Hna Ha HPC Hcgp Hcra Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
    iDestruct "Hresult" as "[Hoom|Hsuccess]"; first (iLeft; iExact "Hoom").
    iRight. iDestruct "Hsuccess" as (b e) "(Hbounds & Hca0 & Hca1 & _ & Howner & Hright & Hreceipt & Hzeroed)".
    iExists b, e. iFrame.
  Qed.


End AllocatorMallocBlocks.
