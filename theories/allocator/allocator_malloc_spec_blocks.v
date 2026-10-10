From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_resource_spec allocator_header_spec.

(** The block specifications of [malloc]: one lemma per block of the
    assembled code. The top-level specifications are in
    [allocator_malloc_spec]. *)

(** Address of an assembled block relative to the entry point. *)

Definition allocator_malloc_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_malloc)))%a.

Section AllocatorMallocBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_malloc_size_check_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 0 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_positive_size wreq.(lw) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ca0 ↦ᵣ wreq ∗
    ct3 ↦ᵣ wtmp ∗
    codefrag pc_a code ∗
    ▷ (ca0 ↦ᵣ wreq ∗
         ct3 ↦ᵣ - ∗
         codefrag pc_a code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 1)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hcont Hpc Hdisjoint (n & Hreq & Hpositive); subst code.
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(HPC & Hca0 & Hct3 & Hcode & Hφ)".
    codefrag_facts "Hcode".
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
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_size_check_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a : Addr) (wreq wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 0 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    ¬ allocator_positive_size wreq.(lw) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ca0 ↦ᵣ wreq ∗
    ct3 ↦ᵣ wtmp ∗
    codefrag pc_a code ∗
    ▷ (ca0 ↦ᵣ wreq ∗
         ct3 ↦ᵣ - ∗
         codefrag pc_a code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 9)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hcont Hpc Hdisjoint Hinvalid; subst code.
    destruct wreq as [wreq π]; cbn in Hinvalid.
    iIntros "(HPC & Hca0 & Hct3 & Hcode & Hφ)".
    codefrag_facts "Hcode".
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

  Lemma allocator_malloc_reject_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : LWord)
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
           (allocator_malloc_block_addr pc_a 11) ∗
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
    assert (Hstep : (pc_a ^+ 57)%a =
      ((allocator_malloc_block_addr pc_a 9) ^+ 1)%a).
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
    assert (Hret : (allocator_malloc_block_addr pc_a 9 ^+ 5)%a =
      allocator_malloc_block_addr pc_a 11).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_oom_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 10 in
    let code := allocator_malloc_instrs_n 10 in
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wstatus ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 11) ∗
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
    assert (Hstep : (pc_a ^+ 60)%a =
      ((allocator_malloc_block_addr pc_a 10) ^+ 1)%a).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    assert (Hca0val :
      (if decide (ca0 = cnull) then 0%Z else (-2)%Z) = ALLOC_NO_MEMORY).
    { unfold ALLOC_NO_MEMORY.
      destruct (decide (ca0 = cnull)); [discriminate|done]. }
    iEval (rewrite Hca0val) in "Hca0".
    assert (Hret : (allocator_malloc_block_addr pc_a 10 ^+ 2)%a =
      allocator_malloc_block_addr pc_a 11).
    { unfold allocator_malloc_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.


  (** The prepare block: reload the heap root, check the capacity, bound the
      payload capability and write the header. The strong allocate step rides
      on the rebasing [subseg ct4 ct1 ct2]: it claims the payload cells for a
      fresh identifier [ι ∉ S], which the payload capability carries. *)
  Lemma allocator_malloc_prepare_success_spec
    (E : coPset)
    (pc_b pc_e pc_a next b finish : Addr) (n : Z) (πn : option AId) (S : gset AId)
    (w0 w1 w2 w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    (0 < n)%Z ->
    (heap_b < next)%a ->
    (next + allocator_header_words)%a = Some b ->
    (b + n)%a = Some finish ->
    (finish <= heap_e)%a ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    allocator_range_memory next b ∗
    ([∗ list] a ∈ finz.seq_between b finish, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
    codefrag start code ∗
    ▷ (∀ ι : AId,
         ⌜ι ∉ S⌝ ∗
         alloc_obj ι b finish ∗
         ι ↦st{1} ALive ∗
         ([∗ list] a ∈ finz.seq_between b finish,
            a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
         allocator_header next b finish (0%Z, 0%Z) ∗
         allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ WInt n @@? πn ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt finish ∗
         ct3 ↦ᵣ WInt 0 ∗
         ct4 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
         ca2 ↦ᵣ (WCap true RW Global b finish b) @@ ι ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 2) ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hcgp_pc Hpositive Hnext Hbase Hfinish Hroom;
      subst start code.
    iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hslot & Hheader &
      Hpayload & Hcode & Hφ)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 1 = (pc_a ^+ 6)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.
    unfold allocator_header_words in Hbase.
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.

    (* Reload the heap root: it is identifier-less and has authority, so it
       loads exactly. *)
    unfold lword_of_word.
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff. solve_addr. } }
    { done. }
    { intros _. left. pose proof heap_valid. apply has_authority_heap_cap; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between.
      unfold allocator_malloc_instrs in Hpc. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    assert (Hstep : (pc_a ^+ 7)%a = ((pc_a ^+ 6)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    assert (Hrange : (next < b /\ b < finish /\ finish <= heap_e)%a) by solve_addr.

    (* Read the bump bounds and reserve space for the header. *)
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca0. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with false
      by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .malloc_no_memory ct3. *)
    iInstr "Hcode".
    (* Compute the payload bounds and restrict its capability. *)
    (* Add ct1 ct1 allocator_header_words. *)
    iInstr "Hcode".
    assert (Hbword : (next + 3)%Z = b) by solve_addr.
    rewrite Hbword.
    (* Add ct2 ct1 ca0. *)
    iInstr "Hcode".
    assert (Heword : (b + n)%Z = finish) by solve_addr.
    rewrite Heword.
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    (* Lea ct4 allocator_header_words. *)
    iInstr "Hcode".

    (* The strong allocate step, riding on the rebasing Subseg: the payload
       cells are claimed by a fresh identifier [ι ∉ S]. *)
    iMod (rules_registry.reg_alloc _ b finish S with "Hpayload")
      as (ι Hι) "(#Hobj & Htok & Hpayload)".
    (* Subseg ct4 ct1 ct2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_subseg_rebase _ _ _ _ _ _ _ _ ct4 ct1 ct2 RW Global heap_b heap_e b _ b _ finish
              b finish _ ι 1 ALive with "[$HPC $Hi $Hct4 $Hct1 $Hct2 $Hobj $Htok]");
      try solve_pure.
    { apply isCorrectPC_intro; [solve_addr | auto]. }
    { rewrite /isWithin. pose proof heap_valid. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct1 & Hct2 & Hct4 & _ & Htok)". wp_pure.
    iSpecialize ("Hcode" with "Hi").

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
      Hthirdaddr
      (finz_seq_between_cons (next ^+ 2)%a b Hthirdb) big_sepL_cons
      Hthirdend Hempty) in "Hheader".
    iDestruct "Hheader" as "([%wend Hend] & [%wr1 Hr1] & [%wr2 Hr2] & _)".
    (* Store ct0 ct2. *)
    iInstr_success "Hcode".
    { eapply (disjoint_from_shadow_not_in heap_b heap_e next); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply isCorrectPC_intro; [solve_addr | auto]. }
    { apply withinBounds_true_iff. solve_addr. }
    (* Store ct0 0 1. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_z_imm _ _ _ _ _ _ _ _ _ _ ct0 0 wr1 _ _ _ _ _ (next ^+ 1)%a 1
      with "[$HPC $Hi $Hct0 $Hr1]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply isCorrectPC_intro; [solve_addr | auto]. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hr1)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Store ct0 0 2. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_z_imm _ _ _ _ _ _ _ _ _ _ ct0 0 wr2 _ _ _ _ _ (next ^+ 2)%a 2
      with "[$HPC $Hi $Hct0 $Hr2]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { apply isCorrectPC_intro; [solve_addr | auto]. }
    { apply withinBounds_true_iff. solve_addr. }
    { solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hr2)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Mov ca2 ct4. *)
    iInstr "Hcode".
    iApply ("Hφ" $! ι).
    iFrame "Hobj Htok Hpayload Hslot Hcgp Hca0 Hct0 Hct1 Hct2 Hct3 Hca2 Hct4".
    iSplit; first done.
    iSplitL "Hend Hr1 Hr2".
    { rewrite /allocator_header /=. iFrame. done. }
    rewrite Hstart.
    replace (allocator_malloc_block_addr pc_a 2) with (pc_a ^+ 22)%a by reflexivity.
    assert (Hnextpc : ((pc_a ^+ 6)%a ^+ 16)%a = (pc_a ^+ 22)%a) by solve_addr.
    iEval (rewrite Hnextpc) in "HPC". iFrame.
  Qed.

  Lemma allocator_malloc_prepare_oom_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (n : Z) (πn : option AId)
    (w0 w1 w2 w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 1 in
    let code := allocator_malloc_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_malloc_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_malloc_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    (0 < n)%Z ->
    (heap_b < next /\ next <= heap_e)%a ->
    (heap_e - next - allocator_header_words < n)%Z ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag start code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ WInt n @@? πn ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt next ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_malloc_block_addr pc_a 10) ∗
         ct2 ↦ᵣ WInt heap_e ∗
         ct3 ↦ᵣ WInt 1 ∗
         ct4 ↦ᵣ w4 ∗
         ca2 ↦ᵣ wa2
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hcgp_pc Hpositive Hnext Hoom;
      subst start code.
    iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hslot & Hcode & Hφ)".
    codefrag_facts "Hcode".
    assert (Hstart : allocator_malloc_block_addr pc_a 1 = (pc_a ^+ 6)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode".
    iEval (rewrite Hstart) in "HPC".
    rewrite Hstart in H.
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.

    (* Reload the heap root. *)
    unfold lword_of_word.
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff. solve_addr. } }
    { done. }
    { intros _. left. pose proof heap_valid. apply has_authority_heap_cap; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between.
      unfold allocator_malloc_instrs in Hpc. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    assert (Hstep : (pc_a ^+ 7)%a = ((pc_a ^+ 6)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep) in "HPC".
    (* GetA ct1 ct0. *)
    iInstr "Hcode".
    (* GetE ct2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct2 ct1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    unfold allocator_header_words in Hoom.
    (* Lt ct3 ct3 ca0. *)
    iInstr "Hcode".
    replace (heap_e - next - 3 <? n)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    (* Jnz .malloc_no_memory ct3. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct3]"); try solve_pure.
    { apply isCorrectPC_intro; [solve_addr | auto]. }
    { instantiate (1 := (pc_a ^+ 59)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hct3)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_malloc_publish_spec
    (E : coPset)
    (pc_b pc_e pc_a next b finish : Addr) (n : Z) (πn : option AId) (π : option AId) (wstatus : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_malloc_block_addr pc_a 8 in
    let code := allocator_malloc_instrs_n 8 in
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
    ct4 ↦ᵣ WCap true RW Global b finish b @@? π ∗
    ca0 ↦ᵣ WInt n @@? πn ∗
    ca1 ↦ᵣ wstatus ∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_malloc_block_addr pc_a 11) ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e finish ∗
         ct4 ↦ᵣ WCap true RW Global b finish b @@? π ∗
         ca0 ↦ᵣ WCap true RW Global b finish b @@? π ∗
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
    assert (Hstart : allocator_malloc_block_addr pc_a 8 = (pc_a ^+ 50)%a) by reflexivity.
    iEval (rewrite Hstart) in "Hcode HPC". rewrite Hstart in H.
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.
    (* Lea ct0 allocator_header_words. *)
    iInstr "Hcode".
    assert (Hstep1 : (pc_a ^+ 51)%a = ((pc_a ^+ 50)%a ^+ 1)%a) by solve_addr.
    iEval (rewrite Hstep1) in "HPC".
    (* Lea ct0 ca0. *)
    iInstr "Hcode".
    (* Store cgp ct0. *)
    iInstr_success "Hcode".
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff. solve_addr. } }
    all: try (apply isCorrectPC_intro; [solve_addr | auto]).
    all: try (apply withinBounds_true_iff; solve_addr).
    (* Mov ca0 ct4. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    (* Jmp .malloc_return. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
    replace (allocator_malloc_block_addr pc_a 11) with (pc_a ^+ 61)%a by reflexivity.
    assert (Hret : ((pc_a ^+ 50)%a ^+ 11)%a = (pc_a ^+ 61)%a) by solve_addr.
    iEval (rewrite Hret) in "HPC". iFrame.
  Qed.

End AllocatorMallocBlocks.
