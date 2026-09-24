From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_header_spec.

(** Address of an assembled block relative to the entry point. *)

Definition allocator_free_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_free)))%a.

Local Instance allocator_free_in_prefix_dec {MP : MachineParameters} next w :
  Decision (allocator_free_in_prefix next w).
Proof.
  unfold allocator_free_in_prefix.
  destruct w as [z|sb|tag p g b e a|ot sb].
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - destruct sb as [tag p g b e a|tag p g b e a].
    + destruct tag.
      * destruct (decide (heap_b < b /\ b < e /\ e <= next)%a) as [Hbounds|Hbounds].
        { left. exists p, g, b, e, a. auto. }
        right. intros (p' & g' & b' & e' & a' & Heq & Hrange).
        inversion Heq; subst. contradiction.
      * right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
    + right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
Defined.

Section AllocatorFreeTraversal.
  Context {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {allocatorg : allocatorG Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.

  (** At the search loop, [allocations] is the unvisited suffix. The visited
      prefix is framed using [allocator_headers_app_spec], so unfolding one
      list node supplies exactly the header read by block 4. Blocks 3 and 5
      implement the loop guard and the advance to the tail, respectively. *)

  Local Lemma allocator_free_search_loop_outcomes_aux
    (E : coPset) (pc_b pc_e pc_a next h b e : Addr)
    (allocations : list allocator_header_entry) (w3 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 3 in
    let code := concat (encodeInstrsW <$> take 3 (drop 3 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < h /\ h <= next /\ next <= heap_e)%a ->

    allocator_headers h next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ WCap true RW Global heap_b heap_e h ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers h next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          (
            ⌜allocator_has_bounds allocations b e⌝ ∗
            PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 6)
          )
          ∨
          (
            ⌜¬ allocator_has_bounds allocations b e⌝ ∗
            PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10)
          )
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }}
      )
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hrange; subst start code.
    revert h w3 wa2 Hrange.
    induction allocations as [| (base & finish & reserved) allocations IH]; intros h w3 wa2 Hrange.
    {
      iIntros "(%Hstop & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
      subst h.
      codefrag_facts "Hcode".
      (* GetA ct3 ct4. *)
      iInstr "Hcode".
      assert (Hstep : (pc_a ^+ 26)%a = (allocator_free_block_addr pc_a 3 ^+ 1)%a) by (unfold allocator_free_block_addr; solve_addr).
      iEval (rewrite Hstep) in "HPC".
      (* GetA ca2 ct0. *)
      iInstr "Hcode".
      (* Lt ct3 ct3 ca2. *)
      iInstr "Hcode".
      rewrite Z.ltb_irrefl.
      (* Jnz .free_header ct3. *)
      iInstr "Hcode".
      (* Jmp .free_invalid. *)
      iInstr "Hcode".
      assert (Hinvalid : (allocator_free_block_addr pc_a 3 ^+ 40)%a = allocator_free_block_addr pc_a 10) by (unfold allocator_free_block_addr; solve_addr).
      iEval (rewrite Hinvalid) in "HPC".
      iApply "Hφ".
      iFrame.
      iSplit; first done.
      iRight.
      iFrame.
      iPureIntro.
      unfold allocator_has_bounds.
      set_solver.
    }
    iIntros "((%Hbounds & (%Hbase & Hend & Hreserved) & Htail) & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    unfold allocator_header_words in Hbase.
    codefrag_facts "Hcode".
    (* GetA ct3 ct4. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 26)%a = (allocator_free_block_addr pc_a 3 ^+ 1)%a) by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* GetA ca2 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ca2. *)
    iInstr "Hcode".
    replace (h <? next)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_header ct3. *)
    iInstr "Hcode".
    (* Load ca2 ct4. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_notinstr _ ca2 ct4 with "[$HPC $Hi $Hca2 $Hct4 $Hend]"); try solve_pure.
    {
      eapply (disjoint_from_shadow_not_in heap_b heap_e h); first exact heap_shadow_disjoint.
      apply withinBounds_true_iff.
      solve_addr.
    }
    { reflexivity. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    {
      split; first done.
      apply withinBounds_true_iff.
      solve_addr.
    }
    iIntros "!> (HPC & Hca2 & Hi & Hct4 & Hend)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (cbn [load_word]) in "Hca2".
    (* GetA ct3 ct4. *)
    iInstr "Hcode".
    (* Add ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct1. *)
    iInstr "Hcode".
    destruct (decide (base = b)) as [->|Hbase_ne].
    + replace (h + 2 - b)%Z with 0%Z by solve_addr.
      (* Jnz .free_next ct3. *)
      iInstr "Hcode".
      (* Sub ct3 ca2 ct2. *)
      iInstr "Hcode".
      destruct (decide (finish = e)) as [->|Hend_ne].
      * rewrite Z.sub_diag.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        (* Jmp .free_found. *)
        iInstr "Hcode".
        assert (Hfound : (allocator_free_block_addr pc_a 3 ^+ 17)%a = allocator_free_block_addr pc_a 6) by (unfold allocator_free_block_addr; solve_addr).
        iEval (rewrite Hfound) in "HPC".
        iApply "Hφ".
        iFrame.
        iSplit; first done.
        iLeft.
        iFrame.
        iPureIntro.
        exists reserved.
        by left.
      * assert (Hneq : WInt (finish - e) ≠ WInt 0) by (intros Heq; injection Heq as Heq; apply Hend_ne; solve_addr).
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        iDestruct (allocator_headers_chain_spec with "Htail") as %Hchain.
        assert (Hmiss : ¬ allocator_has_bounds ((b, (finish, reserved)) :: allocations) b e).
        {
          intros (r & Hin).
          apply elem_of_cons in Hin as [Heq|Hin].
          - injection Heq as Heq.
            congruence.
          - pose proof (allocator_chain_member_bounds _ _ _ _ _ _ Hchain Hin).
            solve_addr.
        }
        assert (Hinvalid : (allocator_free_block_addr pc_a 3 ^+ 40)%a = allocator_free_block_addr pc_a 10) by (unfold allocator_free_block_addr; solve_addr).
        iEval (rewrite Hinvalid) in "HPC".
        iApply "Hφ".
        iFrame.
        iSplit; first done.
        iRight.
        iFrame.
        done.
    + assert (Hneq : WInt (h + 2 - b) ≠ WInt 0) by (intros Heq; injection Heq as Heq; apply Hbase_ne; solve_addr).
      (* Jnz .free_next ct3. *)
      iInstr "Hcode".
      (* GetA ct3 ct4. *)
      iInstr "Hcode".
      (* Sub ct3 ca2 ct3. *)
      iInstr "Hcode".
      (* Lea ct4 ct3. *)
      iInstr "Hcode".
      (* Jmp .free_search. *)
      iInstr "Hcode".
      iApply (IH finish with "[$Htail $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcode Hφ Hend Hreserved]"); first solve_addr.
      iNext.
      iIntros "(Htail & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hresult)".
      iApply "Hφ".
      iFrame.
      iSplit; first done.
      iDestruct "Hresult" as "[(%Hfound & HPC)|(%Hmiss & HPC)]".
      * iLeft.
        iFrame.
        iPureIntro.
        unfold allocator_has_bounds in *.
        set_solver.
      * iRight.
        iFrame.
        iPureIntro.
        intros (r & Hin).
        apply elem_of_cons in Hin as [Heq|Hin].
        { injection Heq as Heq; congruence. }
        apply Hmiss.
        exists r.
        exact Hin.
  Qed.

  Local Lemma allocator_free_search_loop_found_spec
    (E : coPset) (pc_b pc_e pc_a next h b e : Addr)
    (allocations : list allocator_header_entry) (w3 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 3 in
    let code := concat (encodeInstrsW <$> take 3 (drop 3 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < h /\ h <= next /\ next <= heap_e)%a ->

    allocator_has_bounds allocations b e ->

    allocator_headers h next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ WCap true RW Global heap_b heap_e h ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers h next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          ⌜allocator_has_bounds allocations b e⌝ ∗
          PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 6)
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }}
      )
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hrange Hfound; subst start code.
    iIntros "(Hheaders & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iApply (allocator_free_search_loop_outcomes_aux with
      "[$Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcode Hφ]"); eauto.
    iNext.
    iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hresult)".
    iDestruct "Hresult" as "[(%Hhas & HPC)|(%Hmiss & HPC)]".
    - iApply "Hφ". iFrame. iPureIntro. exact Hhas.
    - exfalso. apply Hmiss. exact Hfound.
  Qed.

  Local Lemma allocator_free_search_loop_missing_spec
    (E : coPset) (pc_b pc_e pc_a next h b e : Addr)
    (allocations : list allocator_header_entry) (w3 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 3 in
    let code := concat (encodeInstrsW <$> take 3 (drop 3 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < h /\ h <= next /\ next <= heap_e)%a ->

    ¬ allocator_has_bounds allocations b e ->

    allocator_headers h next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ WCap true RW Global heap_b heap_e h ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers h next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          ⌜¬ allocator_has_bounds allocations b e⌝ ∗
          PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10)
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }}
      )
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hrange Hmissing; subst start code.
    iIntros "(Hheaders & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iApply (allocator_free_search_loop_outcomes_aux with
      "[$Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcode Hφ]"); eauto.
    iNext.
    iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hresult)".
    iDestruct "Hresult" as "[(%Hhas & HPC)|(%Hmiss & HPC)]".
    - exfalso. apply Hmissing. exact Hhas.
    - iApply "Hφ". iFrame. iPureIntro. exact Hmiss.
  Qed.

  (** Full traversal also executes block 2, which rederives the first header
      from the heap root. No payload ownership is needed to identify a block. *)

  Local Lemma allocator_free_search_outcomes_aux
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 2 in
    let code := concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < next /\ next <= heap_e)%a ->

    allocator_headers (heap_b ^+ 1)%a next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers (heap_b ^+ 1)%a next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          (
            ⌜allocator_has_bounds allocations b e⌝ ∗
             PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 6)
          )
          ∨
          (
            ⌜¬ allocator_has_bounds allocations b e⌝ ∗
            PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10)
          )
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hnext; subst start code.
    iIntros "(Hheaders & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 20)%a = (allocator_free_block_addr pc_a 2 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* GetA ca2 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ca2. *)
    iInstr "Hcode".
    (* Add ct3 ct3 1. *)
    iInstr "Hcode".
    (* Lea ct4 ct3. *)
    iInstr "Hcode".
    assert (Hfirst : (next ^+ (heap_b - next + 1))%a = (heap_b ^+ 1)%a) by solve_addr.
    iEval (rewrite Hfirst) in "Hct4".
    assert (Hsearch : (allocator_free_block_addr pc_a 2 ^+ 6)%a = allocator_free_block_addr pc_a 3)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hsearch) in "HPC".
    assert (Hsplit : concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) =
      allocator_free_instrs_n 2 ++ concat (encodeInstrsW <$> take 3 (drop 3 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_search Ha_search "Hsearchcode" "Hcode_cont".
    assert (Ha_eq : a_search = allocator_free_block_addr pc_a 3)
      by (unfold allocator_free_block_addr in *; solve_addr).
    subst a_search.
    iApply (allocator_free_search_loop_outcomes_aux with
      "[- $Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hsearchcode]"); try assumption; first solve_addr.
    iNext. iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hsearchcode & Hresult)".
    iDestruct ("Hcode_cont" with "Hsearchcode") as "Hcode".
    iEval (rewrite -Hsplit) in "Hcode".
    iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_free_search_found_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 2 in
    let code := concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < next /\ next <= heap_e)%a ->

    allocator_has_bounds allocations b e ->

    allocator_headers (heap_b ^+ 1)%a next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers (heap_b ^+ 1)%a next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          ⌜allocator_has_bounds allocations b e⌝ ∗
          PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 6)
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hnext Hout; subst start code.
    iIntros "(Hheaders & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iApply (allocator_free_search_outcomes_aux with
      "[$Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcode Hφ]"); eauto.
    iNext.
    iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hresult)".
    iDestruct "Hresult" as "[(%Hhas & HPC)|(%Hmiss & HPC)]".
    - iApply "Hφ". iFrame. iPureIntro. exact Hhas.
    - exfalso. apply Hmiss. exact Hout.
  Qed.

  Local Lemma allocator_free_search_missing_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 2 in
    let code := concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < next /\ next <= heap_e)%a ->

    ¬ allocator_has_bounds allocations b e ->

    allocator_headers (heap_b ^+ 1)%a next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag start code ∗
    ▷ (
        allocator_headers (heap_b ^+ 1)%a next allocations ∗
        ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
        ct1 ↦ᵣ WInt b ∗
        ct2 ↦ᵣ WInt e ∗
        ct3 ↦ᵣ - ∗
        ct4 ↦ᵣ - ∗
        ca2 ↦ᵣ - ∗
        codefrag start code ∗
        (
          ⌜¬ allocator_has_bounds allocations b e⌝ ∗
          PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10)
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hnext Hout; subst start code.
    iIntros "(Hheaders & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hφ)".
    iApply (allocator_free_search_outcomes_aux with
      "[$Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hcode Hφ]"); eauto.
    iNext.
    iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hcode & Hresult)".
    iDestruct "Hresult" as "[(%Hhas & HPC)|(%Hmiss & HPC)]".
    - exfalso. apply Hout. exact Hhas.
    - iApply "Hφ". iFrame. iPureIntro. exact Hmiss.
  Qed.

  Definition allocator_free_shadow_resources (s : AllocStatus) (b : Addr) : iProp Σ :=
    match s with
    | ShadowLive => b ↦ₐ -
    | ShadowQuarantined => reclaim_token b
    end%I.

  (** This block only reads the shadow bit: ownership of a live cell or a
      reclaim token connects the observation to the shared allocator invariant.
      All resources survive either branch; painting starts at block 8. *)

  Local Lemma allocator_free_shadow_check_spec
    (E : coPset) (pc_b pc_e pc_a next b e sb : Addr)
    (s : AllocStatus) (w3 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 7 in
    let code := allocator_free_instrs_n 7 in
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    (shadow_b + (b - heap_b))%a = Some sb ->
    heap_to_shadow b = Some sb ->

    allocator_ctx ∗
    allocator_free_shadow_resources s b ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ca2 ↦ᵣ wa2 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    codefrag start code ∗
    ▷ (allocator_free_shadow_resources s b ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt e ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
         codefrag start code ∗
         (match s with
            | ShadowLive =>
                PC ↦ᵣ WCap true RX Global pc_b pc_e
                  (allocator_free_block_addr pc_a 8) ∗
                ct3 ↦ᵣ WInt 0 ∗
                ca2 ↦ᵣ WInt (e - b)
            | ShadowQuarantined =>
                PC ↦ᵣ WCap true RX Global pc_b pc_e
                  (allocator_free_block_addr pc_a 10) ∗
                ct3 ↦ᵣ WInt (encodeAllocStatus ShadowQuarantined -
                              encodeAllocStatus ShadowLive) ∗
                              ca2 ↦ᵣ wa2
            end)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code HE Hcont Hpc Hdisjoint Hbounds Hsb Htranslate; subst start code.
    iIntros "(#Hctx & Hres & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hca2 & Hctp & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 52)%a = (allocator_free_block_addr pc_a 7 ^+ 1)%a) by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Load ct3 ctp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iInv Nallocator as ">Hbody" "Hclose".
    assert (Hb_heap : b ∈ heap_addresses) by (rewrite elem_of_heap_addresses; apply withinBounds_true_iff; solve_addr).
    iDestruct (allocator_inv_lookup b with "Hbody") as (st) "[Hentry Hput]"; first done.
    iAssert (⌜shadow_status st = s⌝)%I with "[Hentry Hres]" as %Hstatus.
    {
      destruct s.
      - iDestruct "Hres" as (w) "Hmem".
        iDestruct (allocator_entry_memory_live with "Hentry Hmem") as %->.
        done.
      - iDestruct (allocator_entry_token_quarantined with "Hentry Hres") as %->.
        done.
    }
    iDestruct "Hentry" as "[Hshadow Hstate]".
    iEval (rewrite Hstatus) in "Hshadow".
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hshadow]"); try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htranslate)). }
    {
      apply heap_shadow_inverse.
      exact Htranslate.
    }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htranslate)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hshadow)".
    iMod ("Hclose" with "[Hshadow Hstate Hput]") as "_".
    {
      iNext.
      iApply "Hput".
      instantiate (1 := st).
      rewrite /allocator_entry Hstatus.
      iFrame.
    }
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowLive). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowLive) with (encodeAllocStatus ShadowLive).
    destruct s.
    - rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    assert (Hpaint : (allocator_free_block_addr pc_a 7 ^+ 7)%a = allocator_free_block_addr pc_a 8) by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hpaint) in "HPC".
    iApply "Hφ".
    iFrame.
    - assert (Hneq : WInt (encodeAllocStatus ShadowQuarantined - encodeAllocStatus ShadowLive) ≠ WInt 0).
    {
      intros Heq.
      injection Heq as Heq.
      assert (Henc : encodeAllocStatus ShadowQuarantined = encodeAllocStatus ShadowLive) by lia.
      apply (f_equal decodeAllocStatus) in Henc.
      rewrite !decode_encode_alloc_status_inv in Henc.
      discriminate.
    }
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    assert (Hinvalid : (allocator_free_block_addr pc_a 7 ^+ 14)%a = allocator_free_block_addr pc_a 10) by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hinvalid) in "HPC".
    iApply "Hφ".
    iFrame.
  Qed.

  Local Lemma allocator_free_success_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 9 in
    let code := allocator_free_instrs_n 9 in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wstatus ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_free_block_addr pc_a 11) ∗
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt ALLOC_OK ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 63)%a =
      ((allocator_free_block_addr pc_a 9) ^+ 1)%a).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_OK. *)
    iInstr "Hcode".
    (* Jmp .free_return. *)
    iInstr "Hcode".
    assert (Hret : (allocator_free_block_addr pc_a 9 ^+ 5)%a =
      allocator_free_block_addr pc_a 11).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Local Lemma allocator_free_prepare_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr)
    (wreq w0 w1 w2 w3 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_free_in_prefix next wreq ->

    allocator_ctx ∗
    allocator_service_data next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wreq ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_service_data next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ wreq ∗
         codefrag pc_a code ∗
         (∃ (p : Perm) (g : Locality) (b e a : Addr),
             ⌜wreq = WCap true p g b e a
               ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝ ∗
             PC ↦ᵣ WCap true RX Global pc_b pc_e
                 (allocator_free_block_addr pc_a 2) ∗
             ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
             ct1 ↦ᵣ WInt b ∗
             ct2 ↦ᵣ WInt e ∗
             ct3 ↦ᵣ WInt 0)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout HE Hcont Hpc Hdisjoint (p & g & b & e & a & -> & Hbounds); subst code.
    iIntros "(#Hctx & Hdata & HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    iDestruct "Hdata" as (allocations)
      "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_cap true p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* GetTag ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    rewrite /Z.b2z Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup heap_b with "Hbody") as (s) "[Hentry Hput]".
    {
      apply elem_of_heap_addresses.
      apply withinBounds_true_iff.
      pose proof heap_valid.
      solve_addr.
    }
    iDestruct (allocator_entry_free_token with "Hentry Hroot") as %->.
    iDestruct "Hentry" as "[Hs Hres]".
    iApply (wp_load_success_heap with "[$HPC $Hi $Hct0 $Hcgp $Hslot $Hs]"); try solve_pure.
    {
      eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow.
        rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions.
        set_solver. }
      { apply withinBounds_true_iff.
        pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
        cbn in Hsize.
        solve_addr. }
    }
    {
      unfold is_heap_address.
      apply withinBounds_true_iff.
      pose proof heap_valid.
      solve_addr.
    }
    {
      split; first done.
      apply withinBounds_true_iff.
      pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
      cbn in Hsize.
      solve_addr.
    }
    iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hslot & Hs)".
    iMod ("Hclose" with "[Hs Hres Hput]").
    { iNext. iApply ("Hput" $! Free). iFrame. }
    iModIntro.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (simpl) in "Hct0".
    (* GetB ct1 ca0. *)
    iInstr "Hcode".
    (* GetE ct2 ca0. *)
    iInstr "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct1. *)
    iInstr "Hcode".
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_base_ok ct3. *)
    iInstr "Hcode".
    (* Lt ct3 ct1 ct2. *)
    iInstr "Hcode".
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_nonempty ct3. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct2. *)
    iInstr "Hcode".
    replace (next <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    iApply "Hφ".
    iSplitL "Hslot Hroot Hfree Hheaders Hhistory".
    { iExists allocations. iFrame. done. }
    iFrame "Hcgp Hca0 Hcode".
    iExists p, g, b, e, a.
    iSplit.
    { iPureIntro. split; first done. exact Hbounds. }
    iFrame.
  Qed.

  Local Lemma allocator_free_prepare_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr)
    (wreq w0 w1 w2 w3 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1 in
    allocatorLayoutWf ->
    ↑Nallocator ⊆ E ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    ¬ allocator_free_in_prefix next wreq ->

    allocator_ctx ∗
    allocator_service_data next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wreq ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_service_data next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ wreq ∗
         codefrag pc_a code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_free_block_addr pc_a 10) ∗
         ct0 ↦ᵣ - ∗
         ct1 ↦ᵣ - ∗
         ct2 ↦ᵣ - ∗
         ct3 ↦ᵣ -
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout HE Hcont Hpc Hdisjoint Hrequest; subst code.
    iIntros "(#Hctx & Hdata & HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    iDestruct "Hdata" as (allocations)
      "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    destruct (is_cap wreq) eqn:Hreq_cap.
    + destruct wreq; cbn in Hreq_cap; try done.
      destruct sb; cbn in Hreq_cap; try done.
      rewrite (encodeWordType_correct_cap tag p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      (* GetTag ct3 ca0. *)
      iInstr "Hcode".
      (* Sub ct3 ct3 1. *)
      iInstr "Hcode".
      destruct tag.
      * rewrite /Z.b2z Z.sub_diag.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        (* Load ct0 cgp. *)
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iInv Nallocator as ">Hbody" "Hclose".
        iDestruct (allocator_inv_lookup heap_b with "Hbody") as (s) "[Hentry Hput]".
        {
          apply elem_of_heap_addresses.
          apply withinBounds_true_iff.
          pose proof heap_valid.
          solve_addr.
        }
        iDestruct (allocator_entry_free_token with "Hentry Hroot") as %->.
        iDestruct "Hentry" as "[Hs Hres]".
        iApply (wp_load_success_heap with "[$HPC $Hi $Hct0 $Hcgp $Hslot $Hs]"); try solve_pure.
        {
          eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
          { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
            unfold disjoint_from_shadow.
            rewrite !disjoint_list_cons in Hregions.
            cbn [union_list] in Hregions.
            set_solver. }
          { apply withinBounds_true_iff.
            pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
            cbn in Hsize.
            solve_addr. }
        }
        {
          unfold is_heap_address.
          apply withinBounds_true_iff.
          pose proof heap_valid.
          solve_addr.
        }
        {
          split; first done.
          apply withinBounds_true_iff.
          pose proof (@allocator_size_data MP layout Hlayout) as Hsize.
          cbn in Hsize.
          solve_addr.
        }
        iIntros "!> (HPC & Hct0 & Hi & Hcgp & Hslot & Hs)".
        iMod ("Hclose" with "[Hs Hres Hput]").
        { iNext. iApply ("Hput" $! Free). iFrame. }
        iModIntro.
        wp_pure.
        iSpecialize ("Hcode" with "Hi").
        iEval (simpl) in "Hct0".
        (* GetB ct1 ca0. *)
        iInstr "Hcode".
        (* GetE ct2 ca0. *)
        iInstr "Hcode".
        (* GetB ct3 ct0. *)
        iInstr "Hcode".
        (* Lt ct3 ct3 ct1. *)
        iInstr "Hcode".
        destruct (decide (heap_b < b)%a) as [Hbase|Hbase].
        ** replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
          (* Jnz .free_base_ok ct3. *)
          iInstr "Hcode".
          (* Lt ct3 ct1 ct2. *)
          iInstr "Hcode".
          destruct (decide (b < e)%a) as [Hnonempty|Hempty].
          {
            replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
            (* Jnz .free_nonempty ct3. *)
            iInstr "Hcode".
            (* GetA ct3 ct0. *)
            iInstr "Hcode".
            (* Lt ct3 ct3 ct2. *)
            iInstr "Hcode".
            destruct (decide (next < e)%a) as [Hpast|Hwithin].
            {
              replace (next <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
              (* Jnz .free_invalid ct3. *)
              iInstr "Hcode".
              iApply "Hφ". iFrame. done.
            }
            { exfalso. apply Hrequest.
              exists p, g, b, e, a. split; first reflexivity. solve_addr. }
          }
          replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_nonempty ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame. done.
        ** replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_base_ok ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame. done.
      * cbn.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        iApply "Hφ". iFrame. done.
    + assert (Hnoncap : WInt (encodeWordType wreq - encodeWordType wt_cap) ≠ WInt 0).
      {
        pose proof (encodeWordType_correct wreq wt_cap) as Hencode.
        intro Hzero.
        injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType wt_cap) by lia.
        destruct wreq; cbn in Hreq_cap, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hreq_cap, Hencode; try discriminate); contradiction.
      }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame. done.
  Qed.

  Context {layout_wf : allocatorLayoutWf}.

  (** Common call boundary for rejection. [P] carries the evidence for the
      particular rejection and is returned unchanged. Other client resources
      can be framed. *)



  Lemma allocator_memory_not_free_cell E a w :
    ↑Nallocator ⊆ E ->
    a ∈ heap_addresses ->
    allocator_ctx -∗
    a ↦ₐ w -∗
    free_cell_token a
    ={E}=∗
    False.
  Proof.
    iIntros (HE Ha) "#Hctx Hmem Hfree".
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup a with "Hbody") as (s) "[Hentry Hput]"; first done.
    iDestruct (allocator_entry_memory_live with "Hentry Hmem") as %Hlive.
    iDestruct (allocator_entry_free_token with "Hentry Hfree") as %Hfree.
    exfalso. congruence.
  Qed.

  Lemma allocator_range_free_contradiction E b e next a ws :
    ↑Nallocator ⊆ E ->
    a ∈ heap_addresses ->
    a ∈ finz.seq_between b e ->
    a ∈ finz.seq_between next heap_e ->
    length ws = length (finz.seq_between b e) ->
    allocator_ctx -∗
    [[b,e]] ↦ₐ [[ws]] -∗
    free_cells next heap_e
    ={E}=∗
    False.
  Proof.
    iIntros (HE Ha Hmem_in Hfree_in Hlen) "#Hctx Hmem Hfree".
    destruct (list_elem_of_lookup_1 _ _ Hmem_in) as [i Hi].
    assert (i < length ws) as Hlt by (rewrite Hlen; eapply lookup_lt_Some; eauto).
    destruct (lookup_lt_is_Some_2 ws i Hlt) as [w Hw].
    iDestruct (big_sepL2_lookup_acc with "Hmem") as "[Hcell Hmemclose]"; eauto.
    iDestruct (big_sepL_elem_of with "Hfree") as "Htoken"; eauto.
    iMod (allocator_memory_not_free_cell E a w HE Ha with "Hctx Hcell Htoken") as %[].
  Qed.

  Lemma allocator_owned_range_below_cursor E b e next ws :
    ↑Nallocator ⊆ E ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    (heap_b < next /\ next <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    allocator_ctx -∗
    [[b,e]] ↦ₐ [[ws]] -∗
    free_cells next heap_e
      ={E}=∗
      ⌜(e <= next)%a⌝ ∗
      [[b,e]] ↦ₐ [[ws]] ∗
      free_cells next heap_e.
  Proof.
    iIntros (HE Hb Hnext Hlen) "#Hctx Hmem Hfree".
    destruct (decide (e <= next)%a) as [Hbound|Hbad].
    { iModIntro. iFrame. iPureIntro. exact Hbound. }
    set (a := if decide (b < next)%a then next else b).
    assert (Ha_heap : a ∈ heap_addresses).
    { rewrite /heap_addresses elem_of_list_to_set elem_of_finz_seq_between.
      unfold a. destruct (decide (b < next)%a); solve_addr. }
    assert (Ha_mem : a ∈ finz.seq_between b e).
    { rewrite elem_of_finz_seq_between.
      unfold a. destruct (decide (b < next)%a); solve_addr. }
    assert (Ha_free : a ∈ finz.seq_between next heap_e).
    { rewrite elem_of_finz_seq_between.
      unfold a. destruct (decide (b < next)%a); solve_addr. }
    iMod (allocator_range_free_contradiction E b e next a ws HE Ha_heap Ha_mem Ha_free Hlen with "Hctx Hmem Hfree") as %[].
  Qed.

  Local Lemma allocator_free_reject_correct
    (E : coPset) (wreq wret : Word) (P : iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :
    (∀ next allocations,
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_history allocations -∗
      P -∗
      ⌜¬ allocator_free_valid next allocations wreq⌝) ->
    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    ⊢ (
       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       P ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
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
       P ∗
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
    intros Hreject_request HEheap HEservice.
    iIntros "(#Hctx & #Hservice & Hna & HP & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfreecode" "Hcode_cont".
    assert (Ha_eq : a_free = allocator_free_pcc_addr).
    { pose proof allocator_size_imports as Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *.
      solve_addr. }
    subst a_free.
    (* Check the capability and its bounds. *)
    assert (Hsplit : allocator_free_instrs =
      (allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1) ++
      concat (encodeInstrsW <$> drop 2 assembled_allocator_free)) by reflexivity.
    iEval (rewrite Hsplit) in "Hfreecode".
    focus_block_0 "Hfreecode" as "Hprepare_code" "Hfree_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_free_pcc_addr (allocator_free_pcc_addr ^+ length allocator_free_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      rewrite /allocator_code length_app in Hsize_code.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    iAssert ((P ∗
      allocator_service_data next ∗
      PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
        (allocator_free_block_addr allocator_free_pcc_addr 10) ∗
      cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
      ca0 ↦ᵣ wreq ∗
      ct0 ↦ᵣ - ∗
      ct1 ↦ᵣ - ∗
      ct2 ↦ᵣ - ∗
      ct3 ↦ᵣ - ∗
      ct4 ↦ᵣ - ∗
      ca2 ↦ᵣ - ∗
      codefrag allocator_free_pcc_addr allocator_free_instrs) -∗
      WP Seq (Instr Executable) @ E {{ φ }})%I
      with "[- HP Hdata HPC Hcgp Hca0 Hct0 Hct1 Hct2 Hct3 Hct4 Hca2 Hprepare_code Hfree_cont]" as "Hreject".
    { iIntros "(HP & Hdata & HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hfreecode)".
      iDestruct "Hct0" as (w0') "Hct0".
      iDestruct "Hct1" as (w1') "Hct1".
      iDestruct "Hct2" as (w2') "Hct2".
      iDestruct "Hct3" as (w3') "Hct3".
    (* The validity check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit6 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 10 assembled_allocator_free) ++
      (allocator_free_instrs_n 10 ++ allocator_free_instrs_n 11)) by reflexivity.
    iEval (rewrite Hsplit6) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_invalid Ha_invalid "Hinvalid_code" "Hfreecode_cont".
    assert (Haddr : a_invalid = allocator_free_block_addr allocator_free_pcc_addr 10).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_invalid.
    (* Mov ca0 0. *)
    iInstr "Hinvalid_code".
    iDestruct "Hca1" as (wca1) "Hca1".
    assert (Hstep : (allocator_free_pcc_addr ^+ 66)%a =
      (allocator_free_block_addr allocator_free_pcc_addr 10 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_INVALID. *)
    iInstr_lookup "Hinvalid_code" as "Hi" "Hinvalid_code".
    wp_instr.
    iApply (wp_move_success_z with "[$HPC $Hi $Hca1]"); try solve_pure.
    iIntros "!> (HPC & Hi & Hca1)". wp_pure.
    iSpecialize ("Hinvalid_code" with "Hi").
    iDestruct ("Hfreecode_cont" with "Hinvalid_code") as "Hfreecode".
    iEval (rewrite -Hsplit6) in "Hfreecode".
    (* Return to the caller and restore the service invariant. *)
    assert (Hsplit7 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 11 assembled_allocator_free) ++
      allocator_free_instrs_n 11) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret "Hret_code" "Hfreecode_cont".
    assert (Haddr : a_ret = allocator_free_block_addr allocator_free_pcc_addr 11).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_ret.
    assert (Hret : (allocator_free_block_addr allocator_free_pcc_addr 10 ^+ 2)%a =
      allocator_free_block_addr allocator_free_pcc_addr 11)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hret) in "HPC".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* Jalr cnull cra. *)
    iInstr "Hret_code".
    iDestruct ("Hfreecode_cont" with "Hret_code") as "Hfreecode".
    iEval (rewrite -Hsplit7) in "Hfreecode".
    iDestruct ("Hcode_cont" with "Hfreecode") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next. iFrame. }
    iApply "Hpost". iFrame "∗".
    }
    destruct (decide (allocator_free_in_prefix next wreq)) as [Hprefix|Hprefix].
    - iApply (allocator_free_prepare_valid_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
      iNext. iIntros "(Hdata & Hcgp & Hca0 & Hprepare_code & Hvalid)".
      iDestruct "Hvalid" as (p g b e a) "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      destruct Hvalid as [Heq Hbounds].
      iDestruct "Hdata" as (entries) "(%Hcursor & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
      iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
      iDestruct (Hreject_request next entries Hcursor Hchain with "Hhistory HP") as %Hinvalid.
      assert (Hmissing : ¬ allocator_has_bounds entries b e).
      { intros Hmember. apply Hinvalid. exists p,g,b,e,a. auto. }
      iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
      iEval (rewrite -Hsplit) in "Hfreecode".
      assert (Hsplit_search : allocator_free_instrs =
        concat (encodeInstrsW <$> take 2 assembled_allocator_free) ++
        (concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) ++
         concat (encodeInstrsW <$> drop 6 assembled_allocator_free))) by reflexivity.
      iEval (rewrite Hsplit_search) in "Hfreecode".
      focus_block_nochangePC 1 "Hfreecode" as a_search Ha_search "Hsearchcode" "Hsearch_cont".
      assert (Ha_search_eq : a_search = allocator_free_block_addr allocator_free_pcc_addr 2)
        by (unfold allocator_free_block_addr in *; solve_addr).
      subst a_search.
      iDestruct "Hct4" as (w4) "Hct4".
      iDestruct "Hca2" as (wa2) "Hca2".
      iApply (allocator_free_search_missing_spec with
        "[- $Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hsearchcode]"); eauto.
      iNext. iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hsearchcode & Hresult)".
      iDestruct "Hresult" as "(%Hmiss & HPC)".
      iAssert (allocator_service_data next) with "[Hslot Hroot Hfree Hheaders Hhistory]" as "Hdata".
      { iExists entries. iFrame. done. }
      iDestruct ("Hsearch_cont" with "Hsearchcode") as "Hfreecode".
      iEval (rewrite -Hsplit_search) in "Hfreecode".
      iApply "Hreject". iFrame.
    - iApply (allocator_free_prepare_invalid_spec with
        "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
      iNext. iIntros "(Hdata & Hcgp & Hca0 & Hprepare_code & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
      iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
      iEval (rewrite -Hsplit) in "Hfreecode".
      iApply "Hreject". iFrame.
  Qed.

  (** A strict subrange cannot be another allocation in the header chain.
      The original receipt suffices, whether its payload is live or freed. *)

  Lemma allocator_free_narrowed_spec
    (E : coPset) (p : Perm) (g : Locality)
    (b e : Addr) (reserved : Z) (b' e' a : Addr) (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :
    (b <= b' /\ b' < e' /\ e' <= e)%a ->
    (b', e') ≠ (b, e) ->
    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    ⊢ (
       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       (allocator_allocation b e reserved) ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ (WCap true p g b' e' a) ∗
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
       (allocator_allocation b e reserved) ∗
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
    intros Hbounds Hneq HEheap HEservice.
    eapply allocator_free_reject_correct; [|exact HEheap|exact HEservice].
    intros next allocations Hnext Hchain.
    iIntros "Hhistory #Hreceipt".
    iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt") as %Hlookup.
    assert (Horiginal : allocator_has_bounds allocations b e).
    { exists reserved. apply elem_of_list_to_map_2. exact Hlookup. }
    pose proof (allocator_chain_subrange_spec _ _ _ _ _ _ _
      Hchain Horiginal Hbounds Hneq) as Hmissing.
    iPureIntro. intros (p0 & g0 & b0 & e0 & a0 & Heq & Hprefix & Hmember).
    inversion Heq; subst. contradiction.
  Qed.

  (** A call with an invalid request leaves client memory untouched and returns
      [ALLOC_INVALID]. Other registers and resources can be framed. *)

  Lemma allocator_free_invalid_correct
    (E : coPset) (wreq wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    (∀ (next : Addr) (allocations : list allocator_header_entry),
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      ¬ allocator_free_valid next allocations wreq) ->
    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->

    ⊢ (
       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
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
    intros Hinvalid HEheap HEservice.
    assert (Hreject : ∀ next allocations,
      (heap_b < next /\ next <= heap_e)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_history allocations -∗
      emp -∗
      ⌜¬ allocator_free_valid next allocations wreq⌝).
    { intros next allocations Hnext Hchain. iIntros "_ _".
      iPureIntro. exact (Hinvalid next allocations Hnext Hchain). }
    pose proof (allocator_free_reject_correct E wreq wret emp φ
      Hreject HEheap HEservice) as Hcorrect.
    rewrite !left_id in Hcorrect.
    iApply Hcorrect.
  Qed.

  (** The receipt fixes both original bounds; ownership of every payload cell
      witnesses liveness. A successful call relinquishes that memory and
      returns one reclaim token per cell. Permissions and cursor may vary. *)

  Lemma allocator_free_valid_correct
    (E : coPset) (p : Perm) (g : Locality) (b e a : Addr) (reserved : Z)
    (ws : list Word) (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->

    ⊢ (

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_allocation b e reserved ∗

       (* Initial register file. *)
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WCap true p g b e a ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       [[b, e]] ↦ₐ [[ws]] ∗

       ▷ (na_own cerise_nais E ∗
          allocator_allocation b e reserved ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
          cra ↦ᵣ wret ∗
          ca0 ↦ᵣ WInt 0 ∗
          ca1 ↦ᵣ WInt ALLOC_OK ∗
          ca2 ↦ᵣ - ∗
          ct0 ↦ᵣ - ∗
          ct1 ↦ᵣ - ∗
          ct2 ↦ᵣ - ∗
          ct3 ↦ᵣ - ∗
          ct4 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗
          cnull ↦ᵣ WInt 0 ∗
          allocator_reclaimed b e

          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.
  Proof.
    intros HEheap HEservice Hbounds Hlen.
    iIntros "(#Hctx & #Hservice & Hna & #Hreceipt & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hmem & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iDestruct "Hdata" as (allocations) "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    (* Use ownership of the range to show that it lies below the bump cursor. *)
    iMod (allocator_owned_range_below_cursor E b e next ws HEheap Hbounds Hnext Hlen
      with "Hctx Hmem Hfree") as "(%Hend & Hmem & Hfree)".
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree Hheaders Hhistory]" as "Hdata".
    { iExists allocations. iFrame. done. }
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfreecode" "Hcode_cont".
    assert (Ha_eq : a_free = allocator_free_pcc_addr).
    { pose proof allocator_size_imports as Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *. solve_addr. }
    subst a_free.
    (* Check the capability and its bounds. *)
    assert (Hsplit : allocator_free_instrs =
      (allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1) ++
      concat (encodeInstrsW <$> drop 2 assembled_allocator_free)) by reflexivity.
    iEval (rewrite Hsplit) in "Hfreecode".
    focus_block_0 "Hfreecode" as "Hprepare_code" "Hfree_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_free_pcc_addr (allocator_free_pcc_addr ^+ length allocator_free_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      rewrite /allocator_code length_app in Hsize_code.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    assert (Hrequest : allocator_free_in_prefix next (WCap true p g b e a)).
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    iApply (allocator_free_prepare_valid_spec with
      "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
    iNext. iIntros "(Hdata & Hcgp & Hca0 & Hprepare_code & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0)
      "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. inversion Heq; subst; clear Heq.
    iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
    iEval (rewrite -Hsplit) in "Hfreecode".
    (* Follow authentic headers until both original bounds match. *)
    iDestruct "Hdata" as (entries) "(%Hcursor & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt") as %Hlookup.
    assert (Hmember : allocator_has_bounds entries b0 e0).
    { exists reserved. apply elem_of_list_to_map_2. exact Hlookup. }
    assert (Hsplit_search : allocator_free_instrs =
      concat (encodeInstrsW <$> take 2 assembled_allocator_free) ++
      (concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) ++
       concat (encodeInstrsW <$> drop 6 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit_search) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_search Ha_search "Hsearchcode" "Hsearch_cont".
    assert (Ha_search_eq : a_search = allocator_free_block_addr allocator_free_pcc_addr 2)
      by (unfold allocator_free_block_addr in *; solve_addr).
    subst a_search.
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hca2" as (wa2) "Hca2".
    iApply (allocator_free_search_found_spec with
      "[- $Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hsearchcode]"); eauto.
    iNext. iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hsearchcode & Hresult)".
    iDestruct "Hresult" as "(%Hfound & HPC)".
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree Hheaders Hhistory]" as "Hdata".
    { iExists entries. iFrame. done. }
    iDestruct ("Hsearch_cont" with "Hsearchcode") as "Hfreecode".
    iEval (rewrite -Hsplit_search) in "Hfreecode".
    iDestruct "Hct3" as (w3') "Hct3".
    (* Fetch the shadow capability and translate the range to free. *)
    assert (Hsplit2 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 6 assembled_allocator_free) ++
      (allocator_free_instrs_n 6 ++
       concat (encodeInstrsW <$> drop 7 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit2) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_fetch Ha_fetch
      "Hfetch_code" "Hfreecode_cont".
    assert (Haddr : a_fetch = allocator_free_block_addr allocator_free_pcc_addr 6).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_fetch.
    pose proof allocator_size_imports as Himports_size.
    iDestruct (region_pointsto_single with "Himports") as (v)
      "[Himport %Hentry]"; first exact Himports_size.
    cbn in Hentry. inversion Hentry; subst v.
    assert (Hfetch_eq : allocator_free_instrs_n 6 =
      fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
      by reflexivity.
    iEval (rewrite Hfetch_eq) in "Hfetch_code".
    iDestruct "Hctp" as (wctp) "Hctp".
    iDestruct "Hca2" as (wca2) "Hca2".
    assert (Himpaddr : (allocator_pcc_b ^+ allocator_shadow_import_off)%a =
      allocator_pcc_b) by (unfold allocator_shadow_import_off; solve_addr).
    iEval (rewrite -Himpaddr) in "Himport".
    iApply (allocator_fetch_spec with
      "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Himport]").
    { reflexivity. }
    { rewrite -Hfetch_eq; assumption. }
    { apply withinBounds_true_iff; solve_addr. }
    { exact Hdisjoint. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
      destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
      exfalso. unfold is_heap_address in Hheap.
      apply withinBounds_true_iff in Hheap;
      pose proof heap_shadow_disjoint as Hd;
      rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
      apply (Hd shadow_b); apply elem_of_finz_seq_between; try exact Hheap;
      pose proof shadow_valid; solve_addr. }
    { discriminate. }
    { discriminate. }
    { discriminate. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hfetch_code)".
    iEval (cbn) in "Hctp".
    iEval (rewrite Himpaddr) in "Himport".
    iAssert ([[allocator_pcc_b,allocator_code_b]] ↦ₐ [[allocator_imports]])%I
      with "[Himport]" as "Himports".
    { rewrite /allocator_imports /region_pointsto
        (finz_seq_between_singleton allocator_pcc_b allocator_code_b Himports_size) /=.
      iFrame. }
    iEval (rewrite -Hfetch_eq) in "Hfetch_code".
    iDestruct ("Hfreecode_cont" with "Hfetch_code") as "Hfreecode".
    iEval (rewrite -Hsplit2) in "Hfreecode".
    assert (Hsplit3 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_free) ++
      (allocator_free_instrs_n 7 ++
       concat (encodeInstrsW <$> drop 8 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit3) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_translate Ha_translate
      "Htranslate_code" "Hfreecode_cont".
    assert (Haddr3 : a_translate =
      allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_translate.
    assert (Hpc3 : (allocator_free_block_addr allocator_free_pcc_addr 6 ^+
      length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
      allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hpc3) in "HPC".
    pose (sb := (shadow_b ^+ (b0 - heap_b))%a).
    assert (Hsb : (shadow_b + (b0 - heap_b))%a = Some sb).
    { unfold sb. pose proof heap_shadow_same_size. solve_addr. }
    assert (Hbtranslate : heap_to_shadow b0 = Some sb).
    { rewrite allocator_translation_affine /translate_region.
      assert (Hbheap : withinBounds heap_b heap_e b0 = true)
        by (apply withinBounds_true_iff; solve_addr).
      rewrite Hbheap. exact Hsb. }
    destruct ws as [|v ws].
    { exfalso. rewrite finz_seq_between_length /finz.dist /= in Hlen. solve_addr. }
    assert (Hbnext : (b0 + 1)%a = Some (b0 ^+ 1)%a) by solve_addr.
    assert (Hbnext_e : (b0 ^+ 1 <= e0)%a) by solve_addr.
    iEval (rewrite (region_pointsto_cons _ _ _ _ _ Hbnext Hbnext_e)) in "Hmem".
    iDestruct "Hmem" as "[Hb Hmemtail]".
    iApply (allocator_free_shadow_check_spec _ _ _ _ _ _ _ sb ShadowLive with
      "[- $Hctx $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code]");
      try assumption; try solve_addr.
    iSplitL "Hb". { iExists v. iFrame. }
    iNext. iIntros "(Hb & Hct0 & Hct1 & Hct2 & Hctp & Htranslate_code & HPC & Hct3 & Hca2)".
    iDestruct "Hb" as (v') "Hb".
    iAssert ([[b0,e0]] ↦ₐ [[v' :: ws]])%I with "[Hb Hmemtail]" as "Hmem".
    { rewrite (region_pointsto_cons _ _ _ _ _ Hbnext Hbnext_e). iFrame. }
    iDestruct ("Hfreecode_cont" with "Htranslate_code") as "Hfreecode".
    iEval (rewrite -Hsplit3) in "Hfreecode".
    (* Set the shadow bits and exchange memory ownership for reclaim tokens. *)
    assert (Hsplit4 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 8 assembled_allocator_free) ++
      (allocator_free_instrs_n 8 ++
       concat (encodeInstrsW <$> drop 9 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit4) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_paint Ha_paint
      "Hpaint_code" "Hfreecode_cont".
    assert (Haddr4 : a_paint =
      allocator_free_block_addr allocator_free_pcc_addr 8).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_paint.
    pose (se := (shadow_b ^+ (e0 - heap_b))%a).
    assert (Hshadow : (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a).
    { pose proof heap_shadow_same_size. unfold sb, se. solve_addr. }
    assert (Hlen_shadow : (se - sb = e0 - b0)%Z).
    { unfold sb, se. pose proof heap_shadow_same_size. solve_addr. }
    assert (Htranslation : ∀ x, (b0 <= x /\ x < e0)%a ->
      heap_to_shadow x = Some (sb ^+ (x - b0))%a).
    { intros x Hx. rewrite allocator_translation_affine.
      unfold translate_region.
      assert (Hxheap : withinBounds heap_b heap_e x = true).
      { apply withinBounds_true_iff. solve_addr. }
      rewrite Hxheap. unfold sb. pose proof heap_shadow_same_size. solve_addr. }
    assert (Hpaint_eq : allocator_free_instrs_n 8 =
      allocator_paint_instrs ctp ca2 ShadowQuarantined) by reflexivity.
    iEval (rewrite Hpaint_eq) in "Hpaint_code".
    iApply (allocator_paint_spec ShadowQuarantined ctp ca2 E RX Global
      allocator_pcc_b allocator_pcc_e
      (allocator_free_block_addr allocator_free_pcc_addr 8) b0 e0 sb se (v' :: ws)
      with "[- $Hctx $HPC $Hctp $Hca2 $Hpaint_code $Hmem]").
    { reflexivity. }
    { rewrite -Hpaint_eq; assumption. }
    { exact Hdisjoint. }
    { exact HEheap. }
    { solve_addr. }
    { exact Hshadow. }
    { exact Hlen_shadow. }
    { exact Htranslation. }
    { vm_compute;
      constructor; [rewrite !elem_of_cons elem_of_nil; intuition congruence|];
      constructor; [rewrite !elem_of_cons elem_of_nil; intuition congruence|];
      constructor; [rewrite !elem_of_cons elem_of_nil; intuition congruence|];
      constructor; [apply not_elem_of_nil|];
      constructor. }
    iNext. iIntros "(HPC & Hctp & Hca2 & Hreclaimed & Hpaint_code)".
    iEval (rewrite -Hpaint_eq) in "Hpaint_code".
    iDestruct ("Hfreecode_cont" with "Hpaint_code") as "Hfreecode".
    iEval (rewrite -Hsplit4) in "Hfreecode".
    (* Set ALLOC_OK, then return and restore the service invariant. *)
    assert (Hsplit5 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 9 assembled_allocator_free) ++
      (allocator_free_instrs_n 9 ++
       concat (encodeInstrsW <$> drop 10 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit5) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_success Ha_success
      "Hsuccess_code" "Hfreecode_cont".
    assert (Haddr5 : a_success =
      allocator_free_block_addr allocator_free_pcc_addr 9).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_success.
    assert (Hoff4 : allocator_free_block_addr allocator_free_pcc_addr 8 =
      (allocator_free_pcc_addr ^+ 58)%a) by reflexivity.
    assert (Hoff5 : allocator_free_block_addr allocator_free_pcc_addr 9 =
      (allocator_free_pcc_addr ^+ 62)%a) by reflexivity.
    assert (Hlenpaint : length (allocator_paint_instrs ctp ca2 ShadowQuarantined) = 4)
      by reflexivity.
    assert (Hpc5 : (allocator_free_block_addr allocator_free_pcc_addr 8 ^+
       length (allocator_paint_instrs ctp ca2 ShadowQuarantined))%a =
       allocator_free_block_addr allocator_free_pcc_addr 9).
    { clear -Hoff4 Hoff5 Hlenpaint.
      rewrite Hoff4 Hoff5 Hlenpaint.
      rewrite incr_addr_opt_add_twice.
      { replace (58 + 4)%Z with 62%Z by lia; reflexivity. }
      all: lia. }
    iEval (rewrite Hpc5) in "HPC".
    iDestruct "Hca1" as (wca1) "Hca1".
    iApply (allocator_free_success_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hsuccess_code]"); eauto.
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hsuccess_code)".
    iDestruct ("Hfreecode_cont" with "Hsuccess_code") as "Hfreecode".
    iEval (rewrite -Hsplit5) in "Hfreecode".
    assert (Hsplit7 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 11 assembled_allocator_free) ++
      allocator_free_instrs_n 11) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret
      "Hret_code" "Hfreecode_cont".
    assert (Haddr7 : a_ret =
      allocator_free_block_addr allocator_free_pcc_addr 11).
    { unfold allocator_free_block_addr. clear -Ha_ret.
      cbn [take concat fmap] in *. solve_addr. }
    subst a_ret.
    assert (Hret_eq : allocator_free_instrs_n 11 =
      encodeInstrsW [Jalr cnull cra]) by reflexivity.
    iEval (rewrite Hret_eq) in "Hret_code".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    iApply (allocator_return_spec with
      "[- $HPC $Hcra $Hcnull $Hret_code]"); eauto.
    iNext. iIntros "(HPC & Hcra & Hcnull & Hret_code)".
    iEval (rewrite -Hret_eq) in "Hret_code".
    iDestruct ("Hfreecode_cont" with "Hret_code") as "Hfreecode".
    iEval (rewrite -Hsplit7) in "Hfreecode".
    iDestruct ("Hcode_cont" with "Hfreecode") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next. iFrame. }
    iApply "Hpost". iFrame "Hreceipt ∗".
  Qed.

  (** A still-tagged alias with exact original bounds reaches the shadow
      check and is rejected. Only the first payload cell's reclaim token is
      needed to justify that observation; the remaining tokens can be framed. *)

  Lemma allocator_free_repeated_spec
    (E : coPset) (p : Perm) (g : Locality)
    (b e a : Addr) (reserved : Z) (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :
    ↑Nallocator ⊆ E ->
    ↑Nallocator_service ⊆ E ->
    ⊢ (
       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       allocator_allocation b e reserved ∗
       PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e
         allocator_free_pcc_addr ∗
       cgp ↦ᵣ WCap true RW Global
         allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ (WCap true p g b e a) ∗
       ca1 ↦ᵣ - ∗
       ca2 ↦ᵣ - ∗
       ct0 ↦ᵣ - ∗
       ct1 ↦ᵣ - ∗
       ct2 ↦ᵣ - ∗
       ct3 ↦ᵣ - ∗
       ct4 ↦ᵣ - ∗
       ctp ↦ᵣ - ∗
       cnull ↦ᵣ - ∗
       reclaim_token b ∗
       ▷ (na_own cerise_nais E ∗
          allocator_allocation b e reserved ∗
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
          cnull ↦ᵣ WInt 0 ∗
          reclaim_token b
          -∗ WP Seq (Instr Executable) @ E {{ φ }})
       -∗ WP Seq (Instr Executable) @ E {{ φ }})%I.

  Proof.
    intros HEheap HEservice.
    iIntros "(#Hctx & #Hservice & Hna & #Hreceipt & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hreclaim & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iDestruct "Hdata" as (allocations) "(%Hnext & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hinitial_chain.
    iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt") as %Hinitial_lookup.
    assert (Hinitial_member : (b, (e, reserved)) ∈ allocations).
    { apply elem_of_list_to_map_2. exact Hinitial_lookup. }
    pose proof (allocator_chain_member_bounds _ _ _ _ _ _ Hinitial_chain Hinitial_member) as Hentry_bounds.
    assert (Hbounds : (heap_b < b /\ b < e /\ e <= heap_e)%a) by solve_addr.
    assert (Hend : (e <= next)%a) by solve_addr.
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree Hheaders Hhistory]" as "Hdata".
    { iExists allocations. iFrame. done. }
    iEval (rewrite /allocator_code) in "Hcode".
    focus_block_nochangePC 1 "Hcode" as a_free Ha_free "Hfreecode" "Hcode_cont".
    assert (Ha_eq : a_free = allocator_free_pcc_addr).
    { pose proof allocator_size_imports as Himports_size.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *. solve_addr. }
    subst a_free.
    (* Check the capability and its bounds. *)
    assert (Hsplit : allocator_free_instrs =
      (allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1) ++
      concat (encodeInstrsW <$> drop 2 assembled_allocator_free)) by reflexivity.
    iEval (rewrite Hsplit) in "Hfreecode".
    focus_block_0 "Hfreecode" as "Hprepare_code" "Hfree_cont".
    assert (Hpc : SubBounds allocator_pcc_b allocator_pcc_e
      allocator_free_pcc_addr (allocator_free_pcc_addr ^+ length allocator_free_instrs)%a).
    { pose proof allocator_size_code as Hsize_code.
      rewrite /allocator_code length_app in Hsize_code.
      unfold allocator_free_pcc_addr, allocator_free_pcc_off in *.
      solve_addr. }
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    iDestruct "Hct0" as (w0) "Hct0".
    iDestruct "Hct1" as (w1) "Hct1".
    iDestruct "Hct2" as (w2) "Hct2".
    iDestruct "Hct3" as (w3) "Hct3".
    assert (Hrequest : allocator_free_in_prefix next (WCap true p g b e a)).
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    iApply (allocator_free_prepare_valid_spec with
      "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
    iNext. iIntros "(Hdata & Hcgp & Hca0 & Hprepare_code & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0)
      "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. inversion Heq; subst; clear Heq.
    iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
    iEval (rewrite -Hsplit) in "Hfreecode".
    (* Follow authentic headers until both original bounds match. *)
    iDestruct "Hdata" as (entries) "(%Hcursor & Hslot & Hroot & Hfree & Hheaders & Hhistory)".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt") as %Hlookup.
    assert (Hmember : allocator_has_bounds entries b0 e0).
    { exists reserved. apply elem_of_list_to_map_2. exact Hlookup. }
    assert (Hsplit_search : allocator_free_instrs =
      concat (encodeInstrsW <$> take 2 assembled_allocator_free) ++
      (concat (encodeInstrsW <$> take 4 (drop 2 assembled_allocator_free)) ++
       concat (encodeInstrsW <$> drop 6 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit_search) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_search Ha_search "Hsearchcode" "Hsearch_cont".
    assert (Ha_search_eq : a_search = allocator_free_block_addr allocator_free_pcc_addr 2)
      by (unfold allocator_free_block_addr in *; solve_addr).
    subst a_search.
    iDestruct "Hct4" as (w4) "Hct4".
    iDestruct "Hca2" as (wa2) "Hca2".
    iApply (allocator_free_search_found_spec with
      "[- $Hheaders $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hsearchcode]"); eauto.
    iNext. iIntros "(Hheaders & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hsearchcode & Hresult)".
    iDestruct "Hresult" as "(%Hfound & HPC)".
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree Hheaders Hhistory]" as "Hdata".
    { iExists entries. iFrame. done. }
    iDestruct ("Hsearch_cont" with "Hsearchcode") as "Hfreecode".
    iEval (rewrite -Hsplit_search) in "Hfreecode".
    iDestruct "Hct3" as (w3') "Hct3".
    (* Fetch the shadow capability and translate the range to free. *)
    assert (Hsplit2 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 6 assembled_allocator_free) ++
      (allocator_free_instrs_n 6 ++
       concat (encodeInstrsW <$> drop 7 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit2) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_fetch Ha_fetch
      "Hfetch_code" "Hfreecode_cont".
    assert (Haddr : a_fetch = allocator_free_block_addr allocator_free_pcc_addr 6).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_fetch.
    pose proof allocator_size_imports as Himports_size.
    iDestruct (region_pointsto_single with "Himports") as (v)
      "[Himport %Hentry]"; first exact Himports_size.
    cbn in Hentry. inversion Hentry; subst v.
    assert (Hfetch_eq : allocator_free_instrs_n 6 =
      fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2)
      by reflexivity.
    iEval (rewrite Hfetch_eq) in "Hfetch_code".
    iDestruct "Hctp" as (wctp) "Hctp".
    iDestruct "Hca2" as (wca2) "Hca2".
    assert (Himpaddr : (allocator_pcc_b ^+ allocator_shadow_import_off)%a =
      allocator_pcc_b) by (unfold allocator_shadow_import_off; solve_addr).
    iEval (rewrite -Himpaddr) in "Himport".
    iApply (allocator_fetch_spec with
      "[- $HPC $Hctp $Hct3 $Hca2 $Hfetch_code $Himport]").
    { reflexivity. }
    { rewrite -Hfetch_eq; assumption. }
    { apply withinBounds_true_iff; solve_addr. }
    { exact Hdisjoint. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
      destruct (is_heap_address shadow_b) eqn:Hheap; last reflexivity.
      exfalso. unfold is_heap_address in Hheap.
      apply withinBounds_true_iff in Hheap;
      pose proof heap_shadow_disjoint as Hd;
      rewrite /disjoint_from_shadow elem_of_disjoint in Hd;
      apply (Hd shadow_b); apply elem_of_finz_seq_between; try exact Hheap;
      pose proof shadow_valid; solve_addr. }
    { discriminate. }
    { discriminate. }
    { discriminate. }
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Himport & Hfetch_code)".
    iEval (cbn) in "Hctp".
    iEval (rewrite Himpaddr) in "Himport".
    iAssert ([[allocator_pcc_b,allocator_code_b]] ↦ₐ [[allocator_imports]])%I
      with "[Himport]" as "Himports".
    { rewrite /allocator_imports /region_pointsto
        (finz_seq_between_singleton allocator_pcc_b allocator_code_b Himports_size) /=.
      iFrame. }
    iEval (rewrite -Hfetch_eq) in "Hfetch_code".
    iDestruct ("Hfreecode_cont" with "Hfetch_code") as "Hfreecode".
    iEval (rewrite -Hsplit2) in "Hfreecode".
    assert (Hsplit3 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_free) ++
      (allocator_free_instrs_n 7 ++
       concat (encodeInstrsW <$> drop 8 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit3) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_translate Ha_translate
      "Htranslate_code" "Hfreecode_cont".
    assert (Haddr3 : a_translate =
      allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_translate.
    assert (Hpc3 : (allocator_free_block_addr allocator_free_pcc_addr 6 ^+
      length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
      allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hpc3) in "HPC".
    pose (sb := (shadow_b ^+ (b0 - heap_b))%a).
    assert (Hsb : (shadow_b + (b0 - heap_b))%a = Some sb).
    { unfold sb. pose proof heap_shadow_same_size. solve_addr. }
    assert (Hbtranslate : heap_to_shadow b0 = Some sb).
    { rewrite allocator_translation_affine /translate_region.
      assert (Hbheap : withinBounds heap_b heap_e b0 = true)
        by (apply withinBounds_true_iff; solve_addr).
      rewrite Hbheap. exact Hsb. }
    iApply (allocator_free_shadow_check_spec _ _ _ _ _ _ _ sb ShadowQuarantined with
      "[- $Hctx $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code $Hreclaim]");
      try assumption; try solve_addr.
    iNext. iIntros "(Hreclaim & Hct0 & Hct1 & Hct2 & Hctp & Htranslate_code & HPC & Hct3 & Hca2)".
    iDestruct ("Hfreecode_cont" with "Htranslate_code") as "Hfreecode".
    iEval (rewrite -Hsplit3) in "Hfreecode".
    (* The validity check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit6 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 10 assembled_allocator_free) ++
      (allocator_free_instrs_n 10 ++ allocator_free_instrs_n 11)) by reflexivity.
    iEval (rewrite Hsplit6) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_invalid Ha_invalid "Hinvalid_code" "Hfreecode_cont".
    assert (Haddr : a_invalid = allocator_free_block_addr allocator_free_pcc_addr 10).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_invalid.
    (* Mov ca0 0. *)
    iInstr "Hinvalid_code".
    iDestruct "Hca1" as (wca1) "Hca1".
    assert (Hstep : (allocator_free_pcc_addr ^+ 66)%a =
      (allocator_free_block_addr allocator_free_pcc_addr 10 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_INVALID. *)
    iInstr_lookup "Hinvalid_code" as "Hi" "Hinvalid_code".
    wp_instr.
    iApply (wp_move_success_z with "[$HPC $Hi $Hca1]"); try solve_pure.
    iIntros "!> (HPC & Hi & Hca1)". wp_pure.
    iSpecialize ("Hinvalid_code" with "Hi").
    iDestruct ("Hfreecode_cont" with "Hinvalid_code") as "Hfreecode".
    iEval (rewrite -Hsplit6) in "Hfreecode".
    (* Return to the caller and restore the service invariant. *)
    assert (Hsplit7 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 11 assembled_allocator_free) ++
      allocator_free_instrs_n 11) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret "Hret_code" "Hfreecode_cont".
    assert (Haddr : a_ret = allocator_free_block_addr allocator_free_pcc_addr 11).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_ret.
    assert (Hret : (allocator_free_block_addr allocator_free_pcc_addr 10 ^+ 2)%a =
      allocator_free_block_addr allocator_free_pcc_addr 11)
      by (clear -H Hpc; unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hret) in "HPC".
    iDestruct "Hcnull" as (wnull) "Hcnull".
    (* Jalr cnull cra. *)
    iInstr "Hret_code".
    iDestruct ("Hfreecode_cont" with "Hret_code") as "Hfreecode".
    iEval (rewrite -Hsplit7) in "Hfreecode".
    iDestruct ("Hcode_cont" with "Hfreecode") as "Hcode".
    iEval (rewrite -/allocator_code) in "Hcode".
    iMod ("Hclose" with "[Himports Hcode Hdata Hna]") as "Hna".
    { iSplitR "Hna"; last iFrame.
      iNext. iSplitL "Himports Hcode"; first iFrame.
      iExists next. iFrame. }
    iApply "Hpost". iFrame "Hreceipt ∗".
  Qed.

End AllocatorFreeTraversal.
