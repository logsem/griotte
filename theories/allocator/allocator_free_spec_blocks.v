From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_header_spec.

(** The block specifications of [free]: one lemma per block of the assembled
    code, the revoker store, and the shadow-store permissions of the paint
    and the unpaint. The top-level specifications are in
    [allocator_free_spec]. *)

(** Address of an assembled block relative to the entry point. *)

Definition allocator_free_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_free)))%a.

Global Instance allocator_free_in_prefix_dec {MP : MachineParameters} next w :
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
    {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.

  (** The revoker store: the sweep kills [ι], whose payload is quarantined.
      It reads the whole register file, which must hold no word with authority
      over [ι]. The shadow cursor is then rewound to the payload base for the
      unpaint. *)

  Lemma allocator_free_revoke_spec
    (E : coPset) (pc_b pc_e pc_a b e sb se : Addr) (ι : AId) (regs : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 11 in
    let code := allocator_free_instrs_n 11 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (se + (b - e))%a = Some sb ->
    dom regs = all_registers_s ∖ {[PC; ct1; ct2; ct3; ct4; ctp; ca2]} ->
    (∀ x lv, x ≠ cnull -> regs !! x = Some lv ->
       has_authority lv.(lw) -> lv.(lprov) ≠ Some ι) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ allocator_revoker_cap ∗
    ct4 ↦ᵣ WInt 0 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
    ca2 ↦ᵣ WInt 0 ∗
    ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
    revoke_pre ι ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 12) ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt e ∗
         ct3 ↦ᵣ allocator_revoker_cap ∗
         ct4 ↦ᵣ WInt (b - e) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
         revoke_post ι ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hsb Hdom Hclean; subst start code.
    iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hpre & Hcode & Hφ)".
    codefrag_facts "Hcode".
    pose proof (@allocator_revoker_size MP layout Hlayout) as Hrev.
    assert (Hnone : ∀ r, r ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName) ->
      regs !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }
    (* Store ct3 0. *)
    unfold lword_of_word.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    (* Assemble the whole register file. *)
    iDestruct (big_sepM_insert with "[$Hregs $Hca2]") as "Hregs";
      first (apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hctp]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct4]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct3]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct2]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct1]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iApply (wp_store_revoker _ RX Global pc_b pc_e (allocator_free_block_addr pc_a 11) None
              (allocator_free_block_addr pc_a 11 ^+ 1)%a _ _ ct3 (inl 0%Z) 0 RW Global
              revoker_addr (revoker_addr ^+ 1)%a revoker_addr {[ι]}
      with "[$Hi $Hregs Hpre]").
    { cbn. apply decode_encode_instrW_inv. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { by simplify_map_eq. }
    { intros x.
      destruct (decide (x ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName))) as [Hx|Hx].
      { rewrite !elem_of_union !elem_of_singleton in Hx.
        destruct_or! Hx; subst x; by simplify_map_eq. }
      rewrite !lookup_insert_ne; [|set_solver..].
      apply elem_of_dom. rewrite Hdom. apply elem_of_difference.
      split; [apply all_registers_s_correct|done]. }
    { split_and!; [by simplify_map_eq | by rewrite finz_add_0 | done |].
      apply withinBounds_true_iff. solve_addr. }
    { unfold allocator_free_block_addr in *. solve_addr. }
    { intros x lv ι' bv Hx Hlookup Htag Hbase Hprov.
      rewrite not_elem_of_singleton. intros ->.
      destruct (decide (x ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName))) as [Hin|Hin].
      { rewrite !elem_of_union !elem_of_singleton in Hin.
        destruct_or! Hin; subst x; simplify_map_eq; done. }
      do 7 (rewrite lookup_insert_ne in Hlookup; last set_solver).
      by apply (Hclean x lv Hx Hlookup); [split; [|exists bv]|]. }
    { by rewrite big_sepS_singleton. }
    iNext. iIntros "(Hi & Hregs & Hpost)".
    rewrite big_sepS_singleton insert_insert_eq.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Take the registers back. *)
    iDestruct (big_sepM_insert with "Hregs") as "[HPC Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct1 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct2 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct3 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct4 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hctp Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca2 Hregs]";
      first (apply Hnone; set_solver).
    assert (Hstep : (pc_a ^+ 74)%a = (allocator_free_block_addr pc_a 11 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite -Hstep Hstep) in "HPC".
    (* Sub ct4 ct1 ct2. *)
    iInstr "Hcode".
    (* Lea ctp ct4. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    assert (Hnext : (allocator_free_block_addr pc_a 11 ^+ 4)%a =
      allocator_free_block_addr pc_a 12)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hnext) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  (** The shadow-store permissions of the paint and of the unpaint. *)

  Lemma allocator_free_paint_ok ι b e :
    allocator_paint_ok (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι)) b e.
  Proof.
    intros a Rs Cs _. iIntros "HR HC [Htok Hc]".
    iDestruct (reg_lookup_own with "HR Htok") as %(b1 & e1 & γ & HRι).
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. right. by exists ι, (b1, e1, γ, APainting).
  Qed.

  Lemma allocator_free_unpaint_ok b e :
    allocator_paint_ok emp (λ a, addr_alloc a Unclaimed) b e.
  Proof.
    intros a Rs Cs _. iIntros "_ HC [_ Hc]".
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. by left.
  Qed.

  (** At the search loop, [allocations] is the unvisited suffix. The visited
      prefix is framed using [allocator_headers_app_spec], so unfolding one
      list node supplies exactly the header read by block 4. Blocks 3 and 5
      implement the loop guard and the advance to the tail, respectively. *)

  Lemma allocator_free_search_loop_outcomes_aux
    (E : coPset) (pc_b pc_e pc_a next h b e : Addr)
    (allocations : list allocator_header_entry) (w3 wa2 : LWord)
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
            PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 14)
          )
        )
        -∗ WP Seq (Instr Executable) @ E {{ φ }}
      )
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow Hrange; subst start code.
    revert h w3 wa2 Hrange.
    induction allocations as [| [ [ [base finish] reserved] ι0] allocations IH]; intros h w3 wa2 Hrange.
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
      assert (Hinvalid : (allocator_free_block_addr pc_a 3 ^+ 57)%a = allocator_free_block_addr pc_a 14) by (unfold allocator_free_block_addr; solve_addr).
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
    unfold lword_of_word.
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
    iEval (rewrite /lload_word /lift_word /=) in "Hca2".
    (* GetA ct3 ct4. *)
    iInstr "Hcode".
    (* Add ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct1. *)
    iInstr "Hcode".
    destruct (decide (base = b)) as [->|Hbase_ne].
    + replace (h + 3 - b)%Z with 0%Z by solve_addr.
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
        exists reserved, ι0.
        by left.
      * assert (Hneq : WInt (finish - e) ≠ WInt 0) by (intros Heq; injection Heq as Heq; apply Hend_ne; solve_addr).
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        iDestruct (allocator_headers_chain_spec with "Htail") as %Hchain.
        assert (Hmiss : ¬ allocator_has_bounds ((b, finish, reserved, ι0) :: allocations) b e).
        {
          intros (r & ι' & Hin).
          apply elem_of_cons in Hin as [Heq|Hin].
          - inversion Heq.
            congruence.
          - pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hin).
            solve_addr.
        }
        assert (Hinvalid : (allocator_free_block_addr pc_a 3 ^+ 57)%a = allocator_free_block_addr pc_a 14) by (unfold allocator_free_block_addr; solve_addr).
        iEval (rewrite Hinvalid) in "HPC".
        iApply "Hφ".
        iFrame.
        iSplit; first done.
        iRight.
        iFrame.
        done.
    + assert (Hneq : WInt (h + 3 - b) ≠ WInt 0) by (intros Heq; injection Heq as Heq; apply Hbase_ne; solve_addr).
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
        destruct Hfound as (r & ι' & Hin).
        exists r, ι'. by right.
      * iRight.
        iFrame.
        iPureIntro.
        intros (r & ι' & Hin).
        apply elem_of_cons in Hin as [Heq|Hin].
        { inversion Heq; congruence. }
        apply Hmiss.
        exists r, ι'.
        exact Hin.
  Qed.

  (** Full traversal also executes block 2, which rederives the first header
      from the heap root. No payload ownership is needed to identify a block. *)

  Lemma allocator_free_search_outcomes_aux
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : LWord)
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
            PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 14)
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

  Lemma allocator_free_search_found_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : LWord)
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
        PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 6)
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
    - iApply "Hφ". iFrame.
    - exfalso. apply Hmiss. exact Hout.
  Qed.

  Lemma allocator_free_search_missing_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr)
    (allocations : list allocator_header_entry) (w3 w4 wa2 : LWord)
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
        PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 14)
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
    - iApply "Hφ". iFrame.
  Qed.

  (** This block only reads the shadow entry of the payload base, which is
      unpainted since the payload is live: the check cannot fail. The count
      of addresses to paint is left in [ca2]. *)

  Lemma allocator_free_shadow_check_spec
    (E : coPset) (pc_b pc_e pc_a next b e sb : Addr)
    (w3 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 7 in
    let code := allocator_free_instrs_n 7 in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    (shadow_b + (b - heap_b))%a = Some sb ->
    heap_to_shadow b = Some sb ->

    b ↦ₛ ShadowLive ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ca2 ↦ᵣ wa2 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    codefrag start code ∗
    ▷ (b ↦ₛ ShadowLive ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt e ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
         codefrag start code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 8) ∗
         ct3 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ WInt (e - b)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hdisjoint Hbounds Hsb Htranslate; subst start code.
    iIntros "(Hshadow & HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hca2 & Hctp & Hcode & Hφ)".
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
    unfold lword_of_word.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hshadow]"); try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htranslate)). }
    {
      apply heap_shadow_inverse.
      exact Htranslate.
    }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htranslate)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hshadow)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowLive). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowLive) with (encodeAllocStatus ShadowLive).
    rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    assert (Hpaint : (allocator_free_block_addr pc_a 7 ^+ 7)%a = allocator_free_block_addr pc_a 8) by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hpaint) in "HPC".
    iApply "Hφ".
    iFrame.
  Qed.

  Lemma allocator_free_success_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : LWord)
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
           (allocator_free_block_addr pc_a 10) ∗
         ca0 ↦ᵣ WInt ALLOC_OK ∗
         ca1 ↦ᵣ WInt 0 ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 ALLOC_OK. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 63)%a =
      ((allocator_free_block_addr pc_a 9) ^+ 1)%a).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    assert (Hnext : (allocator_free_block_addr pc_a 9 ^+ 2)%a =
      allocator_free_block_addr pc_a 10).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hnext) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_free_prepare_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr)
    (wreq w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    allocator_free_in_prefix next wreq.(lw) ->

    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wreq ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ wreq ∗
         codefrag pc_a code ∗
         (∃ (p : Perm) (g : Locality) (b e a : Addr),
             ⌜wreq.(lw) = WCap true p g b e a
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
    intros code Hlayout Hcont Hpc Hdisjoint Hcgp_pc (p & g & b & e & a & Hreq & Hbounds);
      subst code.
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.
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
      unfold allocator_free_instrs in Hpc. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
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
    iFrame "Hslot Hcgp Hca0 Hcode".
    iExists p, g, b, e, a.
    iSplit.
    { iPureIntro. split; first done. exact Hbounds. }
    iFrame.
  Qed.

  Lemma allocator_free_prepare_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr)
    (wreq w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_instrs_n 0 ++ allocator_free_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    ¬ allocator_free_in_prefix next wreq.(lw) ->

    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wreq ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ wreq ∗
         codefrag pc_a code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_free_block_addr pc_a 14) ∗
         ct0 ↦ᵣ - ∗
         ct1 ↦ᵣ - ∗
         ct2 ↦ᵣ - ∗
         ct3 ↦ᵣ -
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout Hcont Hpc Hdisjoint Hcgp_pc Hrequest; subst code.
    destruct wreq as [wreq π]; cbn in Hrequest.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.
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
          unfold allocator_free_instrs in Hpc. solve_addr. }
        iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
        iSpecialize ("Hcode" with "Hi").
        iEval (rewrite /lload_word /lift_word /=) in "Hct0".
        iEval (cbn [load_word]) in "Hct0".
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
              iApply "Hφ". iFrame.
            }
            { exfalso. apply Hrequest.
              exists p, g, b, e, a. split; first reflexivity. solve_addr. }
          }
          replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_nonempty ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame.
        ** replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_base_ok ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame.
      * cbn.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        iApply "Hφ". iFrame.
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
      iApply "Hφ". iFrame.
  Qed.

  Context {layout_wf : allocatorLayoutWf}.

  (** The allocator's three imports, as separate words. *)
  Lemma allocator_imports_split :
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ⊣⊢
    (allocator_pcc_b ^+ allocator_shadow_import_off)%a ↦ₐ
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    (allocator_pcc_b ^+ 1)%a ↦ₐ
      WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype ∗
    (allocator_pcc_b ^+ allocator_revoker_import_off)%a ↦ₐ allocator_revoker_cap.
  Proof.
    pose proof allocator_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    rewrite /allocator_imports !fmap_cons fmap_nil.
    rewrite (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 1)%a (allocator_pcc_b ^+ 2)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 2)%a allocator_code_b);
      [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    rewrite /allocator_shadow_import_off /allocator_revoker_import_off.
    assert ((allocator_pcc_b ^+ 0)%a = allocator_pcc_b) as -> by solve_addr.
    iSplit; [iIntros "($ & $ & $ & _)" | iIntros "($ & $ & $)"]; done.
  Qed.

End AllocatorFreeTraversal.
