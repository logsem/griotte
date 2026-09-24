From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec.

(** Address of an assembled block relative to the entry point. *)
Definition allocator_free_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_free)))%a.

Section AllocatorFreeBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_free_success_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 5 in
    let code := allocator_free_instrs_n 5 in
    ContiguousRegion pc_a (length allocator_free_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e start
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ca1 ↦ᵣ wstatus
    ∗ ▷ codefrag start code
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_free_block_addr pc_a 7)
         ∗ ca0 ↦ᵣ WInt 0
         ∗ ca1 ↦ᵣ WInt ALLOC_OK
         ∗ codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(>HPC & >Hca0 & >Hca1 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 37)%a =
      ((allocator_free_block_addr pc_a 5) ^+ 1)%a).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 ALLOC_OK. *)
    iInstr "Hcode".
    (* Jmp .free_return. *)
    iInstr "Hcode".
    assert (Hret : (allocator_free_block_addr pc_a 5 ^+ 5)%a =
      allocator_free_block_addr pc_a 7).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hret) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_free_prepare_valid_spec
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
    allocator_free_valid next wreq ->

    allocator_ctx
    ∗ allocator_service_data next
    ∗ ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ct0 ↦ᵣ w0
    ∗ ▷ ct1 ↦ᵣ w1
    ∗ ▷ ct2 ↦ᵣ w2
    ∗ ▷ ct3 ↦ᵣ w3
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (allocator_service_data next
         ∗ cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b
         ∗ ca0 ↦ᵣ wreq
         ∗ codefrag pc_a code
         ∗ (∃ (p : Perm) (g : Locality) (b e a : Addr),
             ⌜wreq = WCap true p g b e a
               ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝
             ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
                 (allocator_free_block_addr pc_a 2)
             ∗ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
             ∗ ct1 ↦ᵣ WInt b
             ∗ ct2 ↦ᵣ WInt e
             ∗ ct3 ↦ᵣ WInt 0)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout HE Hcont Hpc Hdisjoint (p & g & b & e & a & -> & Hbounds); subst code.
    iIntros "(#Hctx & Hdata & >HPC & >Hcgp & >Hca0 & >Hct0 & >Hct1 & >Hct2 & >Hct3 & >Hcode & Hφ)".
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_cap true p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
    (* Jnz .free_invalid ct3 falls through for a capability. *)
    iInstr "Hcode".
    (* GetTag ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    rewrite /Z.b2z Z.sub_diag.
    (* Jnz .free_invalid ct3 falls through for a tagged capability. *)
    iInstr "Hcode".
    (* Load ct0 cgp reads the stored bump capability with its clear root shadow bit. *)
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
    (* Lt ct3 ct3 ct1 tests heap_b < b. *)
    iInstr "Hcode".
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_base_ok ct3 skips the invalid jump. *)
    iInstr "Hcode".
    (* Lt ct3 ct1 ct2 tests b < e. *)
    iInstr "Hcode".
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_nonempty ct3 skips the invalid jump. *)
    iInstr "Hcode".
    (* GetA ct3 ct0 reads the bump cursor. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct2 tests next < e. *)
    iInstr "Hcode".
    replace (next <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .free_invalid ct3 falls through for e <= next. *)
    iInstr "Hcode".
    iApply "Hφ".
    iSplitL "Hslot Hroot Hfree".
    { iFrame. done. }
    iFrame "Hcgp Hca0 Hcode".
    iExists p, g, b, e, a.
    iSplit.
    { iPureIntro. split; first done. exact Hbounds. }
    iFrame.
  Qed.

  Lemma allocator_free_prepare_invalid_spec
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
    ¬ allocator_free_valid next wreq ->

    allocator_ctx
    ∗ allocator_service_data next
    ∗ ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b
    ∗ ▷ ca0 ↦ᵣ wreq
    ∗ ▷ ct0 ↦ᵣ w0
    ∗ ▷ ct1 ↦ᵣ w1
    ∗ ▷ ct2 ↦ᵣ w2
    ∗ ▷ ct3 ↦ᵣ w3
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (allocator_service_data next
         ∗ cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b
         ∗ ca0 ↦ᵣ wreq
         ∗ codefrag pc_a code
         ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_free_block_addr pc_a 6)
         ∗ ct0 ↦ᵣ -
         ∗ ct1 ↦ᵣ -
         ∗ ct2 ↦ᵣ -
         ∗ ct3 ↦ᵣ -
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout HE Hcont Hpc Hdisjoint Hrequest; subst code.
    iIntros "(#Hctx & Hdata & >HPC & >Hcgp & >Hca0 & >Hct0 & >Hct1 & >Hct2 & >Hct3 & >Hcode & Hφ)".
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    codefrag_facts "Hcode".
    (* GetWType ct3 ca0. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    destruct (is_cap wreq) eqn:Hreq_cap.
    + destruct wreq; cbn in Hreq_cap; try done.
      destruct sb; cbn in Hreq_cap; try done.
      rewrite (encodeWordType_correct_cap tag p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
      (* Jnz .free_invalid ct3 falls through for a capability. *)
      iInstr "Hcode".
      (* GetTag ct3 ca0. *)
      iInstr "Hcode".
      (* Sub ct3 ct3 1. *)
      iInstr "Hcode".
      destruct tag.
      * rewrite /Z.b2z Z.sub_diag.
        (* Jnz .free_invalid ct3 falls through for a tagged capability. *)
        iInstr "Hcode".
        (* Load ct0 cgp reads the stored bump capability with its clear root shadow bit. *)
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
        (* Lt ct3 ct3 ct1 tests heap_b < b. *)
        iInstr "Hcode".
        destruct (decide (heap_b < b)%a) as [Hbase|Hbase].
        ** replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
          (* Jnz .free_base_ok ct3 skips the invalid jump. *)
          iInstr "Hcode".
          (* Lt ct3 ct1 ct2 tests b < e. *)
          iInstr "Hcode".
          destruct (decide (b < e)%a) as [Hnonempty|Hempty].
          {
            replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
            (* Jnz .free_nonempty ct3 skips the invalid jump. *)
            iInstr "Hcode".
            (* GetA ct3 ct0 reads the bump cursor. *)
            iInstr "Hcode".
            (* Lt ct3 ct3 ct2 tests next < e. *)
            iInstr "Hcode".
            destruct (decide (next < e)%a) as [Hpast|Hwithin].
            {
              replace (next <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
              (* Jnz .free_invalid ct3 rejects e > next. *)
              iInstr "Hcode".
              iApply "Hφ". iFrame. done.
            }
            { exfalso. apply Hrequest.
              exists p, g, b, e, a. split; first reflexivity. solve_addr. }
          }
          replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_nonempty ct3 falls through for an empty interval. *)
          iInstr "Hcode".
          (* Jmp .free_invalid rejects an empty interval. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame. done.
        ** replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_base_ok ct3 falls through for an invalid base. *)
          iInstr "Hcode".
          (* Jmp .free_invalid rejects a base outside the heap prefix. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame. done.
      * cbn.
        (* Jnz .free_invalid ct3 rejects an untagged capability. *)
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
      (* Jnz .free_invalid ct3 rejects a non-capability word. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame. done.
  Qed.
End AllocatorFreeBlocks.

Section AllocatorFreeProof.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {allocatorg : allocatorG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}
    {layout_wf : allocatorLayoutWf}
  .

  (** Since the service invariant hides the bump cursor, this class of requests
      is invalid for every possible cursor. It includes [WInt 0]. *)
  Definition allocator_free_always_invalid (wreq : Word) : Prop :=
    ∀ next : Addr,
      (heap_b < next /\ next <= heap_e)%a →
      ¬ allocator_free_valid next wreq.

  Lemma allocator_memory_not_free_cell E a w :
    ↑Nallocator ⊆ E -> a ∈ heap_addresses ->
    allocator_ctx -∗ a ↦ₐ w -∗ free_cell_token a ={E}=∗ False.
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
    allocator_ctx -∗ [[b,e]] ↦ₐ [[ws]] -∗ free_cells next heap_e ={E}=∗ False.
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
    allocator_ctx -∗ [[b,e]] ↦ₐ [[ws]] -∗ free_cells next heap_e
      ={E}=∗ ⌜(e <= next)%a⌝ ∗ [[b,e]] ↦ₐ [[ws]] ∗ free_cells next heap_e.
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

  (** A call with an invalid request leaves client memory untouched and returns
      [ALLOC_INVALID]. Other registers and resources can be framed. *)
  Lemma allocator_free_invalid_correct
    (E : coPset) (wreq wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ⊢ (⌜↑Nallocator ⊆ E⌝ -∗
       ⌜↑Nallocator_service ⊆ E⌝ -∗
       ⌜allocator_free_always_invalid wreq⌝ -∗

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
    iIntros "%HEheap %HEservice %Hinvalid".
    iIntros "(#Hctx & #Hservice & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
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
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    assert (Hrequest : ¬ allocator_free_valid next wreq).
    { apply Hinvalid. exact Hnext. }
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree]" as "Hdata".
    { iFrame. iPureIntro. exact Hnext. }
    iApply (allocator_free_prepare_invalid_spec with
      "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
    iNext. iIntros
      "(Hdata & Hcgp & Hca0 & Hprepare_code & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
    iEval (rewrite -Hsplit) in "Hfreecode".
    (* The validity check rejects the request; set ALLOC_INVALID. *)
    assert (Hsplit6 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 6 assembled_allocator_free) ++
      (allocator_free_instrs_n 6 ++ allocator_free_instrs_n 7)) by reflexivity.
    iEval (rewrite Hsplit6) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_invalid Ha_invalid "Hinvalid_code" "Hfreecode_cont".
    assert (Haddr : a_invalid = allocator_free_block_addr allocator_free_pcc_addr 6).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_invalid.
    (* Mov ca0 0. *)
    iInstr "Hinvalid_code".
    iDestruct "Hca1" as (wca1) "Hca1".
    changePCto ((allocator_free_block_addr allocator_free_pcc_addr 6) ^+ 1)%a.
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
      concat (encodeInstrsW <$> take 7 assembled_allocator_free) ++
      allocator_free_instrs_n 7) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret "Hret_code" "Hfreecode_cont".
    assert (Haddr : a_ret = allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_ret.
    changePCto (allocator_free_block_addr allocator_free_pcc_addr 7).
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
  Qed.

  (** Ownership of every cell in the capability's bounds witnesses a live
      range in the allocated prefix. A successful call relinquishes that memory
      and returns one reclaim token per cell. Permissions and cursor may vary. *)
  Lemma allocator_free_valid_correct
    (E : coPset) (p : Perm) (g : Locality) (b e a : Addr)
    (ws : list Word) (wret : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    ⊢ (⌜↑Nallocator ⊆ E⌝ -∗
       ⌜↑Nallocator_service ⊆ E⌝ -∗
       ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a⌝ -∗
       ⌜length ws = length (finz.seq_between b e)⌝ -∗

       allocator_ctx ∗
       allocator_service_ctx ∗
       na_own cerise_nais E ∗
       [[b, e]] ↦ₐ [[ws]] ∗

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

       ▷ (na_own cerise_nais E ∗
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
    iIntros "%HEheap %HEservice %Hbounds %Hlen".
    iIntros "(#Hctx & #Hservice & Hna & Hmem & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hpost)".
    (* Open the service invariant and recover the allocator code and state. *)
    iMod (na_inv_acc with "Hservice Hna") as "(Hinv & Hna & Hclose)"; try exact HEservice.
    iDestruct "Hinv" as ">[Hstatic Hdata]".
    iDestruct "Hstatic" as "[Himports Hcode]".
    iDestruct "Hdata" as (next) "Hdata".
    iDestruct "Hdata" as "(%Hnext & Hslot & Hroot & Hfree)".
    (* Use ownership of the range to show that it lies below the bump cursor. *)
    iMod (allocator_owned_range_below_cursor E b e next ws HEheap Hbounds Hnext Hlen
      with "Hctx Hmem Hfree") as "(%Hend & Hmem & Hfree)".
    iAssert (allocator_service_data next) with "[Hslot Hroot Hfree]" as "Hdata".
    { iFrame. iPureIntro. exact Hnext. }
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
    assert (Hrequest : allocator_free_valid next (WCap true p g b e a)).
    { exists p, g, b, e, a. split; first reflexivity. solve_addr. }
    iApply (allocator_free_prepare_valid_spec with
      "[- $Hctx $Hdata $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hprepare_code]"); eauto.
    iNext. iIntros "(Hdata & Hcgp & Hca0 & Hprepare_code & Hvalid)".
    iDestruct "Hvalid" as (p0 g0 b0 e0 a0)
      "(%Hvalid & HPC & Hct0 & Hct1 & Hct2 & Hct3)".
    destruct Hvalid as [Heq Hvalid]. inversion Heq; subst; clear Heq.
    iDestruct ("Hfree_cont" with "Hprepare_code") as "Hfreecode".
    iEval (rewrite -Hsplit) in "Hfreecode".
    (* Fetch the shadow capability and translate the range to free. *)
    assert (Hsplit2 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 2 assembled_allocator_free) ++
      (allocator_free_instrs_n 2 ++
       concat (encodeInstrsW <$> drop 3 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit2) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_fetch Ha_fetch
      "Hfetch_code" "Hfreecode_cont".
    assert (Haddr : a_fetch = allocator_free_block_addr allocator_free_pcc_addr 2).
    { unfold allocator_free_block_addr in *. solve_addr. }
    subst a_fetch.
    pose proof allocator_size_imports as Himports_size.
    iDestruct (region_pointsto_single with "Himports") as (v)
      "[Himport %Hentry]"; first exact Himports_size.
    cbn in Hentry. inversion Hentry; subst v.
    assert (Hfetch_eq : allocator_free_instrs_n 2 =
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
    { rewrite -Hfetch_eq; exact H2. }
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
    iNext. iIntros "(HPC & Hctp & Hct3 & Hca2 & Hfetch_code & Himport)".
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
      concat (encodeInstrsW <$> take 3 assembled_allocator_free) ++
      (allocator_free_instrs_n 3 ++
       concat (encodeInstrsW <$> drop 4 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit3) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_translate Ha_translate
      "Htranslate_code" "Hfreecode_cont".
    assert (Haddr3 : a_translate =
      allocator_free_block_addr allocator_free_pcc_addr 3).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_translate.
    assert (Hpc3 : (allocator_free_block_addr allocator_free_pcc_addr 2 ^+
      length (fetch.fetch_instrs allocator_shadow_import_off ctp ct3 ca2))%a =
      allocator_free_block_addr allocator_free_pcc_addr 3).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hpc3) in "HPC".
    assert (Htranslate_eq : allocator_free_instrs_n 3 =
      allocator_malloc_instrs_n 4) by reflexivity.
    iEval (rewrite Htranslate_eq) in "Htranslate_code".
    iApply (allocator_translate_spec with
      "[- $HPC $Hct0 $Hct1 $Hct2 $Hct3 $Hctp $Hca2 $Htranslate_code]");
      eauto; try solve_addr.
    iNext. iIntros
      "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hctp & Hca2 & Htranslate_code)".
    iEval (rewrite -Htranslate_eq) in "Htranslate_code".
    iDestruct ("Hfreecode_cont" with "Htranslate_code") as "Hfreecode".
    iEval (rewrite -Hsplit3) in "Hfreecode".
    (* Set the shadow bits and exchange memory ownership for reclaim tokens. *)
    assert (Hsplit4 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 4 assembled_allocator_free) ++
      (allocator_free_instrs_n 4 ++
       concat (encodeInstrsW <$> drop 5 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit4) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_paint Ha_paint
      "Hpaint_code" "Hfreecode_cont".
    assert (Haddr4 : a_paint =
      allocator_free_block_addr allocator_free_pcc_addr 4).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_paint.
    assert (Hpc4 : (allocator_free_block_addr allocator_free_pcc_addr 3 ^+
      length (allocator_malloc_instrs_n 4))%a =
      allocator_free_block_addr allocator_free_pcc_addr 4).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hpc4) in "HPC".
    pose (sb := (shadow_b ^+ (b0 - heap_b))%a).
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
    assert (Hpaint_eq : allocator_free_instrs_n 4 =
      allocator_paint_instrs ctp ca2 ShadowQuarantined) by reflexivity.
    iEval (rewrite Hpaint_eq) in "Hpaint_code".
    iApply (allocator_paint_spec ShadowQuarantined ctp ca2 E RX Global
      allocator_pcc_b allocator_pcc_e
      (allocator_free_block_addr allocator_free_pcc_addr 4) b0 e0 sb se ws
      with "[- $Hctx $HPC $Hctp $Hca2 $Hpaint_code $Hmem]").
    { reflexivity. }
    { rewrite -Hpaint_eq; exact H6. }
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
    iNext. iIntros "(HPC & Hctp & Hca2 & Hpaint_code & Hreclaimed)".
    iEval (rewrite -Hpaint_eq) in "Hpaint_code".
    iDestruct ("Hfreecode_cont" with "Hpaint_code") as "Hfreecode".
    iEval (rewrite -Hsplit4) in "Hfreecode".
    (* Set ALLOC_OK, then return and restore the service invariant. *)
    assert (Hsplit5 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 5 assembled_allocator_free) ++
      (allocator_free_instrs_n 5 ++
       concat (encodeInstrsW <$> drop 6 assembled_allocator_free))) by reflexivity.
    iEval (rewrite Hsplit5) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_success Ha_success
      "Hsuccess_code" "Hfreecode_cont".
    assert (Haddr5 : a_success =
      allocator_free_block_addr allocator_free_pcc_addr 5).
    { unfold allocator_free_block_addr. solve_addr. }
    subst a_success.
    assert (Hoff4 : allocator_free_block_addr allocator_free_pcc_addr 4 =
      (allocator_free_pcc_addr ^+ 32)%a) by reflexivity.
    assert (Hoff5 : allocator_free_block_addr allocator_free_pcc_addr 5 =
      (allocator_free_pcc_addr ^+ 36)%a) by reflexivity.
    assert (Hlenpaint : length (allocator_paint_instrs ctp ca2 ShadowQuarantined) = 4)
      by reflexivity.
    assert (Hpc5 : (allocator_free_block_addr allocator_free_pcc_addr 4 ^+
       length (allocator_paint_instrs ctp ca2 ShadowQuarantined))%a =
       allocator_free_block_addr allocator_free_pcc_addr 5).
    { clear -Hoff4 Hoff5 Hlenpaint.
      rewrite Hoff4 Hoff5 Hlenpaint.
      rewrite incr_addr_opt_add_twice.
      { replace (32 + 4)%Z with 36%Z by lia; reflexivity. }
      all: lia. }
    iEval (rewrite Hpc5) in "HPC".
    iDestruct "Hca1" as (wca1) "Hca1".
    iApply (allocator_free_success_block_spec with
      "[- $HPC $Hca0 $Hca1 $Hsuccess_code]"); eauto.
    iNext. iIntros "(HPC & Hca0 & Hca1 & Hsuccess_code)".
    iDestruct ("Hfreecode_cont" with "Hsuccess_code") as "Hfreecode".
    iEval (rewrite -Hsplit5) in "Hfreecode".
    assert (Hsplit7 : allocator_free_instrs =
      concat (encodeInstrsW <$> take 7 assembled_allocator_free) ++
      allocator_free_instrs_n 7) by reflexivity.
    iEval (rewrite Hsplit7) in "Hfreecode".
    focus_block_nochangePC 1 "Hfreecode" as a_ret Ha_ret
      "Hret_code" "Hfreecode_cont".
    assert (Haddr7 : a_ret =
      allocator_free_block_addr allocator_free_pcc_addr 7).
    { unfold allocator_free_block_addr. clear -Ha_ret.
      cbn [take concat fmap] in *. solve_addr. }
    subst a_ret.
    assert (Hret_eq : allocator_free_instrs_n 7 =
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
    iApply "Hpost". iFrame "∗".
  Qed.
End AllocatorFreeProof.
