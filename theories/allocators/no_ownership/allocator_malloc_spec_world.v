From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocators.no_ownership Require Import allocator_header_spec allocator_malloc_spec_states.
From griotte.allocators.common Require Export allocator_common_spec_world.

(** * Logical steps of the proof of [malloc]

    The lemmas of this file do not execute code. They are used between the
    block groups of [allocator_malloc_spec_<segment>_blocks_<n>] in the proof
    of [allocator_malloc_valid_correct]. *)

Section AllocatorMallocWorld.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Publish the entry of [ι] in the service data, with the new bump cursor
      [finish]. The status token of [ι] is split between the allocator, the
      client half and the cells of [ι], which go to the client with their
      memory. *)
  Lemma allocator_malloc_publish_entry
    (next b finish : Addr) (ι : AId)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    (heap_b < next)%a ->
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_entries_wf allocations ->
    allocator_cells_wf next allocations live issued Cs ->
    (next + allocator_header_words)%a = Some b ->
    (b < finish /\ finish <= heap_e)%a ->
    ι ∉ issued ->
    allocator_cells
      (allocator_cells_update (finz.seq_between next finish) (allocator_malloc_cell b ι) Cs) -∗
    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e finish -∗
    allocator_headers (heap_b ^+ 1)%a next allocations -∗
    allocator_header next b finish (0%Z, 0%Z) -∗
    allocator_entries_res live allocations -∗
    alloc_obj ι b finish -∗
    ι ↦st{1} ALive -∗
    ([∗ list] a ∈ finz.seq_between b finish, a ↦ₐ WInt 0) -∗
    allocator_service_data finish ∗
    free_auth_held ι ∗
    [[b, finish]] ↦ₕ[ι] [[region_addrs_zeroes b finish]].
  Proof.
    intros Hnext Hchain Hwf Hcwf Hbase Hrange Hιissued.
    iIntros "Hcells Hslot Hheaders Hhead Htoks #Hobj Htok Hzeros".
    iEval (rewrite (st_own_split_alloc ι (finz.seq_between b finish))
      finz_seq_between_length -free_auth_split) in "Htok".
    iDestruct "Htok" as "[[Hkept Hheld] [Hshare Hshares]]".
    assert (Hιids : ι ∉ allocator_entry_ids allocations).
    { intros Hin. apply Hιissued, (acw_issued _ _ _ _ _ Hcwf).
      by apply elem_of_list_to_set. }
    iSplitL "Hcells Hslot Hheaders Hhead Htoks Hkept Hshare".
    { iExists (allocations ++ [(b, finish, (0%Z, 0%Z), ι)]), (live ∪ {[ι]}),
        (issued ∪ {[ι]}), _.
      iFrame "Hslot Hcells".
      iSplit; first (iPureIntro; unfold allocator_header_words in Hbase; solve_addr).
      iSplitL "Hheaders Hhead".
      { iApply (allocator_headers_snoc_spec with "Hheaders Hhead").
        split; [exact Hbase|solve_addr]. }
      iSplit; first (iPureIntro; by apply allocator_entries_wf_snoc).
      iSplit.
      { iPureIntro. by apply allocator_cells_wf_malloc. }
      rewrite allocator_entries_res_app.
      iSplitL "Htoks".
      { iApply (allocator_entries_res_live_ext with "Htoks").
        intros ι' Hι'. assert (ι' ≠ ι) by (intros ->; done). set_solver. }
      rewrite /allocator_entries_res /= /allocator_tok decide_True; last set_solver.
      iFrame "Hobj Hshare Hkept". }
    iFrame "Hheld".
    iApply (heap_region_pointsto_split with "Hobj"). iFrame "Hshares".
    rewrite /region_addrs_zeroes /region_pointsto
      -(finz_seq_between_length b finish) big_sepL2_replicate_r;
      last reflexivity.
    iFrame.
  Qed.

End AllocatorMallocWorld.
