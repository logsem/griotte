From iris.proofmode Require Import proofmode.
From griotte.allocators.ownership Require Import allocator_preamble allocator_header_spec.
From griotte Require Import memory_region.

Section AllocatorServiceInitializationProofs.
  Context {Σ : gFunctors} {ceriseb : ceriseBaseG Σ} {th : Thread}
    {FA : FreeAuth Σ} {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Like KVS initialization, service initialization consumes only imports,
      code, and data, together with the heap: its memory, its unpainted shadow
      entries and its address claims, and the authoritative owner map of the
      owner identifiers [ids], with no allocation yet. *)

  Lemma allocator_service_init_correct (E : coPset) (mem : LMem) (ids : gset Z) :
    allocatorLayoutWf ->
    dom mem = heap_addresses ->
    allocator_service_initial_resources -∗
    allocator_owners (gset_to_gmap ∅ ids) -∗
    ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ ShadowLive) -∗
    ([∗ map] a ↦ c ∈ init_claims {[heap_b]}, addr_alloc a c)
    ={E}=∗
    allocator_service_ctx ∗
    allocator_service_static.
  Proof.
    intros Hwf Hdom.
    iIntros "(Himports & Hcode & Hdata) Howners Hheap Hclaims".
    pose proof heap_valid as Hvalid.
    iDestruct (region_pointsto_single with "Hdata") as (w) "[Hdata %Hword]".
    { exact (@allocator_size_data MP layout Hwf). }
    injection Hword as <-.
    assert (dom (init_claims {[heap_b]}) = heap_addresses) as Hdom_claims.
    { apply set_eq. intros a. rewrite elem_of_dom lookup_init_claims elem_of_heap_addresses.
      destruct (is_heap_address a); naive_solver. }
    iAssert ([∗ map] a ↦ _ ∈ init_claims {[heap_b]}, a ↦ₐ - ∗ a ↦ₛ ShadowLive)%I
      with "[Hheap]" as "Hheap".
    { rewrite big_sepM_dom Hdom_claims -Hdom -big_sepM_dom.
      iApply (big_sepM_mono with "Hheap"). iIntros (a v _) "[Ha $]". by iExists v. }
    iAssert (allocator_cells allocator_initial_cells) with "[Hheap Hclaims]" as "Hcells".
    { rewrite /allocator_cells /allocator_initial_cells big_sepM_fmap.
      iCombine "Hheap Hclaims" as "Hcells". rewrite -big_sepM_sep.
      iApply (big_sepM_mono with "Hcells").
      iIntros (a c Hc) "[ [Ha Hs] Hclaim]". rewrite /cell_res /=. iFrame.
      rewrite lookup_init_claims in Hc.
      destruct (is_heap_address a); last done.
      case_decide; simplify_eq; by iFrame. }
    iAssert (allocator_service_owners []) with "[Howners]" as "Howners".
    { iExists _. iFrame "Howners". iPureIntro. apply allocator_owners_wf_empty. }
    iMod (region_pointsto_persist with "Himports") as "#Himports".
    iMod (codefrag_persist with "Hcode") as "#Hcode".
    iMod (na_inv_alloc (tpool th) E Nallocator_service allocator_service_inv
      with "[Hdata Hcells Howners]") as "#Hservice".
    { iNext. iExists (heap_b ^+ 1), [], ∅, ∅, allocator_initial_cells.
      iFrame "Hdata Hcells Howners".
      rewrite /allocator_entries_res /=.
      iPureIntro.
      split_and!; [solve_addr|solve_addr|done|split; constructor
                  |exact allocator_initial_cells_wf|done]. }
    iModIntro. iFrame "Hservice Himports Hcode".
  Qed.

End AllocatorServiceInitializationProofs.
