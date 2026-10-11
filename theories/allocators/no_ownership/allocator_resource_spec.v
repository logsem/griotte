From iris.proofmode Require Import proofmode.
From griotte.allocators.no_ownership Require Import allocator_preamble allocator_header_spec.
From griotte Require Import memory_region.

Section AllocatorServiceInitializationProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {FA : FreeAuth Σ} {MP : MachineParameters} {layout : allocatorLayout}.

  (** Like KVS initialization, service initialization consumes only imports,
      code, and data, together with the heap: its memory, its unpainted shadow
      entries and its address claims. *)

  Lemma allocator_service_init_correct (E : coPset) (mem : LMem) :
    allocatorLayoutWf ->
    dom mem = heap_addresses ->
    allocator_service_initial_resources -∗
    ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ ShadowLive) -∗
    ([∗ map] a ↦ c ∈ init_claims {[heap_b]}, addr_alloc a c)
    ={E}=∗
    allocator_service_ctx.
  Proof.
    intros Hwf Hdom.
    iIntros "[Hstatic Hdata] Hheap Hclaims".
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
      iIntros (a c Hc) "[[Ha Hs] Hclaim]". rewrite /cell_res /=. iFrame.
      rewrite lookup_init_claims in Hc.
      destruct (is_heap_address a); last done.
      case_decide; simplify_eq; by iFrame. }
    iMod (na_inv_alloc cerise_nais E Nallocator_service allocator_service_inv
      with "[Hstatic Hdata Hcells]") as "#Hservice".
    { iNext. iFrame "Hstatic". iExists (heap_b ^+ 1)%a, [], ∅, ∅, allocator_initial_cells.
      iFrame "Hdata Hcells".
      rewrite /allocator_entries_res /=.
      iPureIntro.
      split_and!; [solve_addr|solve_addr|done|split; constructor
                  |exact allocator_initial_cells_wf|done]. }
    iModIntro. iExact "Hservice".
  Qed.

End AllocatorServiceInitializationProofs.
