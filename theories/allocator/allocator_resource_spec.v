From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From griotte.allocator Require Import allocator_preamble.
From griotte Require Import memory_region.

Section AllocatorResourceProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  Lemma free_cell_token_exclusive_correct (a : Addr) :
    ⊢ (free_cell_token a -∗ free_cell_token a -∗ False)%I.
  Proof. iApply free_cell_token_exclusive. Qed.

  Lemma allocator_entry_free_token_correct (a : Addr) (s : AllocState) :
    ⊢ (allocator_entry a s -∗ free_cell_token a -∗ ⌜s = Free⌝)%I.
  Proof. iApply allocator_entry_free_token. Qed.

  Lemma free_cell_tokens_split_correct (A : gset Addr) :
    ⊢ (own allocator_free_name (GSet A) -∗
       [∗ set] a ∈ A, free_cell_token a)%I.
  Proof. iApply free_cell_tokens_split. Qed.

  Lemma free_cells_split_correct (b m e : Addr) :
    ⊢ (⌜(b <= m /\ m <= e)%a⌝ -∗
       (free_cells b e ∗-∗ free_cells b m ∗ free_cells m e))%I.
  Proof.
    iIntros (Hbounds).
    rewrite /free_cells (finz_seq_between_split b m e Hbounds) big_sepL_app.
    iSplit; iIntros "$".
  Qed.

  Lemma allocator_entry_allocate_correct (a : Addr) :
    ⊢ (allocator_entry a Free -∗ free_cell_token a -∗
       allocator_entry a Live ∗ a ↦ₐ -)%I.
  Proof. iApply allocator_entry_allocate. Qed.

  (** There is no physical shadow update: both [Free] and [Live] are clear.
      Empty ranges are allowed. The returned words have not been zeroed. *)
  Lemma allocator_take_range_correct (E : coPset) (b e : Addr) :
    ⊢ (⌜↑Nallocator ⊆ E⌝ -∗
       ⌜(heap_b <= b /\ b <= e /\ e <= heap_e)%a⌝ -∗
       allocator_ctx -∗ free_cells b e ={E}=∗ allocator_range_memory b e)%I.
  Proof.
    iIntros (HE Hbounds) "#Halloc Hfree".
    rewrite /free_cells /allocator_range_memory.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hfree").
    iIntros "!#" (k a Hlookup) "Hfree".
    assert (a ∈ heap_addresses) as Ha.
    { apply list_elem_of_lookup_2 in Hlookup.
      apply elem_of_finz_seq_between in Hlookup.
      rewrite /heap_addresses elem_of_list_to_set elem_of_finz_seq_between.
      solve_addr. }
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup a with "Hbody") as (s) "[Hentry Hput]"; first done.
    iDestruct (allocator_entry_free_token with "Hentry Hfree") as %->.
    iDestruct (allocator_entry_allocate with "Hentry Hfree") as "[Hentry Ha]".
    iMod ("Hclose" with "[Hentry Hput]").
    { iNext. iApply ("Hput" $! Live). iFrame. }
    iModIntro. iFrame.
  Qed.

End AllocatorResourceProofs.

Section AllocatorInitializationProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocator_preg : allocator_preG Σ}
    {MP : MachineParameters}.

  Lemma allocator_init_with_free_tokens_correct (E : coPset) (m : gmap Addr (AllocState * Word)) :
    ⊢ (⌜dom m = heap_addresses⌝ -∗ allocator_initial_resources m ={E}=∗
       ∃ ag : allocatorG Σ,
         allocator_ctx (allocatorg := ag) ∗
         allocator_client_resources (allocatorg := ag) m ∗
         allocator_initial_free_tokens (allocatorg := ag) m)%I.
  Proof.
    iIntros (Hdom) "Hm".
    iApply (allocator_init_with_free_tokens with "Hm"); done.
  Qed.

  Lemma allocator_init_free_with_tokens_correct (E : coPset) (mem : Mem) :
    ⊢ (⌜dom mem = heap_addresses⌝ -∗
       ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ false) ={E}=∗
       ∃ ag : allocatorG Σ,
         allocator_ctx (allocatorg := ag) ∗
         free_cells (allocatorg := ag) heap_b heap_e)%I.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (allocator_init_with_free_tokens E ((fun v => (Free,v)) <$> mem)
      with "[Hm]") as (ag) "[Halloc [_ Hfree]]".
    { by rewrite dom_fmap_L. }
    { rewrite /allocator_initial_resources big_sepM_fmap. iExact "Hm". }
    iModIntro. iExists ag. iFrame "Halloc".
    rewrite /allocator_initial_free_tokens big_sepM_fmap /= big_sepM_dom Hdom
      /heap_addresses big_sepS_list_to_set; last apply finz_seq_between_NoDup.
    iExact "Hfree".
  Qed.
End AllocatorInitializationProofs.

Lemma allocator_namespaces_disjoint : Nallocator ## Nallocator_service.
Proof. unfold Nallocator, Nallocator_service. solve_ndisj. Qed.

Section AllocatorServiceInitializationProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocator_preg : allocator_preG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** The initial heap may contain arbitrary words, but every shadow bit must
      be clear. Initialization allocates both token families and both invariants.
      Existing heap-only clients continue to use their compatibility wrappers. *)
  Lemma allocator_service_init_correct (E : coPset) (mem : Mem) :
    ⊢ (⌜allocatorLayoutWf /\ dom mem = heap_addresses⌝ -∗
       allocator_service_initial_resources -∗
       ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ false) ={E}=∗
       ∃ ag : allocatorG Σ,
         allocator_ctx (allocatorg := ag) ∗
         allocator_service_ctx (allocatorg := ag))%I.
  Proof.
    iIntros ([Hwf Hdom]) "[Hstatic Hdata] Hheap".
    iMod (allocator_init_free_with_tokens_correct E mem with "[] Hheap") as (ag) "[Halloc Hfree]";
      first done.
    iDestruct (region_pointsto_single with "Hdata") as (w) "[Hdata %Hword]".
    { exact (@allocator_size_data MP layout Hwf). }
    injection Hword as <-.
    iEval (rewrite /free_cells (finz_seq_between_cons heap_b heap_e (heap_valid))
      big_sepL_cons) in "Hfree".
    iDestruct "Hfree" as "[Hroot Hfree]".
    iMod (na_inv_alloc cerise_nais E Nallocator_service
      (allocator_service_inv (allocatorg := ag)) with "[Hstatic Hdata Hroot Hfree]") as "#Hservice".
    { iNext. iFrame "Hstatic". iExists (heap_b ^+ 1)%a.
      iFrame "Hdata Hroot Hfree". iPureIntro.
      pose proof heap_valid. solve_addr. }
    iModIntro. iExists ag. iFrame "Halloc Hservice".
  Qed.
End AllocatorServiceInitializationProofs.
