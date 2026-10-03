From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From griotte.allocator Require Import allocator_preamble.
From griotte Require Import memory_region.

Section AllocatorResourceProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  Lemma free_addr_token_exclusive_correct (a : Addr) :
    ⊢ (free_addr_token a -∗
    free_addr_token a -∗
    False)%I.
  Proof. iApply free_addr_token_exclusive. Qed.

  Lemma allocator_entry_free_token_correct (a : Addr) (s : AllocState) :
    ⊢ (allocator_entry a s -∗
    free_addr_token a -∗
    ⌜s = Free⌝)%I.
  Proof. iApply allocator_entry_free_token. Qed.

  Lemma free_addr_tokens_split_correct (A : gset Addr) :
    ⊢ (own allocator_free_name (GSet A) -∗
       [∗ set] a ∈ A, free_addr_token a)%I.
  Proof. iApply free_addr_tokens_split. Qed.

  Lemma free_addrs_split_correct (b m e : Addr) :
    (b <= m /\ m <= e)%a ->
    ⊢ (free_addrs b e ∗-∗
       free_addrs b m ∗
       free_addrs m e)%I.
  Proof.
    intros Hbounds.
    rewrite /free_addrs (finz_seq_between_split b m e Hbounds) big_sepL_app.
    iSplit; iIntros "$".
  Qed.

  Lemma allocator_entry_allocate_correct (a : Addr) :
    ⊢ (allocator_entry a Free -∗
    free_addr_token a -∗
       allocator_entry a Live ∗
       a ↦ₐ -)%I.
  Proof. iApply allocator_entry_allocate. Qed.

  (** There is no physical shadow update: both [Free] and [Live] are clear.
      Empty ranges are allowed. The returned words have not been zeroed. *)

  Lemma allocator_take_range_correct (E : coPset) (b e : Addr) :
    ↑Nallocator ⊆ E ->
    (heap_b <= b /\ b <= e /\ e <= heap_e)%a ->
    ⊢ (allocator_ctx -∗
       free_addrs b e
       ={E}=∗
       allocator_range_memory b e)%I.
  Proof.
    intros HE Hbounds.
    iIntros "#Halloc Hfree".
    rewrite /free_addrs /allocator_range_memory.
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
    { iNext. iApply ("Hput" $! Live with "[//]"). iFrame. }
    iModIntro. iFrame.
  Qed.

End AllocatorResourceProofs.

Section AllocatorInitializationProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocator_preg : allocator_preG Σ}
    {MP : MachineParameters}.

  Lemma allocator_init_with_free_tokens_correct (E : coPset) (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    ⊢ (allocator_initial_resources m -∗
       reg_auth ∅
    ={E}=∗
       ∃ ag : allocatorG Σ,
         allocator_ctx (allocatorg := ag) ∗
         allocator_client_resources (allocatorg := ag) m ∗
         allocator_initial_free_tokens (allocatorg := ag) m ∗
         allocator_history_empty (allocatorg := ag))%I.
  Proof.
    intros Hdom.
    iIntros "Hm HR".
    iApply (allocator_init_with_free_tokens with "Hm HR"); done.
  Qed.

  Lemma allocator_init_free_with_tokens_correct (E : coPset) (mem : Mem) :
    dom mem = heap_addresses ->
    ⊢ (([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗
       a ↦ₛ ShadowLive) -∗
       reg_auth ∅
       ={E}=∗
       ∃ ag : allocatorG Σ,
         allocator_ctx (allocatorg := ag) ∗
         free_addrs (allocatorg := ag) heap_b heap_e ∗
         allocator_history_empty (allocatorg := ag))%I.
  Proof.
    intros Hdom.
    iIntros "Hm HR".
    iMod (allocator_init_with_free_tokens E ((fun v => (Free,v)) <$> mem)
      with "[Hm] HR") as (ag) "[Halloc [_ [Hfree Hhistory]]]".
    { by rewrite dom_fmap_L. }
    { rewrite /allocator_initial_resources big_sepM_fmap. iExact "Hm". }
    iModIntro. iExists ag. iFrame "Halloc Hhistory".
    rewrite /allocator_initial_free_tokens big_sepM_fmap /= big_sepM_dom Hdom
      /heap_addresses big_sepS_list_to_set; last apply finz_seq_between_NoDup.
    iExact "Hfree".
  Qed.

End AllocatorInitializationProofs.

Lemma allocator_namespaces_disjoint : Nallocator ## Nallocator_service.
Proof. unfold Nallocator, Nallocator_service. solve_ndisj. Qed.

Section AllocatorServiceInitializationProofs.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocator_preg : allocator_preG Σ}
    {FA : FreeAuth Σ} {MP : MachineParameters} {layout : allocatorLayout}.

  (** The initial heap may contain arbitrary words, but every shadow bit must
      be clear. Initialization allocates both token families, an empty immutable
      header-metadata map, and both invariants. There are initially no header addresses.
      Existing heap-only clients continue to use their compatibility wrappers. *)

  Lemma allocator_service_init_correct (E : coPset) (mem : Mem) :
    allocatorLayoutWf /\ dom mem = heap_addresses ->
    ⊢ (allocator_service_initial_resources -∗
       ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗
       a ↦ₛ ShadowLive) -∗
       reg_auth ∅
       ={E}=∗
       ∃ (ag : allocatorG Σ),
         allocator_ctx (allocatorg := ag) ∗
         allocator_service_ctx (allocatorg := ag))%I.
  Proof.
    intros [Hwf Hdom].
    iIntros "[Hstatic Hdata] Hheap HR".
    iMod (allocator_init_free_with_tokens_correct E mem Hdom with "Hheap HR")
      as (ag) "[Halloc [Hfree Hhistory]]".
    iDestruct (region_pointsto_single with "Hdata") as (w) "[Hdata %Hword]".
    { exact (@allocator_size_data MP layout Hwf). }
    injection Hword as <-.
    iEval (rewrite /free_addrs (finz_seq_between_cons heap_b heap_e (heap_valid))
      big_sepL_cons) in "Hfree".
    iDestruct "Hfree" as "[Hroot Hfree]".
    iMod (na_inv_alloc cerise_nais E Nallocator_service
      (allocator_service_inv (allocatorg := ag))
      with "[Hstatic Hdata Hroot Hfree Hhistory]") as "#Hservice".
    { iNext. iFrame "Hstatic". iExists (heap_b ^+ 1)%a, [].
      iEval (rewrite /allocator_history_empty /allocator_history /=) in "Hhistory".
      iFrame "Hdata Hroot Hfree Hhistory".
      rewrite /allocator_entries_res /=.
      iPureIntro.
      split_and!; [pose proof heap_valid; solve_addr|pose proof heap_valid; solve_addr|done|split; constructor|done]. }
    iModIntro. iExists ag. iFrame "Halloc Hservice".
  Qed.

End AllocatorServiceInitializationProofs.
