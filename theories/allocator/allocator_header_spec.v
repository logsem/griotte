From iris.proofmode Require Import proofmode.
From griotte.allocator Require Import allocator_preamble.

From griotte Require Import proofmode heap_region region_keys.

Lemma allocator_chain_bounds h stop allocations :
  allocator_chain h stop allocations -> (h <= stop)%a.
Proof.
  destruct allocations as [| [ [ [b e] reserved] ι] rest]; simpl.
  - intros ->. solve_addr.
  - intros ((Hbase & Hbe & Hstop) & _).
    unfold allocator_header_words in Hbase. solve_addr.
Qed.

Lemma allocator_chain_member_bounds h stop allocations b e reserved ι :
  allocator_chain h stop allocations ->
  (b, e, reserved, ι) ∈ allocations ->
  (h < b /\ b < e /\ e <= stop)%a.
Proof.
  revert h. induction allocations as [| [ [ [b0 e0] r0] ι0] rest IH]; intros h Hchain Hin.
  - set_solver.
  - destruct Hchain as ((Hbase & Hbe & Hstop) & Htail).
    unfold allocator_header_words in Hbase.
    rewrite elem_of_cons in Hin. destruct Hin as [Heq|Hin].
    + injection Heq as -> -> -> ->. solve_addr.
    + specialize (IH e0 Htail Hin). solve_addr.
Qed.

(** Bases are unique in a chain: an entry is determined by its base. *)
Lemma allocator_chain_base_unique h stop allocations b e reserved ι e' reserved' ι' :
  allocator_chain h stop allocations ->
  (b, e, reserved, ι) ∈ allocations ->
  (b, e', reserved', ι') ∈ allocations ->
  e = e' ∧ reserved = reserved' ∧ ι = ι'.
Proof.
  revert h. induction allocations as [| [ [ [b0 e0] r0] ι0] rest IH];
    intros h Hchain Hin Hin'.
  - set_solver.
  - destruct Hchain as ((Hbase & Hbe & Hstop) & Htail).
    unfold allocator_header_words in Hbase.
    rewrite elem_of_cons in Hin. rewrite elem_of_cons in Hin'.
    destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin'].
    + injection Heq as -> -> -> ->. injection Heq' as -> -> ->. done.
    + injection Heq as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b0 e' reserved' ι' Htail Hin').
      solve_addr.
    + injection Heq' as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b0 e reserved ι Htail Hin).
      solve_addr.
    + eapply (IH e0); eauto.
Qed.

Lemma allocator_entry_ids_app l l' :
  allocator_entry_ids (l ++ l') = allocator_entry_ids l ++ allocator_entry_ids l'.
Proof. by rewrite /allocator_entry_ids fmap_app. Qed.

Lemma allocator_entry_ids_elem_of allocations b e reserved ι :
  (b, e, reserved, ι) ∈ allocations -> ι ∈ allocator_entry_ids allocations.
Proof.
  intros Hin. apply list_elem_of_fmap. by exists (b, e, reserved, ι).
Qed.

Lemma allocator_history_map_fst allocations :
  fst <$> ((λ '(b, e, reserved, ι), (ι, (b, e, reserved))) <$> allocations) =
  allocator_entry_ids allocations.
Proof.
  rewrite /allocator_entry_ids -list_fmap_compose.
  apply list_fmap_ext. by intros _ [ [ [b e] reserved] ι] _.
Qed.

Lemma allocator_history_map_member allocations ι b e reserved :
  allocator_history_map allocations !! ι = Some (b, e, reserved) ->
  (b, e, reserved, ι) ∈ allocations.
Proof.
  intros Hlookup. apply elem_of_list_to_map_2, list_elem_of_fmap in Hlookup.
  destruct Hlookup as ([ [ [b' e'] r'] ι'] & Heq & Hin). by simplify_eq.
Qed.

Lemma allocator_history_map_lookup allocations ι b e reserved :
  NoDup (allocator_entry_ids allocations) ->
  (b, e, reserved, ι) ∈ allocations ->
  allocator_history_map allocations !! ι = Some (b, e, reserved).
Proof.
  intros Hnodup Hin. apply elem_of_list_to_map_1.
  - by rewrite allocator_history_map_fst.
  - apply list_elem_of_fmap. by exists (b, e, reserved, ι).
Qed.

Lemma allocator_history_map_fresh allocations ι :
  ι ∉ allocator_entry_ids allocations ->
  allocator_history_map allocations !! ι = None.
Proof.
  intros Hι. apply not_elem_of_list_to_map_1.
  by rewrite allocator_history_map_fst.
Qed.

Lemma allocator_entries_wf_snoc allocations b e ι :
  ι ∉ allocator_entry_ids allocations ->
  allocator_entries_wf allocations ->
  allocator_entries_wf (allocations ++ [(b, e, (0%Z, 0%Z), ι)]).
Proof.
  intros Hι [Hzero Hnodup]. split.
  - apply Forall_app. split; first done. by repeat constructor.
  - rewrite allocator_entry_ids_app. apply list.NoDup_app. split; first done.
    split.
    + intros ι' Hin Hin'. cbn in Hin'. apply list_elem_of_singleton in Hin'. by subst.
    + cbn. apply NoDup_singleton.
Qed.

Lemma allocator_chain_subrange_spec :
  ∀ h stop allocations b e b' e',
    allocator_chain h stop allocations ->
    allocator_has_bounds allocations b e ->
    (b <= b' /\ b' < e' /\ e' <= e)%a ->
    (b', e') ≠ (b, e) ->
    ¬ allocator_has_bounds allocations b' e'.
Proof.
  intros h stop allocations. revert h.
  induction allocations as [| [ [ [b0 e0] r0] ι0] rest IH];
    intros h b e b' e' Hchain [r [ι Hin] ] Hbounds Hneq [r' [ι' Hin'] ].
  - set_solver.
  - destruct Hchain as [Hhead Htail].
    rewrite elem_of_cons in Hin. rewrite elem_of_cons in Hin'.
    destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin'].
    + injection Heq as -> -> -> ->. injection Heq' as -> -> -> ->. done.
    + injection Heq as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b' e' r' ι' Htail Hin').
      solve_addr.
    + injection Heq' as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b e r ι Htail Hin).
      solve_addr.
    + eapply (IH e0 b e b' e' Htail); eauto; do 2 eexists; eassumption.
Qed.

Section AllocatorHeaderContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  Lemma allocator_headers_chain_spec :
    ∀ h stop allocations,
      allocator_headers h stop allocations ⊢
      ⌜allocator_chain h stop allocations⌝.
  Proof.
    intros h stop allocations. revert h.
    induction allocations as [| [ [ [b e] reserved] ι] rest IH]; intros h; simpl.
    - done.
    - iIntros "(%Hbounds & (%Hbase & Hfirst & Hreserved) & Htail)".
      iDestruct (IH with "Htail") as %Htail.
      iPureIntro. split; [split|]; done.
  Qed.

  (** The split point is a header address or the terminal bump pointer.
      This is the prefix/suffix decomposition used by the traversal loop. *)

  Lemma allocator_headers_app_spec :
    ∀ h stop prefix suffix,
      allocator_headers h stop (prefix ++ suffix) ⊣⊢
      ∃ middle : Addr,
        allocator_headers h middle prefix ∗
        allocator_headers middle stop suffix.
  Proof.
    intros h stop prefix. revert h.
    induction prefix as [| [ [ [b e] reserved] ι] prefix IH]; intros h suffix; simpl.
    - iSplit.
      + iIntros "Htail". iExists h. iFrame. done.
      + iIntros "(%middle & %Heq & Htail)". by subst middle.
    - iSplit.
      + iIntros "(%Hbounds & Hhead & Htail)".
        iDestruct (IH with "Htail") as (middle) "[Hprefix Hsuffix]".
        iDestruct (allocator_headers_chain_spec with "Hprefix") as %Hchain.
        pose proof (allocator_chain_bounds e middle prefix Hchain) as Hmiddle.
        iExists middle. iFrame "Hsuffix". simpl. iFrame "Hhead Hprefix".
        iPureIntro. solve_addr.
      + iIntros "(%middle & (%Hbounds & Hhead & Hprefix) & Hsuffix)".
        iDestruct (allocator_headers_chain_spec with "Hsuffix") as %Hchain.
        pose proof (allocator_chain_bounds middle stop suffix Hchain) as Hmiddle.
        iSplit; first (iPureIntro; solve_addr). iFrame "Hhead".
        iApply IH. iExists middle. iFrame.
  Qed.

  Lemma allocator_headers_snoc_spec :
    ∀ first h b e reserved ι allocations,
      allocator_header_bounds h e b e ->
      allocator_headers first h allocations -∗
      allocator_header h b e reserved -∗
      allocator_headers first e (allocations ++ [(b, e, reserved, ι)]).
  Proof.
    intros first h b e reserved ι allocations [Hbase Hbounds].
    iIntros "Hprefix Hhead". iApply allocator_headers_app_spec.
    iExists h. iFrame "Hprefix". simpl. iFrame "Hhead". done.
  Qed.

End AllocatorHeaderContracts.

Section AllocatorHistoryContracts.
  Context {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}.

  Lemma allocator_allocation_persistent_spec :
    ∀ ι b e reserved, Persistent (allocator_allocation ι b e reserved).
  Proof.
    intros ι b e reserved. apply _.
  Qed.

  Lemma allocator_history_lookup_spec :
    ∀ allocations ι b e reserved,
      allocator_history allocations -∗
      allocator_allocation ι b e reserved -∗
      ⌜allocator_history_map allocations !! ι = Some (b, e, reserved)⌝.
  Proof.
    intros allocations ι b e reserved. apply ghost_map_lookup.
  Qed.

  (** A receipt names a ghost header entry. *)
  Lemma allocator_history_member_spec allocations ι b e reserved :
    allocator_history allocations -∗
    allocator_allocation ι b e reserved -∗
    ⌜(b, e, reserved, ι) ∈ allocations⌝.
  Proof.
    iIntros "Hhistory Hreceipt".
    iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt") as %Hlookup.
    iPureIntro. by apply allocator_history_map_member.
  Qed.

  (** Receipt uniqueness: under the history, a base names one identifier. *)
  Lemma allocator_receipt_unique h stop allocations ι ι' b e e' reserved reserved' :
    allocator_chain h stop allocations ->
    allocator_history allocations -∗
    allocator_allocation ι b e reserved -∗
    allocator_allocation ι' b e' reserved' -∗
    ⌜ι = ι' ∧ e = e' ∧ reserved = reserved'⌝.
  Proof.
    iIntros (Hchain) "Hhistory Hreceipt Hreceipt'".
    iDestruct (allocator_history_member_spec with "Hhistory Hreceipt") as %Hin.
    iDestruct (allocator_history_member_spec with "Hhistory Hreceipt'") as %Hin'.
    iPureIntro.
    destruct (allocator_chain_base_unique _ _ _ _ _ _ _ _ _ _ Hchain Hin Hin')
      as (-> & -> & ->).
    done.
  Qed.

  Lemma allocator_history_insert_spec :
    ∀ allocations ι b e reserved,
      allocator_history_map allocations !! ι = None ->
      allocator_history allocations
      ==∗
      allocator_history (allocations ++ [(b, e, reserved, ι)]) ∗
      allocator_allocation ι b e reserved.
  Proof.
    intros allocations ι b e reserved Hfresh.
    iIntros "Hhistory".
    iMod (ghost_map_insert_persist ι (b, e, reserved) with "Hhistory") as "[Hhistory Hreceipt]";
      first exact Hfresh.
    iModIntro. iFrame "Hreceipt".
    rewrite /allocator_history /allocator_history_map fmap_app list_to_map_app /=
      -insert_union_r; last exact Hfresh.
    rewrite right_id. iExact "Hhistory".
  Qed.

End AllocatorHistoryContracts.

Section AllocatorEntriesContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}.

  Lemma allocator_entries_res_app l l' :
    allocator_entries_res (l ++ l') ⊣⊢
    allocator_entries_res l ∗ allocator_entries_res l'.
  Proof. by rewrite /allocator_entries_res big_sepL_app. Qed.

  Lemma allocator_entries_res_ids allocations :
    allocator_entries_res allocations -∗
    allocator_entries_res allocations ∗
    [∗ list] ι ∈ allocator_entry_ids allocations, ∃ b e, alloc_obj ι b e.
  Proof.
    induction allocations as [| [ [ [b e] reserved] ι] rest IH]; simpl.
    - by iIntros "$".
    - rewrite /allocator_entries_res /=.
      iIntros "[[#Hobj Htok] Hrest]".
      iDestruct (IH with "Hrest") as "[$ $]". iFrame "∗#".
  Qed.

  (** Take the token of the entry at index [k] and put back another one. *)
  Lemma allocator_entries_res_acc allocations k b e reserved ι :
    allocations !! k = Some (b, e, reserved, ι) ->
    allocator_entries_res allocations -∗
    alloc_obj ι b e ∗ allocator_tok ι b e ∗
    (allocator_tok ι b e -∗ allocator_entries_res allocations).
  Proof.
    iIntros (Hk) "Hres".
    iDestruct (big_sepL_lookup_acc _ _ k (b, e, reserved, ι) with "Hres")
      as "[[#Hobj Htok] Hclose]"; first exact Hk.
    iFrame "Hobj Htok". iIntros "Htok". iApply "Hclose". iFrame "∗#".
  Qed.

End AllocatorEntriesContracts.

Section AllocatorServiceContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {FA : FreeAuth Σ} {MP : MachineParameters} {layout : allocatorLayout}.

  Lemma allocator_history_heap_bounds h allocations next :
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_history allocations -∗
    heap_provenance h -∗
    ⌜∀ κ o, h !! κ = Some o ->
      (alloc_object_base o < alloc_object_end o /\ alloc_object_end o <= next)%a⌝.
  Proof.
    revert allocations next.
    induction h as [|κ o h Hnone IH] using map_ind;
      intros allocations next Hchain; iIntros "Hhistory #Hprovenance".
    - iPureIntro. intros κ o Hlookup. rewrite lookup_empty in Hlookup. discriminate.
    - iEval (rewrite /heap_provenance big_sepM_insert //) in "Hprovenance".
      iDestruct "Hprovenance" as "[(_ & #Hreceipt & _) #Hrest]".
      iDestruct "Hreceipt" as (reserved) "#Hreceipt".
      iDestruct (allocator_history_member_spec with "Hhistory Hreceipt")
        as %Hmember.
      pose proof (allocator_chain_member_bounds (heap_b ^+ 1)%a next
        allocations _ _ reserved κ Hchain Hmember)
        as (_ & Hbe & Hend).
      iDestruct (IH allocations next Hchain with "Hhistory Hrest") as %Hrest_bounds.
      iPureIntro. intros κ' o' Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      naive_solver.
  Qed.

  (** The new chunk lies above every object of a world whose provenance the
      history covers, so any identifier unknown to the world is fresh there. *)
  Lemma allocator_history_heap_fresh h allocations next b e :
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_header_bounds next heap_e b e ->
    allocator_history allocations -∗
    heap_provenance h -∗
    ⌜∀ ι, h !! ι = None -> heap_fresh h ι b e⌝.
  Proof.
    iIntros (Hchain Hchunk) "Hhistory Hprovenance".
    iDestruct (allocator_history_heap_bounds h allocations next Hchain
      with "Hhistory Hprovenance") as %Hbounds.
    destruct Hchunk as [Hbase Hrest].
    destruct Hrest as [Hbe Hend].
    iPureIntro. intros ι Hι. unfold heap_fresh.
    split; first exact Hι.
    split; first exact Hbe.
    intros κ o a Hlookup Hnew Hold.
    pose proof (Hbounds κ o Hlookup) as [_ Hoend].
    unfold alloc_object_contains in Hold.
    unfold allocator_header_words in Hbase. solve_addr.
  Qed.

  (** The bump slot already contains [e]: the executable store must precede
      this logical publication. This update neither writes memory nor paints.
      It allocates the identifier of the new object in the registry, fresh
      for the given set [X] and for the published entries, and splits its
      status token between the allocator, the client and the [n] cells. *)

  Lemma allocator_service_commit_spec :
    ∀ E next b e allocations (X : gset AId),
      ↑Nallocator ⊆ E ->
      (heap_b < next)%a ->
      allocator_header_bounds next heap_e b e ->
      allocator_entries_wf allocations ->
      allocator_ctx -∗
      ([∗ set] ι ∈ X, ∃ b' e', alloc_obj ι b' e') -∗
      allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e e -∗
      free_addr_token heap_b -∗
      free_addrs e heap_e -∗
      allocator_headers (heap_b ^+ 1)%a next allocations -∗
      allocator_history allocations -∗
      allocator_entries_res allocations -∗
      allocator_header next b e (0%Z, 0%Z)
      ={E}=∗
      ∃ ι,
        ⌜ι ∉ X⌝ ∗
        allocator_service_data e ∗
        alloc_obj ι b e ∗
        allocator_allocation ι b e (0%Z, 0%Z) ∗
        free_auth_held ι ∗
        ([∗ list] _ ∈ finz.seq_between b e, ι ↦st{share (finz.dist b e)} ALive).
  Proof.
    intros E next b e allocations X HE Hnext [Hbase Hbounds] Hwf.
    iIntros "#Hctx #HX Hslot Hroot Hfree Hheaders Hhistory Hres Hhead".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iDestruct (allocator_entries_res_ids with "Hres") as "[Hres #Hids]".
    iAssert ([∗ set] ι ∈ X ∪ list_to_set (allocator_entry_ids allocations),
      ∃ b' e', alloc_obj ι b' e')%I as "#HX'".
    { iApply (big_sepS_union_2 with "HX").
      rewrite big_sepS_list_to_set; last exact (proj2 Hwf). iExact "Hids". }
    iMod (allocator_registry_alloc E b e _ HE with "Hctx HX'")
      as (ι Hι) "[#Hobj Htok]".
    apply not_elem_of_union in Hι as [HιX Hιids].
    rewrite elem_of_list_to_set in Hιids.
    iMod (allocator_history_insert_spec allocations ι b e (0%Z, 0%Z) with "Hhistory")
      as "[Hhistory Hreceipt]"; first by apply allocator_history_map_fresh.
    iEval (rewrite (st_own_split_alloc ι (finz.seq_between b e))
      finz_seq_between_length -free_auth_split) in "Htok".
    iDestruct "Htok" as "[[Hkept Hheld] [Hshare Hcells]]".
    iModIntro. iExists ι. iFrame "Hobj Hreceipt Hheld Hcells".
    iSplit; first done.
    iExists (allocations ++ [(b, e, (0%Z, 0%Z), ι)]).
    iFrame "Hslot Hroot Hfree Hhistory".
    iSplit; first (iPureIntro; unfold allocator_header_words in Hbase; solve_addr).
    iSplitL "Hheaders Hhead".
    { iApply (allocator_headers_snoc_spec with "Hheaders Hhead").
      split; [exact Hbase|solve_addr]. }
    iSplit; first (iPureIntro; by apply allocator_entries_wf_snoc).
    rewrite allocator_entries_res_app. iFrame "Hres".
    rewrite /allocator_entries_res /=. iFrame "Hobj".
    iLeft. iFrame.
  Qed.

End AllocatorServiceContracts.
