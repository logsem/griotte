From iris.proofmode Require Import proofmode.
From griotte.allocator Require Import allocator_preamble.

From griotte Require Import proofmode heap_region.

Lemma allocator_chain_bounds h stop allocations :
  allocator_chain h stop allocations -> (h <= stop)%a.
Proof.
  destruct allocations as [| (b & e & reserved) rest]; simpl.
  - intros ->. solve_addr.
  - intros ((Hbase & Hbe & Hstop) & _).
    unfold allocator_header_words in Hbase. solve_addr.
Qed.

Lemma allocator_chain_member_bounds h stop allocations b e reserved :
  allocator_chain h stop allocations ->
  (b, (e, reserved)) ∈ allocations ->
  (h < b /\ b < e /\ e <= stop)%a.
Proof.
  revert h. induction allocations as [| (b0 & e0 & r0) rest IH]; intros h Hchain Hin.
  - set_solver.
  - destruct Hchain as ((Hbase & Hbe & Hstop) & Htail).
    unfold allocator_header_words in Hbase.
    rewrite elem_of_cons in Hin. destruct Hin as [Heq|Hin].
    + injection Heq as -> -> ->. solve_addr.
    + specialize (IH e0 Htail Hin). solve_addr.
Qed.

Lemma allocator_chain_nodup_spec :
  ∀ h stop allocations,
    allocator_chain h stop allocations ->
    NoDup allocations.*1.
Proof.
  intros h stop allocations. revert h.
  induction allocations as [| (b & e & reserved) rest IH]; intros h Hchain; simpl.
  - constructor.
  - destruct Hchain as ((Hbase & Hbe & He) & Htail).
    constructor; last by apply (IH e).
    intros Hin. apply list_elem_of_fmap in Hin.
    destruct Hin as ((b' & e' & r') & Heq & Hin). simpl in Heq. subst b'.
    pose proof (allocator_chain_member_bounds e stop rest b e' r' Htail Hin).
    solve_addr.
Qed.

Lemma allocator_chain_lookup_spec :
  ∀ h stop allocations b e reserved,
    allocator_chain h stop allocations ->
    ((list_to_map allocations : gmap Addr (Addr * (Z * Z))) !! b = Some (e, reserved) <->
     (b, (e, reserved)) ∈ allocations).
Proof.
  intros h stop allocations b e reserved Hchain. split.
  - apply elem_of_list_to_map_2.
  - apply elem_of_list_to_map_1. eapply allocator_chain_nodup_spec; eauto.
Qed.

Lemma allocator_owned_has_bounds allocations o b e :
  allocator_owned_bounds allocations o b e -> allocator_has_bounds allocations b e.
Proof. intros [r Hin]. by exists (o, r). Qed.

Lemma allocator_chain_subrange_spec :
  ∀ h stop allocations b e b' e',
    allocator_chain h stop allocations ->
    allocator_has_bounds allocations b e ->
    (b <= b' /\ b' < e' /\ e' <= e)%a ->
    (b', e') ≠ (b, e) ->
    ¬ allocator_has_bounds allocations b' e'.
Proof.
  intros h stop allocations. revert h.
  induction allocations as [| (b0 & e0 & r0) rest IH];
    intros h b e b' e' Hchain [r Hin] Hbounds Hneq [r' Hin'].
  - set_solver.
  - destruct Hchain as [Hhead Htail].
    rewrite elem_of_cons in Hin. rewrite elem_of_cons in Hin'.
    destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin'].
    + injection Heq as -> -> ->. injection Heq' as -> -> ->. done.
    + injection Heq as -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b' e' r' Htail Hin').
      solve_addr.
    + injection Heq' as -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b e r Htail Hin).
      solve_addr.
    + eapply (IH e0 b e b' e' Htail); eauto; eexists; eassumption.
Qed.

(** A new chunk at the bump pointer has a base that is a fresh heap address. *)

Lemma allocator_chain_fresh_base {MP : MachineParameters} next allocations b e :
  allocator_chain (heap_b ^+ 1)%a next allocations ->
  (heap_b < next)%a ->
  allocator_header_bounds next heap_e b e ->
  b ∈ heap_addresses ∖ allocation_bases allocations.
Proof.
  intros Hchain Hnext [Hbase Hbounds].
  unfold allocator_header_words in Hbase.
  apply elem_of_difference. split.
  - rewrite /heap_addresses elem_of_list_to_set elem_of_finz_seq_between.
    solve_addr.
  - rewrite /allocation_bases elem_of_list_to_set list_elem_of_fmap.
    intros ((b' & e' & r') & Heq & Hin). simpl in Heq. subst b'.
    pose proof (allocator_chain_member_bounds (heap_b ^+ 1)%a next
      allocations b e' r' Hchain Hin).
    solve_addr.
Qed.

Section AllocatorHeaderContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  Lemma allocator_headers_chain_spec :
    ∀ h stop allocations,
      allocator_headers h stop allocations ⊢
      ⌜allocator_chain h stop allocations⌝.
  Proof.
    intros h stop allocations. revert h.
    induction allocations as [| (b & e & reserved) rest IH]; intros h; simpl.
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
    induction prefix as [| (b & e & reserved) prefix IH]; intros h suffix; simpl.
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
    ∀ first h b e reserved allocations,
      allocator_header_bounds h e b e ->
      allocator_headers first h allocations -∗
      allocator_header h b e reserved -∗
      allocator_headers first e (allocations ++ [(b, (e, reserved))]).
  Proof.
    intros first h b e reserved allocations [Hbase Hbounds].
    iIntros "Hprefix Hhead". iApply allocator_headers_app_spec.
    iExists h. iFrame "Hprefix". simpl. iFrame "Hhead". done.
  Qed.

End AllocatorHeaderContracts.

Section AllocatorHistoryContracts.
  Context {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}.

  Lemma allocator_allocation_persistent_spec :
    ∀ b e reserved, Persistent (allocator_allocation b e reserved).
  Proof.
    intros b e reserved. apply _.
  Qed.

  Lemma allocator_history_lookup_spec :
    ∀ allocations b e reserved,
      allocator_history allocations -∗
      allocator_allocation b e reserved -∗
      ⌜(list_to_map allocations : gmap Addr (Addr * (Z * Z))) !! b = Some (e, reserved)⌝.
  Proof.
    intros allocations b e reserved. apply ghost_map_lookup.
  Qed.

  Lemma allocator_history_insert_spec :
    ∀ allocations b e reserved,
      (list_to_map allocations : gmap Addr (Addr * (Z * Z))) !! b = None ->
      allocator_history allocations
      ==∗
      allocator_history (allocations ++ [(b, (e, reserved))]) ∗
      allocator_allocation b e reserved.
  Proof.
    intros allocations b e reserved Hfresh.
    iIntros "Hhistory".
    iMod (ghost_map_insert_persist b (e, reserved) with "Hhistory") as "[Hhistory Hreceipt]";
      first exact Hfresh.
    iModIntro. iFrame "Hreceipt".
    rewrite /allocator_history list_to_map_app /= -insert_union_r; last exact Hfresh.
    rewrite right_id. iExact "Hhistory".
  Qed.

End AllocatorHistoryContracts.

Section AllocatorServiceContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Owner and rights update when publishing the allocation [b] of [o]. *)

  Lemma allocator_service_owners_publish_spec :
    ∀ next b e o r allocations S,
      (heap_b < next)%a ->
      allocator_chain (heap_b ^+ 1)%a next allocations ->
      allocator_header_bounds next heap_e b e ->
      allocator_service_owners allocations -∗
      allocator_owner_id o S
      ==∗
      allocator_service_owners (allocations ++ [(b, (e, (o, r)))]) ∗
      allocator_owner_id o (S ∪ {[b]}) ∗
      free_right b.
  Proof.
    intros next b e o r allocations S Hnext Hchain Hchunk.
    iIntros "(%O & HO & %Hwf & Hpool) Howner".
    iDestruct (allocator_owners_agree with "HO Howner") as %HS.
    iMod (allocator_owners_update with "[$HO $Howner]") as "[HO Howner]".
    pose proof (allocator_chain_fresh_base next allocations b e Hchain Hnext Hchunk)
      as Hfresh.
    iDestruct (free_rights_pool_split _ b Hfresh with "Hpool") as "[Hright Hpool]".
    iModIntro. iFrame "Howner Hright".
    iExists _. iFrame "HO".
    iSplit; first (iPureIntro; by apply allocator_owners_wf_snoc).
    rewrite allocation_bases_snoc.
    replace (heap_addresses ∖ (allocation_bases allocations ∪ {[b]}))
      with (heap_addresses ∖ allocation_bases allocations ∖ {[b]}) by set_solver.
    iExact "Hpool".
  Qed.

  Lemma allocator_history_heap_bounds h allocations next :
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_history allocations -∗
    heap_provenance h -∗
    ⌜∀ c o, h !! c = Some o ->
      (c < alloc_object_end o /\ alloc_object_end o <= next)%a⌝.
  Proof.
    revert allocations next.
    induction h as [|c o h Hnone IH] using map_ind;
      intros allocations next Hchain; iIntros "Hhistory #Hprovenance".
    - iPureIntro. intros c o Hlookup. rewrite lookup_empty in Hlookup. discriminate.
    - iEval (rewrite /heap_provenance big_sepM_insert //) in "Hprovenance".
      iDestruct "Hprovenance" as "[#Hreceipt #Hrest]".
      iDestruct "Hreceipt" as (reserved) "#Hreceipt".
      iDestruct (allocator_history_lookup_spec with "Hhistory Hreceipt")
        as %Hhist_lookup.
      apply (proj1 (allocator_chain_lookup_spec _ _ _ _ _ _ Hchain)) in Hhist_lookup.
      pose proof (allocator_chain_member_bounds (heap_b ^+ 1)%a next
        allocations c (alloc_object_end o) reserved Hchain Hhist_lookup)
        as (_ & Hbe & Hend).
      iDestruct (IH allocations next Hchain with "Hhistory Hrest") as %Hrest_bounds.
      iPureIntro. intros c' o' Hlookup.
      rewrite lookup_insert_Some in Hlookup.
      naive_solver.
  Qed.

  Lemma allocator_history_heap_fresh h allocations next b e :
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_header_bounds next heap_e b e ->
    allocator_history allocations -∗
    heap_provenance h -∗
    ⌜heap_fresh h b e⌝.
  Proof.
    iIntros (Hchain Hchunk) "Hhistory Hprovenance".
    iDestruct (allocator_history_heap_bounds h allocations next Hchain
      with "Hhistory Hprovenance") as %Hbounds.
    destruct Hchunk as [Hbase Hrest].
    destruct Hrest as [Hbe Hend].
    iPureIntro. unfold heap_fresh.
    split.
    { destruct (h !! b) as [o|] eqn:Hlookup; last done.
      pose proof (Hbounds b o Hlookup) as [_ Hoend].
      unfold allocator_header_words in Hbase.
      exfalso.
      pose proof (proj1 (Hbounds b o Hlookup)) as Hb_end.
      solve_addr. }
    split; first exact Hbe.
    intros c o a Hlookup Hnew Hold.
    pose proof (Hbounds c o Hlookup) as [_ Hoend].
    unfold alloc_object_contains in Hold.
    unfold allocator_header_words in Hbase. solve_addr.
  Qed.

  (** The bump slot already contains [e]: the executable store must precede
      this logical publication. This update neither writes memory nor paints. *)

  Lemma allocator_service_commit_spec :
    ∀ next b e o r allocations S,
      (heap_b < next)%a ->
      allocator_header_bounds next heap_e b e ->
      allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e e -∗
      free_addr_token heap_b -∗
      free_addrs e heap_e -∗
      allocator_headers (heap_b ^+ 1)%a next allocations -∗
      allocator_history allocations -∗
      allocator_service_owners allocations -∗
      allocator_owner_id o S -∗
      allocator_header next b e (o, r)
      ==∗
      allocator_service_data e ∗
      allocator_allocation b e (o, r) ∗
      allocator_owner_id o (S ∪ {[b]}) ∗
      free_right b.
  Proof.
    intros next b e o r allocations S Hnext Hchunk.
    iIntros "Hslot Hroot Hfree Hheaders Hhistory Howners Howner Hhead".
    iDestruct (allocator_headers_chain_spec with "Hheaders") as %Hchain.
    iMod (allocator_service_owners_publish_spec next b e o r allocations S
      Hnext Hchain Hchunk with "Howners Howner") as "(Howners & Howner & Hright)".
    iFrame "Howner Hright".
    set (reserved := (o, r)).
    destruct Hchunk as [Hbase Hbounds].
    assert (Hfresh : (list_to_map allocations : gmap Addr (Addr * (Z * Z))) !! b = None).
    { apply eq_None_not_Some. intros ((e' & r') & Hlookup).
      apply elem_of_list_to_map_2 in Hlookup.
      pose proof (allocator_chain_member_bounds (heap_b ^+ 1)%a next
        allocations b e' r' Hchain Hlookup).
      unfold allocator_header_words in Hbase. solve_addr. }
    iMod (allocator_history_insert_spec with "Hhistory") as "[Hhistory Hreceipt]";
      first exact Hfresh.
    iModIntro. iFrame "Hreceipt".
    iExists (allocations ++ [(b, (e, reserved))]).
    iFrame "Hslot Hroot Hfree Hhistory Howners".
    iSplit; first (iPureIntro; unfold allocator_header_words in Hbase; solve_addr).
    iApply (allocator_headers_snoc_spec with "Hheaders Hhead").
    split; [exact Hbase|solve_addr].
  Qed.

End AllocatorServiceContracts.
