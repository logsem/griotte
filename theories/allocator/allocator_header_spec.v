From iris.proofmode Require Import proofmode.
From griotte.allocator Require Import allocator_preamble.

From griotte Require Import proofmode region_keys.

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

(** Two entries of a chain with different bases have disjoint payloads. *)
Lemma allocator_chain_disjoint h stop allocations b e reserved ι b' e' reserved' ι' :
  allocator_chain h stop allocations ->
  (b, e, reserved, ι) ∈ allocations ->
  (b', e', reserved', ι') ∈ allocations ->
  b ≠ b' ->
  (e <= b' \/ e' <= b)%a.
Proof.
  revert h. induction allocations as [| [ [ [b0 e0] r0] ι0] rest IH];
    intros h Hchain Hin Hin' Hne.
  - set_solver.
  - destruct Hchain as ((Hbase & Hbe & Hstop) & Htail).
    unfold allocator_header_words in Hbase.
    rewrite elem_of_cons in Hin. rewrite elem_of_cons in Hin'.
    destruct Hin as [Heq|Hin]; destruct Hin' as [Heq'|Hin'].
    + injection Heq as -> -> -> ->. injection Heq' as -> -> -> ->. done.
    + injection Heq as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b' e' reserved' ι' Htail Hin').
      left. solve_addr.
    + injection Heq' as -> -> -> ->.
      pose proof (allocator_chain_member_bounds e0 stop rest b e reserved ι Htail Hin).
      right. solve_addr.
    + eapply (IH e0); eauto.
Qed.

(** Distinct identifiers name entries with different bases. *)
Lemma allocator_chain_disjoint_ids h stop allocations b e reserved ι b' e' reserved' ι' :
  allocator_chain h stop allocations ->
  (b, e, reserved, ι) ∈ allocations ->
  (b', e', reserved', ι') ∈ allocations ->
  ι ≠ ι' ->
  (e <= b' \/ e' <= b)%a.
Proof.
  intros Hchain Hin Hin' Hne.
  destruct (decide (b = b')) as [<-|Hb].
  - destruct (allocator_chain_base_unique _ _ _ _ _ _ _ _ _ _ Hchain Hin Hin')
      as (_ & _ & ->). done.
  - by eapply allocator_chain_disjoint.
Qed.

(** An identifier names at most one entry. *)
Lemma allocator_entries_wf_unique allocations b e reserved ι b' e' reserved' :
  allocator_entries_wf allocations ->
  (b, e, reserved, ι) ∈ allocations ->
  (b', e', reserved', ι) ∈ allocations ->
  b = b' ∧ e = e' ∧ reserved = reserved'.
Proof.
  intros [_ Hnodup] Hin Hin'.
  apply list_elem_of_lookup_1 in Hin as [k Hk].
  apply list_elem_of_lookup_1 in Hin' as [k' Hk'].
  assert (allocator_entry_ids allocations !! k = Some ι) as Hik
    by (rewrite /allocator_entry_ids list_lookup_fmap Hk //).
  assert (allocator_entry_ids allocations !! k' = Some ι) as Hik'
    by (rewrite /allocator_entry_ids list_lookup_fmap Hk' //).
  pose proof (NoDup_lookup _ _ _ _ Hnodup Hik Hik') as ->.
  rewrite Hk in Hk'. by simplify_eq.
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

  Lemma allocator_entries_res_app live l l' :
    allocator_entries_res live (l ++ l') ⊣⊢
    allocator_entries_res live l ∗ allocator_entries_res live l'.
  Proof. by rewrite /allocator_entries_res big_sepL_app. Qed.

  Lemma allocator_entries_res_ids live allocations :
    allocator_entries_res live allocations -∗
    allocator_entries_res live allocations ∗
    [∗ list] ι ∈ allocator_entry_ids allocations, ∃ b e, alloc_obj ι b e.
  Proof.
    induction allocations as [| [ [ [b e] reserved] ι] rest IH]; simpl.
    - by iIntros "$".
    - rewrite /allocator_entries_res /=.
      iIntros "[[#Hobj Htok] Hrest]".
      iDestruct (IH with "Hrest") as "[$ $]". iFrame "∗#".
  Qed.

  (** The tokens of the entries depend only on the membership of their own
      identifiers in [live]. *)
  Lemma allocator_entries_res_live_ext live live' allocations :
    (∀ ι, ι ∈ allocator_entry_ids allocations -> (ι ∈ live <-> ι ∈ live')) ->
    allocator_entries_res live allocations ⊣⊢ allocator_entries_res live' allocations.
  Proof.
    intros Hext. rewrite /allocator_entries_res.
    apply big_sepL_proper. intros k [ [ [b e] reserved] ι] Hk.
    assert (ι ∈ allocator_entry_ids allocations) as Hι.
    { apply list_elem_of_fmap. exists (b, e, reserved, ι).
      split; first done. by eapply list_elem_of_lookup_2. }
    rewrite /allocator_tok.
    destruct (decide (ι ∈ live)) as [H1|H1], (decide (ι ∈ live')) as [H2|H2];
      try done; exfalso; naive_solver.
  Qed.

  (** Take the token of the entry carrying [ι]; put back a token for a new
      [live] set that agrees with the old one on the other identifiers. *)
  Lemma allocator_entries_res_acc live allocations b e reserved ι :
    NoDup (allocator_entry_ids allocations) ->
    (b, e, reserved, ι) ∈ allocations ->
    allocator_entries_res live allocations -∗
    alloc_obj ι b e ∗ allocator_tok live ι b e ∗
    (∀ live', ⌜∀ ι', ι' ≠ ι -> (ι' ∈ live <-> ι' ∈ live')⌝ -∗
       allocator_tok live' ι b e -∗ allocator_entries_res live' allocations).
  Proof.
    iIntros (Hnodup Hin) "Hres".
    apply list_elem_of_lookup_1 in Hin as [k Hk].
    rewrite /allocator_entries_res.
    iDestruct (big_sepL_lookup_acc_impl k (b, e, reserved, ι) with "Hres")
      as "[[#Hobj Htok] Hclose]"; first exact Hk.
    iFrame "Hobj Htok". iIntros (live' Hext) "Htok".
    iApply ("Hclose" $! (λ _ entry, let '(b, e, _, ι) := entry in
              alloc_obj ι b e ∗ allocator_tok live' ι b e)%I with "[] [Htok]").
    - iIntros "!>" (k' [ [ [b' e'] reserved'] ι'] Hk' Hne) "[$ Htok]".
      assert (ι' ≠ ι) as Hι'.
      { intros ->. apply Hne.
        assert (allocator_entry_ids allocations !! k = Some ι) as Hik
          by (rewrite /allocator_entry_ids list_lookup_fmap Hk //).
        assert (allocator_entry_ids allocations !! k' = Some ι) as Hik'
          by (rewrite /allocator_entry_ids list_lookup_fmap Hk' //).
        exact (NoDup_lookup _ _ _ _ Hnodup Hik' Hik). }
      rewrite /allocator_tok.
      destruct (decide (ι' ∈ live)) as [H1|H1], (decide (ι' ∈ live')) as [H2|H2];
        try done; exfalso; naive_solver.
    - iFrame "∗#".
  Qed.

End AllocatorEntriesContracts.

(** The service-local cell map: the cells of a list of addresses are
    replaced by new values. *)
Definition allocator_cells_update (l : list Addr)
    (g : Addr → AddrClaim * AllocStatus * bool)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) :
    gmap Addr (AddrClaim * AllocStatus * bool) :=
  list_to_map ((λ a, (a, g a)) <$> l) ∪ Cs.

Lemma lookup_allocator_cells_update l g Cs a :
  allocator_cells_update l g Cs !! a = if decide (a ∈ l) then Some (g a) else Cs !! a.
Proof.
  rewrite /allocator_cells_update lookup_union. case_decide as Ha.
  - rewrite (elem_of_list_to_map_1' _ a (g a)).
    + by destruct (Cs !! a).
    + intros y (x & Hx & Hxl)%list_elem_of_fmap. by simplify_eq.
    + apply list_elem_of_fmap. eauto.
  - rewrite not_elem_of_list_to_map_1.
    + by destruct (Cs !! a).
    + rewrite -list_fmap_compose. intros (x & Hxa & Hx)%list_elem_of_fmap.
      cbn in Hxa. by subst.
Qed.

Section AllocatorCellsContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  Definition cell_res' (a : Addr) (x : AddrClaim * AllocStatus * bool) : iProp Σ :=
    cell_res a x.1.1 x.1.2 x.2.

  (** One cell, and the map with that cell replaced. *)
  Lemma allocator_cells_acc Cs a x :
    Cs !! a = Some x ->
    allocator_cells Cs -∗
    cell_res' a x ∗ (∀ x', cell_res' a x' -∗ allocator_cells (<[a := x']> Cs)).
  Proof.
    iIntros (Ha) "Hcells". rewrite /allocator_cells.
    iDestruct (big_sepM_insert_acc with "Hcells") as "[Hx Hclose]"; first exact Ha.
    iFrame "Hx". iIntros (x') "Hx'". iApply ("Hclose" with "Hx'").
  Qed.

  (** The cells of a duplicate-free list of addresses, and the map with these
      cells replaced. *)
  Lemma allocator_cells_range_acc (l : list Addr) f Cs :
    NoDup l ->
    (∀ a, a ∈ l -> Cs !! a = Some (f a)) ->
    allocator_cells Cs -∗
    ([∗ list] a ∈ l, cell_res' a (f a)) ∗
    (∀ g, ([∗ list] a ∈ l, cell_res' a (g a)) -∗
       allocator_cells (allocator_cells_update l g Cs)).
  Proof.
    revert Cs. induction l as [|a l IH]; intros Cs Hnodup Hl; iIntros "Hcells".
    - iSplitR; first done. iIntros (g) "_".
      rewrite /allocator_cells_update /= left_id_L. iExact "Hcells".
    - apply list.NoDup_cons in Hnodup as [Hal Hnodup].
      rewrite /allocator_cells.
      iDestruct (big_sepM_delete with "Hcells") as "[Ha Hcells]".
      { apply Hl. apply list_elem_of_here. }
      iDestruct (IH (delete a Cs) Hnodup with "Hcells") as "[Hl Hclose]".
      { intros a' Ha'. rewrite lookup_delete_ne; last set_solver.
        apply Hl. by apply list_elem_of_further. }
      rewrite big_sepL_cons. iFrame "Ha Hl".
      iIntros (g) "[Ha Hl]".
      iDestruct ("Hclose" $! g with "Hl") as "Hcells".
      iDestruct (big_sepM_insert with "[$Hcells $Ha]") as "Hcells".
      { rewrite lookup_allocator_cells_update decide_False //. apply lookup_delete_eq. }
      assert (<[a:=g a]> (allocator_cells_update l g (delete a Cs)) =
              allocator_cells_update (a :: l) g Cs) as ->; last done.
      apply map_eq. intros a'. rewrite lookup_allocator_cells_update.
      destruct (decide (a = a')) as [<-|Hne].
      + rewrite lookup_insert_eq decide_True //. apply list_elem_of_here.
      + rewrite lookup_insert_ne // lookup_allocator_cells_update lookup_delete_ne //.
        repeat case_decide; try done; exfalso; set_solver.
  Qed.

End AllocatorCellsContracts.

(** [malloc] appends the entry of [ι] over [[b, finish)], with its header at
    [[next, b)], to the cells and the header list. *)
Definition allocator_malloc_cell (b : Addr) (ι : AId) (a : Addr) :
    AddrClaim * AllocStatus * bool :=
  if decide (a < b)%a then (Unclaimed, ShadowLive, true) else (Claimed ι, ShadowLive, false).

Lemma allocator_cells_wf_malloc {MP : MachineParameters} next b finish allocations
    live issued Cs ι :
  allocator_chain (heap_b ^+ 1)%a next allocations ->
  allocator_cells_wf next allocations live issued Cs ->
  (heap_b < next)%a ->
  (next + allocator_header_words)%a = Some b ->
  (b < finish /\ finish <= heap_e)%a ->
  ι ∉ issued ->
  allocator_cells_wf finish (allocations ++ [(b, finish, (0%Z, 0%Z), ι)])
    (live ∪ {[ι]}) (issued ∪ {[ι]})
    (allocator_cells_update (finz.seq_between next finish) (allocator_malloc_cell b ι) Cs).
Proof.
  intros Hchain Hwf Hnext Hb Hfinish Hι.
  unfold allocator_header_words in Hb.
  destruct Hwf as [Hdom Hroot Hcursor Hlive Hclaimed Hlive_ids Hissued].
  assert (∀ x, x ∈ allocator_entry_ids allocations -> x ≠ ι) as Hids.
  { intros x Hx ->. apply Hι, Hissued. by apply elem_of_list_to_set. }
  constructor.
  - intros a Ha. rewrite lookup_allocator_cells_update. case_decide; [by eexists|by apply Hdom].
  - rewrite lookup_allocator_cells_update decide_False //.
    rewrite elem_of_finz_seq_between. solve_addr.
  - intros a Ha. rewrite lookup_allocator_cells_update decide_False.
    + apply Hcursor. solve_addr.
    + rewrite elem_of_finz_seq_between. solve_addr.
  - intros b' e' reserved ι' a Hin Hι' Ha.
    rewrite lookup_allocator_cells_update.
    apply elem_of_app in Hin as [Hin|Hin].
    + pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hin) as Hbounds.
      assert (ι' ≠ ι) as Hne.
      { apply Hids. by eapply allocator_entry_ids_elem_of. }
      rewrite decide_False; last (rewrite elem_of_finz_seq_between; solve_addr).
      apply (Hlive b' e' reserved); [done|set_solver|done].
    + apply list_elem_of_singleton in Hin. simplify_eq.
      rewrite decide_True; last (rewrite elem_of_finz_seq_between; solve_addr).
      rewrite /allocator_malloc_cell decide_False //. solve_addr.
  - intros a ι' s hdr. rewrite lookup_allocator_cells_update.
    case_decide as Ha.
    + rewrite /allocator_malloc_cell. case_decide; intros Heq; simplify_eq.
      exists b, finish, (0%Z, 0%Z). split; [set_solver|]. split; [set_solver|].
      rewrite elem_of_finz_seq_between in Ha. solve_addr.
    + intros Hcs. destruct (Hclaimed a ι' s hdr Hcs) as (b' & e' & reserved & Hin & Hι' & Ha').
      exists b', e', reserved. split; [set_solver|]. split; [set_solver|done].
  - rewrite allocator_entry_ids_app list_to_set_app_L /=. set_solver.
  - rewrite allocator_entry_ids_app list_to_set_app_L /=. set_solver.
Qed.

(** [free] revokes the live entry of [ι] over [[b, e)]: its cells become
    unclaimed and unpainted, with their memory back in the service invariant. *)
Definition allocator_free_cell (a : Addr) : AddrClaim * AllocStatus * bool :=
  (Unclaimed, ShadowLive, false).

Lemma allocator_cells_wf_free {MP : MachineParameters} next allocations live issued Cs
    b e reserved ι :
  allocator_chain (heap_b ^+ 1)%a next allocations ->
  allocator_entries_wf allocations ->
  allocator_cells_wf next allocations live issued Cs ->
  (b, e, reserved, ι) ∈ allocations ->
  allocator_cells_wf next allocations (live ∖ {[ι]}) issued
    (allocator_cells_update (finz.seq_between b e) allocator_free_cell Cs).
Proof.
  intros Hchain Hentries Hwf Hin.
  pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hin) as Hbounds.
  destruct Hwf as [Hdom Hroot Hcursor Hlive Hclaimed Hlive_ids Hissued].
  constructor.
  - intros a Ha. rewrite lookup_allocator_cells_update. case_decide; [by eexists|by apply Hdom].
  - rewrite lookup_allocator_cells_update decide_False //.
    rewrite elem_of_finz_seq_between. solve_addr.
  - intros a Ha. rewrite lookup_allocator_cells_update decide_False.
    + by apply Hcursor.
    + rewrite elem_of_finz_seq_between. solve_addr.
  - intros b' e' reserved' ι' a Hin' Hι' Ha.
    apply elem_of_difference in Hι' as [Hι' Hne%not_elem_of_singleton].
    rewrite lookup_allocator_cells_update decide_False.
    + by apply (Hlive b' e' reserved').
    + rewrite elem_of_finz_seq_between.
      pose proof (allocator_chain_disjoint_ids _ _ _ _ _ _ _ _ _ _ _ Hchain Hin Hin' (not_eq_sym Hne)).
      solve_addr.
  - intros a ι' s hdr. rewrite lookup_allocator_cells_update.
    case_decide as Ha; first (rewrite /allocator_free_cell; intros [=]).
    intros Hcs. destruct (Hclaimed a ι' s hdr Hcs) as (b' & e' & reserved' & Hin' & Hι' & Ha').
    exists b', e', reserved'. split; first done. split; last done.
    apply elem_of_difference. split; first done.
    rewrite not_elem_of_singleton. intros ->.
    destruct (allocator_entries_wf_unique _ _ _ _ _ _ _ _ Hentries Hin Hin') as (-> & -> & _).
    apply Ha. by apply elem_of_finz_seq_between.
  - set_solver.
  - done.
Qed.
