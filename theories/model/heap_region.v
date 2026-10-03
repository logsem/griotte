From iris.proofmode Require Import proofmode.
From griotte Require Export heap_std region_keys allocator_resources.

(** * Status APIs

    The key-level API reads the status of the object a region key belongs to:
    a non-heap key is always live, and a heap key [LHeap a ι] reads the
    world's entry for [ι]. The address-keyed API goes through the address
    lookup; it serves the logical relation until words carry their
    allocation identifier. *)

Definition heap_key_status (W_heap : Heap) (k : LAddr) : option AllocObjectStatus :=
  match k with
  | LNonHeap _ => Some AllocObjectLive
  | LHeap a ι =>
      match W_heap !! ι with
      | Some o => if decide (alloc_object_contains o a) then Some (alloc_object_status o) else None
      | None => None
      end
  end.

Definition heap_key_live (W_heap : Heap) (k : LAddr) : Prop :=
  heap_key_status W_heap k = Some AllocObjectLive.

Lemma heap_key_live_nonheap W_heap a : heap_key_live W_heap (LNonHeap a).
Proof. done. Qed.

Lemma heap_key_status_lookup W_heap a ι o :
  W_heap !! ι = Some o -> alloc_object_contains o a ->
  heap_key_status W_heap (LHeap a ι) = Some (alloc_object_status o).
Proof. intros Hι Ho. by rewrite /heap_key_status Hι decide_True. Qed.

Lemma heap_key_status_Some W_heap a ι s :
  heap_key_status W_heap (LHeap a ι) = Some s ->
  ∃ o, W_heap !! ι = Some o ∧ alloc_object_contains o a ∧ alloc_object_status o = s.
Proof.
  rewrite /heap_key_status. destruct (W_heap !! ι) as [o|]; last done.
  case_decide; last done. intros [= <-]. eauto.
Qed.

Lemma heap_key_live_lookup W_heap a ι o :
  W_heap !! ι = Some o -> alloc_object_contains o a -> alloc_object_status o = AllocObjectLive ->
  heap_key_live W_heap (LHeap a ι).
Proof. intros Hι Ha Ho. by rewrite /heap_key_live (heap_key_status_lookup _ _ _ o) // Ho. Qed.

Lemma heap_key_status_future W_heap W_heap' k s :
  related_sts_heap_std W_heap W_heap' ->
  heap_key_status W_heap k = Some s ->
  ∃ s', heap_key_status W_heap' k = Some s' ∧
        (s = AllocObjectQuarantined → s' = AllocObjectQuarantined).
Proof.
  intros [Hkeep _] Hs. destruct k as [a|a ι].
  - simplify_eq/=. eauto.
  - apply heap_key_status_Some in Hs as (o & Hι & Ha & <-).
    destruct (Hkeep ι o Hι) as (o' & Hι' & Hb & He & Hq).
    exists (alloc_object_status o'). rewrite (heap_key_status_lookup _ _ _ o') //.
    unfold alloc_object_contains in *. by rewrite -Hb -He.
Qed.

Definition heap_addr_status `{HeapRegion} (W_heap : Heap) (a : Addr) : option AllocObjectStatus :=
  if is_heap_address a then
    alloc_object_status ∘ snd <$> heap_lookup_addr W_heap a
  else Some AllocObjectLive.

Definition heap_addr_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  heap_addr_status W_heap a = Some AllocObjectLive.

(** The region key of an address, as the logical relation chooses it: a heap
    address recorded in the world is keyed by the identifier of the object
    containing it. *)
Definition heap_addr_key `{HeapRegion} (W_heap : Heap) (a : Addr) : LAddr :=
  if is_heap_address a then
    match heap_lookup_addr W_heap a with
    | Some (ι, _) => LHeap a ι
    | None => LNonHeap a
    end
  else LNonHeap a.

Section heap_addr_key.
  Context `{HeapRegion}.

  Lemma heap_addr_key_addr W_heap a : laddr_addr (heap_addr_key W_heap a) = a.
  Proof.
    rewrite /heap_addr_key. destruct (is_heap_address a); last done.
    by destruct (heap_lookup_addr W_heap a) as [[ι o]|].
  Qed.

  Lemma heap_addr_key_nonheap W_heap a :
    is_heap_address a = false -> heap_addr_key W_heap a = LNonHeap a.
  Proof. intros Ha. by rewrite /heap_addr_key Ha. Qed.

  Lemma heap_addr_key_lookup W_heap a ι o :
    is_heap_address a = true -> heap_lookup_addr W_heap a = Some (ι,o) ->
    heap_addr_key W_heap a = LHeap a ι.
  Proof. intros Ha Hl. by rewrite /heap_addr_key Ha Hl. Qed.

  Lemma heap_addr_key_status W_heap a s :
    heap_addr_status W_heap a = Some s ->
    heap_key_status W_heap (heap_addr_key W_heap a) = Some s.
  Proof.
    rewrite /heap_addr_status /heap_addr_key.
    destruct (is_heap_address a); last done.
    destruct (heap_lookup_addr W_heap a) as [[ι o]|] eqn:Hl; last done.
    intros Hs. apply heap_lookup_addr_sound in Hl as [Hι Ha].
    by rewrite (heap_key_status_lookup _ _ _ o).
  Qed.

  Lemma heap_addr_key_live W_heap a :
    heap_addr_live W_heap a -> heap_key_live W_heap (heap_addr_key W_heap a).
  Proof. apply heap_addr_key_status. Qed.

  (** Keys are stable in futures, for addresses the world knows. *)
  Lemma heap_addr_key_future W_heap W_heap' a :
    heap_wf W_heap' -> related_sts_heap_std W_heap W_heap' ->
    is_Some (heap_addr_status W_heap a) ->
    heap_addr_key W_heap' a = heap_addr_key W_heap a.
  Proof.
    intros Hwf Hrel [s Hs]. rewrite /heap_addr_status in Hs. rewrite /heap_addr_key.
    destruct (is_heap_address a); last done.
    destruct (heap_lookup_addr W_heap a) as [[ι o]|] eqn:Hl; last discriminate.
    destruct (heap_lookup_addr_future _ _ _ _ _ Hwf Hrel Hl) as (o' & Hl' & _).
    by rewrite Hl'.
  Qed.

  Lemma heap_addr_status_future W_heap W_heap' a s :
    heap_wf W_heap' -> related_sts_heap_std W_heap W_heap' ->
    heap_addr_status W_heap a = Some s ->
    ∃ s', heap_addr_status W_heap' a = Some s' ∧
          (s = AllocObjectQuarantined → s' = AllocObjectQuarantined).
  Proof.
    intros Hwf Hrel Hs. rewrite /heap_addr_status in Hs |- *.
    destruct (is_heap_address a); last (simplify_eq; eauto).
    destruct (heap_lookup_addr W_heap a) as [[ι o]|] eqn:Hl; last discriminate.
    destruct (heap_lookup_addr_future _ _ _ _ _ Hwf Hrel Hl) as (o' & Hl' & _ & _ & Hq).
    simplify_eq/=. rewrite Hl' /=. eauto.
  Qed.

End heap_addr_key.

(** Every heap key of a world names an identifier the world's heap knows,
    even for regions that are currently open. *)
Definition heap_keys_known (W_heap : Heap) (D : gset LAddr) : Prop :=
  ∀ a ι, LHeap a ι ∈ D → ι ∈ dom W_heap.

Lemma heap_keys_known_empty W_heap : heap_keys_known W_heap ∅.
Proof. intros a ι. set_solver. Qed.

Lemma heap_keys_known_mono W_heap W_heap' D D' :
  dom W_heap ⊆ dom W_heap' → D' ⊆ D →
  heap_keys_known W_heap D → heap_keys_known W_heap' D'.
Proof. intros Hh HD Hk a ι Ha. apply Hh. apply (Hk a). by apply HD. Qed.

Lemma heap_keys_known_union W_heap D D' :
  heap_keys_known W_heap D → heap_keys_known W_heap D' →
  heap_keys_known W_heap (D ∪ D').
Proof. intros Hk Hk' a ι [Ha|Ha]%elem_of_union; [by eapply Hk|by eapply Hk']. Qed.

Lemma heap_keys_known_singleton W_heap k :
  (if k is LHeap _ ι then ι ∈ dom W_heap else True) →
  heap_keys_known W_heap {[k]}.
Proof. intros Hk a ι Ha%elem_of_singleton. by subst k. Qed.

Lemma heap_keys_known_insert W_heap (D : gset LAddr) k :
  k ∈ D → heap_keys_known W_heap D → heap_keys_known W_heap ({[k]} ∪ D).
Proof.
  intros Hk Hknown. eapply heap_keys_known_mono; [done| |exact Hknown]. set_solver.
Qed.

Lemma heap_keys_known_insert_new W_heap (D : gset LAddr) k :
  (if k is LHeap _ ι then ι ∈ dom W_heap else True) →
  heap_keys_known W_heap D → heap_keys_known W_heap ({[k]} ∪ D).
Proof.
  intros Hk Hknown. apply heap_keys_known_union; last done.
  by apply heap_keys_known_singleton.
Qed.

Lemma heap_keys_known_nonheap_list W_heap (l : list Addr) :
  heap_keys_known W_heap (list_to_set (LNonHeap <$> l)).
Proof.
  intros a ι Ha. apply elem_of_list_to_set, list_elem_of_fmap in Ha as (? & ? & _).
  discriminate.
Qed.

Lemma heap_key_status_known W_heap k s :
  heap_key_status W_heap k = Some s →
  if k is LHeap _ ι then ι ∈ dom W_heap else True.
Proof.
  destruct k as [a|a ι]; first done.
  intros (o & Hι & _)%heap_key_status_Some. by apply elem_of_dom_2 in Hι.
Qed.

(** * The heap branch of the region map

    A heap region [LHeap a ι] needs the world to know [ι], with [a] in its
    range. A live object's region holds its usual resources; a quarantined
    object's region holds nothing. *)
Definition heap_key_resource {Σ : gFunctors} (W_heap : Heap) (k : LAddr) (P : iProp Σ) : iProp Σ :=
  match k with
  | LNonHeap _ => P
  | LHeap a ι =>
      match W_heap !! ι with
      | None => False
      | Some o =>
          ⌜alloc_object_contains o a⌝ ∗
          match alloc_object_status o with
          | AllocObjectLive => P
          | AllocObjectQuarantined => emp
          end
      end
  end%I.

Section heap_key_resource.
  Context {Σ : gFunctors}.

  Global Instance heap_key_resource_ne W_heap k : NonExpansive (heap_key_resource (Σ:=Σ) W_heap k).
  Proof.
    intros n P Q HPQ. rewrite /heap_key_resource.
    destruct k as [a|a ι]; first done.
    destruct (W_heap !! ι) as [o|]; last done.
    destruct (alloc_object_status o); by repeat f_equiv.
  Qed.

  Lemma heap_key_resource_live_elim W_heap k (P : iProp Σ) :
    heap_key_live W_heap k -> heap_key_resource W_heap k P -∗ P.
  Proof.
    rewrite /heap_key_live /heap_key_resource.
    destruct k as [a|a ι]; first by iIntros (_) "$".
    intros (o & -> & _ & ->)%heap_key_status_Some. iIntros "[_ $]".
  Qed.

  Lemma heap_key_resource_live_intro W_heap k (P : iProp Σ) :
    heap_key_live W_heap k ->
    P -∗ heap_key_resource W_heap k P.
  Proof.
    rewrite /heap_key_live /heap_key_resource.
    destruct k as [a|a ι]; first by iIntros (_) "$".
    intros (o & -> & Ha & ->)%heap_key_status_Some. iIntros "$". done.
  Qed.

  Lemma heap_key_resource_status W_heap k (P : iProp Σ) :
    heap_key_resource W_heap k P -∗ ⌜is_Some (heap_key_status W_heap k)⌝.
  Proof.
    rewrite /heap_key_resource. destruct k as [a|a ι]; first by iIntros.
    destruct (W_heap !! ι) as [o|] eqn:Hι; last (iIntros "[]").
    iIntros "[% _]". by rewrite (heap_key_status_lookup _ _ _ o).
  Qed.

  Lemma heap_key_resource_mono W_heap k (P Q : iProp Σ) :
    (P -∗ Q) -∗ heap_key_resource W_heap k P -∗ heap_key_resource W_heap k Q.
  Proof.
    rewrite /heap_key_resource. destruct k as [a|a ι]; first (iIntros "H HP"; by iApply "H").
    destruct (W_heap !! ι) as [o|]; last (iIntros "_ []").
    destruct (alloc_object_status o); iIntros "HPQ [$ HP]"; try done.
    by iApply "HPQ".
  Qed.

  Lemma heap_key_resource_quarantined W_heap a ι o (P : iProp Σ) :
    W_heap !! ι = Some o -> alloc_object_status o = AllocObjectQuarantined ->
    alloc_object_contains o a ->
    ⊢ heap_key_resource W_heap (LHeap a ι) P.
  Proof. intros Hι Ho Ha. rewrite /heap_key_resource Hι Ho. by iSplit. Qed.

  Lemma heap_key_resource_quarantined_irrel W_heap k (P Q : iProp Σ) :
    heap_key_status W_heap k = Some AllocObjectQuarantined ->
    heap_key_resource W_heap k P -∗ heap_key_resource W_heap k Q.
  Proof.
    destruct k as [a|a ι]; first done.
    intros (o & Hι & Ha & Ho)%heap_key_status_Some.
    rewrite /heap_key_resource Hι Ho. by iIntros "[$ _]".
  Qed.

  Lemma heap_key_resource_known W_heap k (P : iProp Σ) :
    heap_key_resource W_heap k P -∗
    ⌜if k is LHeap a ι then ∃ o, W_heap !! ι = Some o ∧ alloc_object_contains o a else True⌝.
  Proof.
    rewrite /heap_key_resource. destruct k as [a|a ι]; first by iIntros.
    destruct (W_heap !! ι) as [o|]; last (iIntros "[]").
    iIntros "[% _]". eauto.
  Qed.

  (** The region of a heap key survives a change of the world's heap that
      keeps the key's entry. *)
  Lemma heap_key_resource_heap_eq W_heap W_heap' k (P : iProp Σ) :
    (if k is LHeap _ ι then W_heap' !! ι = W_heap !! ι else True) ->
    heap_key_resource W_heap k P -∗ heap_key_resource W_heap' k P.
  Proof.
    rewrite /heap_key_resource. destruct k as [a|a ι]; first by iIntros (_) "$".
    intros ->. iIntros "$".
  Qed.

  Lemma heap_key_resource_emp W_heap k :
    is_Some (heap_key_status W_heap k) ->
    ⊢ heap_key_resource (Σ := Σ) W_heap k emp.
  Proof.
    rewrite /heap_key_status /heap_key_resource.
    destruct k as [a|a ι]; first by iIntros.
    destruct (W_heap !! ι) as [o|]; last by intros [? ?].
    case_decide; last by intros [? ?].
    intros _. iSplit; first done. by destruct (alloc_object_status o).
  Qed.

  Lemma heap_key_resource_future W_heap W_heap' k (P Q : iProp Σ) :
    related_sts_heap_std W_heap W_heap' ->
    heap_key_resource W_heap k P -∗ (P -∗ Q) -∗ heap_key_resource W_heap' k Q.
  Proof.
    iIntros ([Hfut _]) "HP HPQ".
    destruct k as [a|a ι]; first by iApply "HPQ".
    rewrite /heap_key_resource.
    destruct (W_heap !! ι) as [o|] eqn:Hι; last done.
    destruct (Hfut ι o Hι) as (o' & Hι' & Hbase & Hend & Hq).
    rewrite Hι'.
    iDestruct "HP" as "[%Hcontains HP]".
    iSplit.
    { iPureIntro. rewrite /alloc_object_contains -Hbase -Hend. exact Hcontains. }
    destruct (alloc_object_status o') eqn:Hs'; last done.
    destruct (alloc_object_status o) eqn:Hs; first by iApply "HPQ".
    specialize (Hq eq_refl). congruence.
  Qed.

End heap_key_resource.

Section heap_region.
  Context {Σ : gFunctors} {allocatorg : allocatorG Σ} `{!allocRegistryG Σ} `{HeapRegion}.

  (** Each entry of a world's heap carries the registry's record of its range
      (D18) and, temporarily, the allocator's receipt for it. A quarantined
      entry carries the registry's witness that its object reached [AQuar]. *)
  Definition heap_entry_provenance (ι : AId) (o : AllocObject) : iProp Σ :=
    alloc_obj ι (alloc_object_base o) (alloc_object_end o) ∗
    (∃ reserved : Z * Z,
       allocator_allocation ι (alloc_object_base o) (alloc_object_end o) reserved) ∗
    (if alloc_object_status o is AllocObjectQuarantined then ι ⊒ AQuar else True).

  Definition heap_provenance (h : Heap) : iProp Σ :=
    [∗ map] ι ↦ o ∈ h, heap_entry_provenance ι o.

  Global Instance heap_entry_provenance_persistent ι o :
    Persistent (heap_entry_provenance ι o).
  Proof. rewrite /heap_entry_provenance. destruct (alloc_object_status o); apply _. Qed.

  Global Instance heap_provenance_persistent h : Persistent (heap_provenance h).
  Proof. apply _. Qed.

  Lemma heap_provenance_lookup h ι o :
    h !! ι = Some o ->
    heap_provenance h -∗ heap_entry_provenance ι o.
  Proof. iIntros (Hι) "Hprov". by iApply (big_sepM_lookup with "Hprov"). Qed.

  Lemma heap_provenance_alloc_obj h ι o :
    h !! ι = Some o ->
    heap_provenance h -∗ alloc_obj ι (alloc_object_base o) (alloc_object_end o).
  Proof.
    iIntros (Hι) "Hprov". by iDestruct (heap_provenance_lookup with "Hprov") as "[$ _]".
  Qed.

  Lemma heap_provenance_quarantined h ι o :
    h !! ι = Some o -> alloc_object_status o = AllocObjectQuarantined ->
    heap_provenance h -∗ ι ⊒ AQuar.
  Proof.
    iIntros (Hι Ho) "Hprov". iDestruct (heap_provenance_lookup with "Hprov") as "(_ & _ & Hq)";
      first done.
    by rewrite Ho.
  Qed.

  Lemma heap_provenance_quarantine h ι :
    heap_provenance h -∗ ι ⊒ AQuar -∗ heap_provenance (heap_quarantine h ι).
  Proof.
    iIntros "#Hprovenance #Hq".
    iApply big_sepM_intro.
    iIntros (κ o' Hlookup). iModIntro.
    destruct (decide (κ = ι)) as [->|Hne].
    - destruct (h !! ι) as [o|] eqn:Hι.
      + rewrite (heap_quarantine_lookup h ι o Hι) in Hlookup.
        injection Hlookup as <-.
        iDestruct (heap_provenance_lookup with "Hprovenance") as "(Hobj & Hreceipt & _)";
          first exact Hι.
        rewrite /heap_entry_provenance /=. iFrame "#".
      + rewrite /heap_quarantine fin_maps.lookup_alter_eq Hι in Hlookup.
        discriminate.
    - rewrite (heap_quarantine_lookup_ne h ι κ (λ Heq, Hne (eq_sym Heq))) in Hlookup.
      by iApply (heap_provenance_lookup with "Hprovenance").
  Qed.

  Lemma heap_provenance_allocate h ι b e reserved :
    heap_provenance h -∗
    alloc_obj ι b e -∗
    allocator_allocation ι b e reserved -∗
    heap_provenance (heap_allocate h ι b e).
  Proof.
    iIntros "#Hprov #Hobj #Hreceipt".
    rewrite /heap_provenance /heap_allocate.
    iApply big_sepM_insert_2; last done.
    rewrite /heap_entry_provenance /=. iFrame "#".
  Qed.

  (** A status share held outside a world refutes a quarantined entry. *)
  Lemma heap_provenance_status_live h ι o q :
    h !! ι = Some o ->
    heap_provenance h -∗ ι ↦st{q} ALive -∗
    ⌜alloc_object_status o = AllocObjectLive⌝.
  Proof.
    iIntros (Hι) "Hprov Hs".
    destruct (alloc_object_status o) eqn:Ho; first done.
    iDestruct (heap_provenance_quarantined with "Hprov") as "Hq"; [done|done|].
    iDestruct (live_quar_false with "Hs Hq") as %[].
  Qed.

End heap_region.

Lemma heap_addr_live_nonheap `{HeapRegion} W_heap a :
  is_heap_address a = false -> heap_addr_live W_heap a.
Proof. intros Ha. by rewrite /heap_addr_live /heap_addr_status Ha. Qed.

Lemma heap_addr_live_lookup `{HeapRegion} W_heap a ι o :
  heap_lookup_addr W_heap a = Some (ι,o) ->
  alloc_object_status o = AllocObjectLive -> heap_addr_live W_heap a.
Proof.
  intros Ha Ho. rewrite /heap_addr_live /heap_addr_status.
  destruct (is_heap_address a); last done. by rewrite Ha /= Ho.
Qed.

Lemma free_heap_quarantine_status_outside `{HeapRegion} h ι b e :
  heap_wf h ->
  h !! ι = Some (MkAllocObject b e AllocObjectLive) ->
  ∀ a, a ∉ finz.seq_between b e ->
    heap_addr_status h a =
    heap_addr_status (heap_quarantine h ι) a.
Proof.
  intros Hwf Hι a Houtside.
  rewrite /heap_addr_status.
  destruct (is_heap_address a) eqn:Ha; last reflexivity.
  destruct (heap_lookup_addr h a) as [ [κ o] |] eqn:Hlookup.
  - apply heap_lookup_addr_sound in Hlookup as [Hκ Hcontains].
    assert (κ <> ι) as Hκne.
    { intro Heq. subst κ. rewrite Hι in Hκ. injection Hκ as <-.
      apply Houtside. apply elem_of_finz_seq_between.
      unfold alloc_object_contains in Hcontains. simpl in Hcontains.
      exact Hcontains. }
    assert (heap_lookup_addr (heap_quarantine h ι) a = Some (κ,o))
      as Hnew.
    { eapply heap_lookup_addr_complete.
      - apply heap_quarantine_wf. exact Hwf.
      - rewrite heap_quarantine_lookup_ne; [exact Hκ|congruence].
      - exact Hcontains. }
    rewrite Hnew. reflexivity.
  - pose proof (proj1 (heap_lookup_addr_none h a Hwf) Hlookup) as Hnone.
    destruct (heap_lookup_addr (heap_quarantine h ι) a)
      as [ [κ o] |] eqn:Hnew; last reflexivity.
    apply heap_lookup_addr_sound in Hnew as [Hκ Hcontains].
    destruct (decide (κ = ι)) as [->|Hκne].
    + rewrite (heap_quarantine_lookup h ι _ Hι) in Hκ.
      injection Hκ as <-. exfalso. apply Houtside.
      apply elem_of_finz_seq_between.
      unfold alloc_object_contains in Hcontains. simpl in Hcontains.
      exact Hcontains.
    + rewrite heap_quarantine_lookup_ne in Hκ; [|congruence].
      exfalso. exact (Hnone κ o Hκ Hcontains).
Qed.

Lemma hts_heap_quarantine_single_status `{HeapRegion} h ι b e :
    heap_wf h ->
    (b + 1)%a = Some e ->
    h !! ι = Some (MkAllocObject b e AllocObjectLive) ->
    forall a, a <> b ->
      heap_addr_status h a = heap_addr_status (heap_quarantine h ι) a.
Proof.
  intros Hwf Hsucc Hι a Hne. apply (free_heap_quarantine_status_outside h ι b e Hwf Hι).
  rewrite elem_of_finz_seq_between. solve_addr.
Qed.
