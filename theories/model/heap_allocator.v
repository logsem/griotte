From griotte Require Export heap_std.
From griotte.allocator Require Import allocator_preamble.

Definition alloc_object_cell_state (s : AllocObjectStatus) : AllocState :=
  match s with
  | AllocObjectLive => Live
  | AllocObjectQuarantined => Quarantined
  end.

(** Agreement at allocator operation boundaries. Headers and free cells are
    outside object payloads. During trusted painting, the per-cell states may
    temporarily disagree with the indivisible logical object transition. *)
Definition heap_std_allocator_agree
  (W_heap : Heap) (allocations : list allocator_header_entry)
  (alloc_map : gmap Addr AllocState) : Prop :=
  heap_wf W_heap /\
  alloc_object_end <$> W_heap = fst <$> list_to_map allocations /\
  ∀ b o a, W_heap !! b = Some o -> alloc_object_contains b o a ->
    alloc_map !! a = Some (alloc_object_cell_state (alloc_object_status o)).

Lemma heap_std_allocator_agree_lookup W_heap allocations alloc_map a b o :
  heap_std_allocator_agree W_heap allocations alloc_map ->
  heap_lookup_addr W_heap a = Some (b,o) ->
  alloc_map !! a = Some (alloc_object_cell_state (alloc_object_status o)).
Proof.
  intros (_ & _ & Hcells) Hfind.
  apply heap_lookup_addr_sound in Hfind as [Hb Ha]. eauto.
Qed.

Lemma heap_std_allocator_agree_bounds W_heap allocations alloc_map b o :
  heap_std_allocator_agree W_heap allocations alloc_map ->
  W_heap !! b = Some o ->
  ∃ reserved : Z, (list_to_map allocations : gmap Addr (Addr * Z)) !! b = Some (alloc_object_end o, reserved).
Proof.
  intros (_ & Hbounds & _) Hb.
  assert (((alloc_object_end <$> W_heap) : gmap Addr Addr) !! b =
    ((fst <$> list_to_map allocations) : gmap Addr Addr) !! b) as Hlookup
    by (rewrite Hbounds; reflexivity).
  rewrite !lookup_fmap Hb /= in Hlookup.
  symmetry in Hlookup. apply fmap_Some in Hlookup as ([e r] & He & Heq).
  cbn in Heq. subst e. eauto.
Qed.

Lemma heap_std_allocator_agree_empty alloc_map :
  heap_std_allocator_agree ∅ [] alloc_map.
Proof.
  split; first apply heap_wf_empty. split; first by rewrite /= !fmap_empty.
  intros b o a Hb. rewrite lookup_empty in Hb. discriminate.
Qed.
