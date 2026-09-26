From iris.proofmode Require Import proofmode.
From griotte Require Export heap_std allocator_resources.

(** Outside the physical heap, ordinary region resources are unchanged.
    An unrecorded heap address cannot be an active shared cell. *)
Definition heap_cell_status `{HeapRegion} (W_heap : Heap) (a : Addr) : option AllocObjectStatus :=
  if is_heap_address a then
    alloc_object_status ∘ snd <$> heap_lookup_addr W_heap a
  else Some AllocObjectLive.

Definition heap_cell_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  heap_cell_status W_heap a = Some AllocObjectLive.

(** A closed compartment world records every cell of a quarantined object.
    Live objects may remain outside this compartment's standard world. *)
Definition heap_quarantine_covered `{HeapRegion} {B : Type}
    (W_heap : Heap) (W_std : gmap Addr B) : Prop :=
  ∀ a, heap_cell_status W_heap a = Some AllocObjectQuarantined →
    a ∈ dom W_std.

Lemma heap_quarantine_covered_empty `{HeapRegion} {B : Type} :
  heap_quarantine_covered (B:=B) ∅ ∅.
Proof.
  intros a Hstatus.
  rewrite /heap_cell_status /= in Hstatus.
  destruct (is_heap_address a); last discriminate.
  rewrite /heap_lookup_addr map_to_list_empty /= in Hstatus. discriminate.
Qed.

Lemma heap_quarantine_covered_mono `{HeapRegion} {B : Type}
    W_heap (W_std W_std' : gmap Addr B) :
  dom W_std ⊆ dom W_std' →
  heap_quarantine_covered W_heap W_std →
  heap_quarantine_covered W_heap W_std'.
Proof. intros Hdom Hcovered a Hstatus. by apply Hdom, Hcovered. Qed.

Section heap_region.
  Context {Σ : gFunctors} {allocatorg : allocatorG Σ} `{HeapRegion}.

  Definition heap_cell_resource (W_heap : Heap) (a : Addr) (P : iProp Σ) : iProp Σ :=
    (if is_heap_address a then
       match heap_lookup_addr W_heap a with
       | None => False
       | Some (_, o) =>
           match alloc_object_status o with
           | AllocObjectLive => P
           | AllocObjectQuarantined => reclaim_token a
           end
       end
     else P)%I.

  Lemma heap_cell_resource_status W_heap a P :
    heap_cell_resource W_heap a P =
    (match heap_cell_status W_heap a with
     | Some AllocObjectLive => P
     | Some AllocObjectQuarantined => reclaim_token a
     | None => False
     end)%I.
  Proof.
    rewrite /heap_cell_resource /heap_cell_status.
    destruct (is_heap_address a); last done.
    destruct (heap_lookup_addr W_heap a) as [[base obj]|]; done.
  Qed.

  Global Instance heap_cell_resource_ne W_heap a : NonExpansive (heap_cell_resource W_heap a).
  Proof. intros n P Q HPQ. rewrite !heap_cell_resource_status.
    destruct (heap_cell_status W_heap a) as [[]|]; done. Qed.

  Lemma heap_cell_resource_live W_heap a P :
    heap_cell_live W_heap a -> heap_cell_resource W_heap a P = P.
  Proof. intros Ha. by rewrite heap_cell_resource_status Ha. Qed.

  Lemma heap_cell_resource_live_elim W_heap a P :
    heap_cell_live W_heap a -> heap_cell_resource W_heap a P -∗ P.
  Proof. intros Ha. rewrite (heap_cell_resource_live _ _ _ Ha). iIntros "$". Qed.

  Lemma heap_cell_resource_live_intro W_heap a P :
    heap_cell_live W_heap a -> P -∗ heap_cell_resource W_heap a P.
  Proof. intros Ha. rewrite (heap_cell_resource_live _ _ _ Ha). iIntros "$". Qed.


  Lemma heap_cell_resource_mono W_heap a P Q :
    (P -∗ Q) -∗ heap_cell_resource W_heap a P -∗ heap_cell_resource W_heap a Q.
  Proof.
    rewrite !heap_cell_resource_status. destruct (heap_cell_status W_heap a) as [[]|];
      iIntros "HPQ HP"; try done. by iApply "HPQ".
  Qed.
End heap_region.

Lemma heap_cell_live_nonheap `{HeapRegion} W_heap a :
  is_heap_address a = false -> heap_cell_live W_heap a.
Proof. intros Ha. by rewrite /heap_cell_live /heap_cell_status Ha. Qed.

Lemma heap_cell_live_lookup `{HeapRegion} W_heap a b o :
  heap_lookup_addr W_heap a = Some (b,o) ->
  alloc_object_status o = AllocObjectLive -> heap_cell_live W_heap a.
Proof.
  intros Ha Ho. rewrite /heap_cell_live /heap_cell_status.
  destruct (is_heap_address a); last done. by rewrite Ha /= Ho.
Qed.

(** The explicit cases used by list interfaces allow non-heap and live-heap
    addresses to occur together. *)
Definition heap_cell_nonheap_or_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  is_heap_address a = false ∨
  (is_heap_address a = true ∧ ∃ base obj,
    heap_lookup_addr W_heap a = Some (base,obj) ∧
    alloc_object_status obj = AllocObjectLive).

Lemma heap_cell_live_cases `{HeapRegion} W_heap a :
  heap_cell_live W_heap a ↔ heap_cell_nonheap_or_live W_heap a.
Proof.
  rewrite /heap_cell_live /heap_cell_status /heap_cell_nonheap_or_live.
  destruct (is_heap_address a) eqn:Hheap; last naive_solver.
  destruct (heap_lookup_addr W_heap a) as [[base obj]|] eqn:Hlookup;
    last naive_solver.
  cbn. destruct (alloc_object_status obj) eqn:Hstatus.
  - split; last done. intros _. right. split; first done. exists base,obj. done.
  - split; first discriminate. intros [Hfalse|[_ (base' & obj' & Heq & Hlive)]].
    + discriminate.
    + simplify_eq. congruence.
Qed.

Lemma heap_cells_live_cases `{HeapRegion} W_heap l :
  Forall (heap_cell_live W_heap) l ↔ Forall (heap_cell_nonheap_or_live W_heap) l.
Proof. rewrite !Forall_forall. setoid_rewrite heap_cell_live_cases. done. Qed.
