From stdpp Require Import gmap list.
From griotte Require Export addresses region_keys.

(** Allocation objects describe payloads, not allocator headers or free addresses.
    The heap is keyed by allocation identifier; each object records its range.
    A world does not require the ranges of its objects to be disjoint: the
    allocation registry keeps the ranges of live objects disjoint (D5). *)
Inductive AllocObjectStatus := AllocObjectLive | AllocObjectQuarantined.

Global Instance alloc_object_status_eq_dec : EqDecision AllocObjectStatus.
Proof. solve_decision. Defined.

Record AllocObject := MkAllocObject {
  alloc_object_base : Addr;
  alloc_object_end : Addr;
  alloc_object_status : AllocObjectStatus;
}.

Global Instance alloc_object_eq_dec : EqDecision AllocObject.
Proof. solve_decision. Defined.

Definition Heap := gmap AId AllocObject.

Definition alloc_object_contains (o : AllocObject) (a : Addr) : Prop :=
  (alloc_object_base o <= a < alloc_object_end o)%a.

Global Instance alloc_object_contains_dec o a :
  Decision (alloc_object_contains o a).
Proof. unfold alloc_object_contains. apply _. Defined.

Definition alloc_object_future (o o' : AllocObject) : Prop :=
  alloc_object_base o = alloc_object_base o' /\
  alloc_object_end o = alloc_object_end o' /\
  (alloc_object_status o = AllocObjectQuarantined ->
   alloc_object_status o' = AllocObjectQuarantined).

(** Both public and private futures use this relation. A fresh object may
    already be quarantined in a future reached by several operations. A new
    object is non-empty. *)
Definition related_sts_heap_std (W_heap W_heap' : Heap) : Prop :=
  (∀ ι o, W_heap !! ι = Some o ->
    ∃ o', W_heap' !! ι = Some o' /\ alloc_object_future o o') /\
  (∀ ι o, W_heap !! ι = None -> W_heap' !! ι = Some o ->
    (alloc_object_base o < alloc_object_end o)%a).

Lemma alloc_object_future_refl o : alloc_object_future o o.
Proof. repeat split; auto. Qed.

Lemma alloc_object_future_trans o1 o2 o3 :
  alloc_object_future o1 o2 -> alloc_object_future o2 o3 -> alloc_object_future o1 o3.
Proof. intros (Hb12 & He12 & Hs12) (Hb23 & He23 & Hs23). split; [congruence|]. split; [congruence|auto]. Qed.

Lemma related_sts_heap_std_refl W_heap : related_sts_heap_std W_heap W_heap.
Proof.
  split.
  - intros b o Hb. exists o. split; auto using alloc_object_future_refl.
  - intros b o Hb Hb'. congruence.
Qed.

Lemma related_sts_heap_std_trans W_heap1 W_heap2 W_heap3 :
  related_sts_heap_std W_heap1 W_heap2 -> related_sts_heap_std W_heap2 W_heap3 ->
  related_sts_heap_std W_heap1 W_heap3.
Proof.
  intros H12 H23. destruct H12 as [Hkeep12 Hnew12].
  destruct H23 as [Hkeep23 Hnew23]. split.
  - intros ι o Hι. destruct (Hkeep12 ι o Hι) as (o2 & Hι2 & Ho2).
    destruct (Hkeep23 ι o2 Hι2) as (o3 & Hι3 & Ho3).
    exists o3. split; eauto using alloc_object_future_trans.
  - intros ι o Hι Hι3. destruct (W_heap2 !! ι) as [o2|] eqn:Hι2.
    + destruct (Hkeep23 ι o2 Hι2) as (o3 & Hι3' & Hb & He & _).
      rewrite Hι3 in Hι3'. simplify_eq. rewrite -Hb -He. eauto.
    + eauto.
Qed.


Lemma related_sts_heap_std_dom W_heap W_heap' :
  related_sts_heap_std W_heap W_heap' -> dom W_heap ⊆ dom W_heap'.
Proof.
  intros [Hkeep _] ι. rewrite !elem_of_dom.
  intros [o Hι]. destruct (Hkeep ι o Hι) as (o' & Hι' & _). eauto.
Qed.

Lemma related_sts_heap_std_quarantined W_heap W_heap' ι b e :
  related_sts_heap_std W_heap W_heap' -> W_heap !! ι = Some (MkAllocObject b e AllocObjectQuarantined) ->
  W_heap' !! ι = Some (MkAllocObject b e AllocObjectQuarantined).
Proof.
  intros [Hkeep _] Hι. destruct (Hkeep _ _ Hι) as ([b' e' s'] & Hι' & Hb_eq & He & Hs).
  cbn in *. specialize (Hs eq_refl). by subst.
Qed.

Definition heap_allocate (W_heap : Heap) (ι : AId) (b e : Addr) : Heap :=
  <[ι := MkAllocObject b e AllocObjectLive]> W_heap.

(** Extending a world needs a fresh identifier only: the world does not
    require its objects to be disjoint. *)
Definition heap_fresh (W_heap : Heap) (ι : AId) (b e : Addr) : Prop :=
  W_heap !! ι = None /\ (b < e)%a.

Lemma heap_allocate_future W_heap ι b e :
  heap_fresh W_heap ι b e -> related_sts_heap_std W_heap (heap_allocate W_heap ι b e).
Proof.
  intros [Hι Hbe]. split.
  - intros κ o Hκ. exists o. split; last apply alloc_object_future_refl.
    rewrite /heap_allocate fin_maps.lookup_insert_ne; [exact Hκ|intros ->; congruence].
  - intros κ o Hκ Hnew. rewrite /heap_allocate in Hnew.
    apply fin_maps.lookup_insert_Some in Hnew as [[-> <-]|[_ Hcontra]]; last by rewrite Hκ in Hcontra.
    done.
Qed.

(** Adjusting the one object entry changes the status of its entire interval. *)
Definition heap_quarantine (W_heap : Heap) (ι : AId) : Heap :=
  alter (λ o, MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined) ι W_heap.

Lemma heap_quarantine_lookup W_heap ι o :
  W_heap !! ι = Some o ->
  heap_quarantine W_heap ι !! ι = Some (MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
Proof. intros Hι. by rewrite /heap_quarantine fin_maps.lookup_alter_eq Hι. Qed.

Lemma heap_quarantine_lookup_ne W_heap ι κ :
  ι ≠ κ -> heap_quarantine W_heap ι !! κ = W_heap !! κ.
Proof. intros Hne. by rewrite /heap_quarantine fin_maps.lookup_alter_ne. Qed.

Lemma heap_quarantine_future W_heap ι : related_sts_heap_std W_heap (heap_quarantine W_heap ι).
Proof.
  split.
  - intros κ o Hκ. destruct (decide (ι = κ)) as [->|Hne].
    + exists (MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
      split; first by apply heap_quarantine_lookup. repeat split; done.
    + exists o. rewrite heap_quarantine_lookup_ne; last done.
      split; auto using alloc_object_future_refl.
  - intros κ o Hκ Hnew. destruct (decide (ι = κ)) as [->|Hne].
    + rewrite /heap_quarantine fin_maps.lookup_alter_eq Hκ /= in Hnew. discriminate.
    + rewrite heap_quarantine_lookup_ne // Hκ in Hnew. discriminate.
Qed.

Lemma heap_quarantine_idempotent W_heap ι :
  heap_quarantine (heap_quarantine W_heap ι) ι = heap_quarantine W_heap ι.
Proof.
  apply map_eq. intros κ. destruct (decide (ι = κ)) as [->|Hne].
  - rewrite /heap_quarantine !fin_maps.lookup_alter_eq. destruct (W_heap !! κ) eqn:Hκ; by rewrite Hκ.
  - by rewrite !heap_quarantine_lookup_ne.
Qed.

Lemma heap_quarantine_dom W_heap ι : dom (heap_quarantine W_heap ι) = dom W_heap.
Proof. by rewrite /heap_quarantine dom_alter_L. Qed.

Lemma heap_fresh_no_reuse W_heap ι b e o :
  W_heap !! ι = Some o -> ~ heap_fresh W_heap ι b e.
Proof. intros Hι [Hnone _]. rewrite Hι in Hnone. discriminate. Qed.

Lemma alloc_object_no_reverse b e :
  ~ alloc_object_future (MkAllocObject b e AllocObjectQuarantined)
      (MkAllocObject b e AllocObjectLive).
Proof. intros (_ & _ & Hs). discriminate (Hs eq_refl). Qed.
