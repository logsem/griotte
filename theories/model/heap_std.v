From stdpp Require Import gmap list.
From griotte Require Export addresses region_keys.

(** Allocation objects describe payloads, not allocator headers or free addresses.
    The heap is keyed by allocation identifier; each object records its range.
    Without address reuse, [heap_wf] keeps the ranges of a world disjoint, so
    an address belongs to at most one object. *)
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

Definition heap_entry_valid (W_heap : Heap) (ι : AId) (o : AllocObject) : Prop :=
  (alloc_object_base o < alloc_object_end o)%a /\
  ∀ ι' o' a, W_heap !! ι' = Some o' ->
    alloc_object_contains o a -> alloc_object_contains o' a -> ι = ι'.

Definition heap_wf (W_heap : Heap) : Prop :=
  ∀ ι o, W_heap !! ι = Some o -> heap_entry_valid W_heap ι o.

Definition alloc_object_future (o o' : AllocObject) : Prop :=
  alloc_object_base o = alloc_object_base o' /\
  alloc_object_end o = alloc_object_end o' /\
  (alloc_object_status o = AllocObjectQuarantined ->
   alloc_object_status o' = AllocObjectQuarantined).

(** Both public and private futures use this relation. A fresh object may
    already be quarantined in a future reached by several operations. *)
Definition related_sts_heap_std (W_heap W_heap' : Heap) : Prop :=
  (∀ b o, W_heap !! b = Some o ->
    ∃ o', W_heap' !! b = Some o' /\ alloc_object_future o o') /\
  (∀ b o, W_heap !! b = None -> W_heap' !! b = Some o -> heap_entry_valid W_heap' b o).

Lemma heap_wf_empty : heap_wf ∅.
Proof. intros b o. rewrite lookup_empty. discriminate. Qed.

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

Lemma heap_entry_valid_future W_heap W_heap' ι o o' :
  related_sts_heap_std W_heap W_heap' -> W_heap !! ι = Some o ->
  W_heap' !! ι = Some o' -> heap_entry_valid W_heap ι o -> heap_entry_valid W_heap' ι o'.
Proof.
  intros [Hkeep Hnew] Hι Hι' (Hnonempty & Hdisj).
  destruct (Hkeep ι o Hι) as (ox & Hox & Hbase' & He & Hs).
  simplify_eq. split; first by rewrite -Hbase' -He.
  intros κ oc a Hκ Ha Hκa.
  destruct (W_heap !! κ) as [old|] eqn:Hκ0.
  - destruct (Hkeep κ old Hκ0) as (oc' & Hoc' & Hbc & Hec & Hsc).
    simplify_eq. eapply Hdisj; eauto.
    + unfold alloc_object_contains in *. by rewrite Hbase' He.
    + unfold alloc_object_contains in *. by rewrite Hbc Hec.
  - destruct (Hnew κ oc Hκ0 Hκ) as (_ & Hfresh).
    symmetry. eapply Hfresh; eauto.
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
    + eapply heap_entry_valid_future; eauto. split; assumption.
    + eauto.
Qed.

Lemma related_sts_heap_std_wf W_heap W_heap' :
  related_sts_heap_std W_heap W_heap' -> heap_wf W_heap -> heap_wf W_heap'.
Proof.
  intros Hrel Hwf ι o Hι. destruct (W_heap !! ι) as [old|] eqn:Hι0.
  - eapply heap_entry_valid_future; eauto.
  - apply (proj2 Hrel ι o Hι0 Hι).
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

(** The address lookup, used by the logical relation until words carry their
    allocation identifier. It is well-defined under [heap_wf]. *)
Definition heap_lookup_addr (W_heap : Heap) (a : Addr) : option (AId * AllocObject) :=
  snd <$> list_find (λ io, alloc_object_contains io.2 a) (map_to_list W_heap).

Lemma heap_lookup_addr_sound W_heap a ι o :
  heap_lookup_addr W_heap a = Some (ι,o) ->
  W_heap !! ι = Some o /\ alloc_object_contains o a.
Proof.
  rewrite /heap_lookup_addr. intros Hfind.
  apply fmap_Some in Hfind as ([i [ι' o']] & Hfind & Heq).
  cbn in Heq. simplify_eq. apply list_find_Some in Hfind as [Hlookup [Ha _]].
  split; last done. apply elem_of_map_to_list. eapply list_elem_of_lookup_2; eauto.
Qed.

Lemma heap_lookup_addr_complete W_heap a ι o :
  heap_wf W_heap -> W_heap !! ι = Some o -> alloc_object_contains o a ->
  heap_lookup_addr W_heap a = Some (ι,o).
Proof.
  intros Hwf Hι Ha.
  destruct (list_find_elem_of (λ io : AId * AllocObject,
    alloc_object_contains io.2 a) (map_to_list W_heap) (ι,o))
    as [[i [ι' o']] Hfind]; [by apply elem_of_map_to_list|exact Ha|].
  rewrite /heap_lookup_addr Hfind /=.
  apply list_find_Some in Hfind as [Hlookup [Ha' _]].
  assert (W_heap !! ι' = Some o') as Hι'.
  { apply elem_of_map_to_list. eapply list_elem_of_lookup_2; eauto. }
  destruct (Hwf ι o Hι) as (_ & Hunique).
  assert (ι = ι') by (eapply Hunique; eauto). simplify_eq. done.
Qed.

Lemma heap_lookup_addr_is_Some W_heap a ι o :
  W_heap !! ι = Some o -> alloc_object_contains o a -> is_Some (heap_lookup_addr W_heap a).
Proof.
  intros Hι Ha. rewrite /heap_lookup_addr.
  destruct (list_find _ _) as [ [i [κ o'] ] |] eqn:Hfind; first by eexists.
  apply list_find_None in Hfind. rewrite list.Forall_forall in Hfind.
  exfalso. apply (Hfind (ι,o)); last done.
  by apply elem_of_map_to_list.
Qed.

Lemma heap_lookup_addr_none W_heap a :
  heap_wf W_heap ->
  (heap_lookup_addr W_heap a = None <-> ∀ ι o, W_heap !! ι = Some o -> ~ alloc_object_contains o a).
Proof.
  intros Hwf. split.
  - intros Hnone ι o Hι Ha. rewrite (heap_lookup_addr_complete W_heap a ι o Hwf Hι Ha) in Hnone.
    discriminate.
  - intros Hnone. destruct (heap_lookup_addr W_heap a) as [[ι o]|] eqn:Hfind; last done.
    apply heap_lookup_addr_sound in Hfind as [Hι Ha]. exfalso. exact (Hnone ι o Hι Ha).
Qed.

Lemma heap_lookup_addr_future W_heap W_heap' a ι o :
  heap_wf W_heap' -> related_sts_heap_std W_heap W_heap' -> heap_lookup_addr W_heap a = Some (ι,o) ->
  ∃ o', heap_lookup_addr W_heap' a = Some (ι,o') /\ alloc_object_future o o'.
Proof.
  intros Hwf [Hkeep _] Hfind. apply heap_lookup_addr_sound in Hfind as [Hι Ha].
  destruct (Hkeep ι o Hι) as (o' & Hι' & Ho').
  exists o'. split; last done. apply heap_lookup_addr_complete; auto.
  destruct Ho' as (Hb & He & _).
  unfold alloc_object_contains in *. by rewrite -Hb -He.
Qed.

(** Two addresses of the same object find the same entry. *)
Lemma heap_lookup_addr_same_object W_heap a a' ι o :
  heap_wf W_heap -> heap_lookup_addr W_heap a = Some (ι,o) ->
  alloc_object_contains o a' -> heap_lookup_addr W_heap a' = Some (ι,o).
Proof.
  intros Hwf Hfind Ha'. apply heap_lookup_addr_sound in Hfind as [Hι _].
  by apply heap_lookup_addr_complete.
Qed.

Definition heap_allocate (W_heap : Heap) (ι : AId) (b e : Addr) : Heap :=
  <[ι := MkAllocObject b e AllocObjectLive]> W_heap.

Definition heap_fresh (W_heap : Heap) (ι : AId) (b e : Addr) : Prop :=
  W_heap !! ι = None /\ (b < e)%a /\
  ∀ κ o a, W_heap !! κ = Some o -> (b <= a < e)%a -> ~ alloc_object_contains o a.

Lemma heap_allocate_future W_heap ι b e :
  heap_fresh W_heap ι b e -> related_sts_heap_std W_heap (heap_allocate W_heap ι b e).
Proof.
  intros [Hι [Hbe Hdisj]]. split.
  - intros κ o Hκ. exists o. split; last apply alloc_object_future_refl.
    rewrite /heap_allocate fin_maps.lookup_insert_ne; [exact Hκ|intros ->; congruence].
  - intros κ o Hκ Hnew. rewrite /heap_allocate in Hnew.
    apply fin_maps.lookup_insert_Some in Hnew as [[-> <-]|[_ Hcontra]]; last by rewrite Hκ in Hcontra.
    split; first done. intros κ' oc a Hκ' Ha Hca.
    rewrite /heap_allocate in Hκ'.
    apply fin_maps.lookup_insert_Some in Hκ' as [[-> <-]|[_ Hκ']]; first done.
    exfalso. eapply Hdisj; eauto.
Qed.

Lemma heap_allocate_wf W_heap ι b e :
  heap_wf W_heap -> heap_fresh W_heap ι b e -> heap_wf (heap_allocate W_heap ι b e).
Proof. eauto using related_sts_heap_std_wf, heap_allocate_future. Qed.

(** Adjusting the one object entry changes the status of its entire interval. *)
Definition heap_quarantine (W_heap : Heap) (ι : AId) : Heap :=
  alter (λ o, MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined) ι W_heap.

Definition heap_quarantine_addr (W_heap : Heap) (a : Addr) : option Heap :=
  (λ io, heap_quarantine W_heap io.1) <$> heap_lookup_addr W_heap a.

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

Lemma heap_quarantine_wf W_heap ι : heap_wf W_heap -> heap_wf (heap_quarantine W_heap ι).
Proof. eauto using related_sts_heap_std_wf, heap_quarantine_future. Qed.

Lemma heap_quarantine_idempotent W_heap ι :
  heap_quarantine (heap_quarantine W_heap ι) ι = heap_quarantine W_heap ι.
Proof.
  apply map_eq. intros κ. destruct (decide (ι = κ)) as [->|Hne].
  - rewrite /heap_quarantine !fin_maps.lookup_alter_eq. destruct (W_heap !! κ) eqn:Hκ; by rewrite Hκ.
  - by rewrite !heap_quarantine_lookup_ne.
Qed.

Lemma heap_quarantine_dom W_heap ι : dom (heap_quarantine W_heap ι) = dom W_heap.
Proof. by rewrite /heap_quarantine dom_alter_L. Qed.

Lemma heap_quarantine_addr_whole_object W_heap a ι o a' :
  heap_wf W_heap -> heap_lookup_addr W_heap a = Some (ι,o) ->
  alloc_object_contains o a' ->
  heap_quarantine_addr W_heap a = Some (heap_quarantine W_heap ι) /\
  heap_lookup_addr (heap_quarantine W_heap ι) a' =
    Some (ι, MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
Proof.
  intros Hwf Hfind Ha'. split; first by rewrite /heap_quarantine_addr Hfind.
  apply heap_lookup_addr_sound in Hfind as [Hι Ha].
  apply heap_lookup_addr_complete; eauto using heap_quarantine_wf, heap_quarantine_lookup.
Qed.

(** The lookup returns the object containing the address. *)
Lemma heap_lookup_addr_base W_heap a ι o :
  heap_lookup_addr W_heap a = Some (ι,o) ->
  W_heap !! ι = Some o /\ (alloc_object_base o <= a < alloc_object_end o)%a.
Proof. apply heap_lookup_addr_sound. Qed.

(** The lookup at the base of an object returns that object. *)
Lemma heap_lookup_original_base W_heap ι o :
  heap_wf W_heap -> W_heap !! ι = Some o ->
  heap_lookup_addr W_heap (alloc_object_base o) = Some (ι,o).
Proof.
  intros Hwf Hι. apply heap_lookup_addr_complete; auto.
  destruct (Hwf ι o Hι) as (Hnonempty & _).
  unfold alloc_object_contains. split; [reflexivity|exact Hnonempty].
Qed.

Lemma heap_lookup_exclusive_end W_heap ι o :
  heap_lookup_addr W_heap (alloc_object_end o) ≠ Some (ι,o).
Proof.
  intros Hfind. apply heap_lookup_addr_sound in Hfind as [_ [_ Hlt]].
  unfold finz.lt in Hlt. lia.
Qed.

Lemma heap_fresh_no_reuse W_heap ι b e o :
  W_heap !! ι = Some o -> ~ heap_fresh W_heap ι b e.
Proof. intros Hι [Hnone _]. rewrite Hι in Hnone. discriminate. Qed.

Lemma heap_quarantine_addr_none W_heap a :
  heap_lookup_addr W_heap a = None -> heap_quarantine_addr W_heap a = None.
Proof. intros Hnone. by rewrite /heap_quarantine_addr Hnone. Qed.

Lemma alloc_object_no_reverse b e :
  ~ alloc_object_future (MkAllocObject b e AllocObjectQuarantined)
      (MkAllocObject b e AllocObjectLive).
Proof. intros (_ & _ & Hs). discriminate (Hs eq_refl). Qed.
