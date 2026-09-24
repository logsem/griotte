From stdpp Require Import gmap list.
From griotte Require Export addresses.

(** Allocation objects describe payloads, not allocator headers or free cells.
    The original base is the identity and is never reused. The map key agrees
    with the base recorded in the object. *)
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

Definition Heap := gmap Addr AllocObject.

Definition alloc_object_contains (b : Addr) (o : AllocObject) (a : Addr) : Prop :=
  (b <= a < alloc_object_end o)%a.

Global Instance alloc_object_contains_dec b o a :
  Decision (alloc_object_contains b o a).
Proof. unfold alloc_object_contains. apply _. Defined.

Definition heap_entry_valid (W_heap : Heap) (b : Addr) (o : AllocObject) : Prop :=
  b = alloc_object_base o /\ (b < alloc_object_end o)%a /\
  ∀ b' o' a, W_heap !! b' = Some o' ->
    alloc_object_contains b o a -> alloc_object_contains b' o' a -> b = b'.

Definition heap_wf (W_heap : Heap) : Prop :=
  ∀ b o, W_heap !! b = Some o -> heap_entry_valid W_heap b o.

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

Lemma heap_entry_valid_future W_heap W_heap' b o o' :
  related_sts_heap_std W_heap W_heap' -> W_heap !! b = Some o ->
  W_heap' !! b = Some o' -> heap_entry_valid W_heap b o -> heap_entry_valid W_heap' b o'.
Proof.
  intros [Hkeep Hnew] Hb Hb' (Hbase & Hnonempty & Hdisj).
  destruct (Hkeep b o Hb) as (ox & Hox & Hbase' & He & Hs).
  simplify_eq. split; first congruence. split; first by rewrite -He.
  intros c oc a Hc Ha Hca.
  destruct (W_heap !! c) as [old|] eqn:Hc0.
  - destruct (Hkeep c old Hc0) as (oc' & Hoc' & Hbc & Hec & Hsc).
    simplify_eq. eapply Hdisj; eauto.
    + unfold alloc_object_contains in *. by rewrite He.
    + unfold alloc_object_contains in *. by rewrite Hec.
  - destruct (Hnew c oc Hc0 Hc) as (_ & _ & Hfresh).
    symmetry. eapply Hfresh; eauto.
Qed.

Lemma related_sts_heap_std_trans W_heap1 W_heap2 W_heap3 :
  related_sts_heap_std W_heap1 W_heap2 -> related_sts_heap_std W_heap2 W_heap3 ->
  related_sts_heap_std W_heap1 W_heap3.
Proof.
  intros H12 H23. destruct H12 as [Hkeep12 Hnew12].
  destruct H23 as [Hkeep23 Hnew23]. split.
  - intros b o Hb. destruct (Hkeep12 b o Hb) as (o2 & Hb2 & Ho2).
    destruct (Hkeep23 b o2 Hb2) as (o3 & Hb3 & Ho3).
    exists o3. split; eauto using alloc_object_future_trans.
  - intros b o Hb Hb3. destruct (W_heap2 !! b) as [o2|] eqn:Hb2.
    + eapply heap_entry_valid_future; eauto. split; assumption.
    + eauto.
Qed.

Lemma related_sts_heap_std_wf W_heap W_heap' :
  related_sts_heap_std W_heap W_heap' -> heap_wf W_heap -> heap_wf W_heap'.
Proof.
  intros Hrel Hwf b o Hb. destruct (W_heap !! b) as [old|] eqn:Hb0.
  - eapply heap_entry_valid_future; eauto.
  - apply (proj2 Hrel b o Hb0 Hb).
Qed.

Lemma related_sts_heap_std_empty W_heap :
  heap_wf W_heap -> related_sts_heap_std ∅ W_heap.
Proof.
  intros Hwf. split.
  - intros b o Hb. rewrite lookup_empty in Hb. discriminate.
  - intros b o _ Hb. by apply Hwf.
Qed.

Lemma related_sts_heap_std_dom W_heap W_heap' :
  related_sts_heap_std W_heap W_heap' -> dom W_heap ⊆ dom W_heap'.
Proof.
  intros [Hkeep _] b. rewrite !elem_of_dom.
  intros [o Hb]. destruct (Hkeep b o Hb) as (o' & Hb' & _). eauto.
Qed.

Lemma related_sts_heap_std_quarantined W_heap W_heap' b e :
  related_sts_heap_std W_heap W_heap' -> W_heap !! b = Some (MkAllocObject b e AllocObjectQuarantined) ->
  W_heap' !! b = Some (MkAllocObject b e AllocObjectQuarantined).
Proof.
  intros [Hkeep _] Hb. destruct (Hkeep _ _ Hb) as ([b' e' s'] & Hb' & Hb_eq & He & Hs).
  cbn in *. specialize (Hs eq_refl). by subst.
Qed.

Definition heap_lookup_addr (W_heap : Heap) (a : Addr) : option (Addr * AllocObject) :=
  snd <$> list_find (λ bo, alloc_object_contains bo.1 bo.2 a) (map_to_list W_heap).

Lemma heap_lookup_addr_sound W_heap a b o :
  heap_lookup_addr W_heap a = Some (b,o) ->
  W_heap !! b = Some o /\ alloc_object_contains b o a.
Proof.
  rewrite /heap_lookup_addr. intros Hfind.
  apply fmap_Some in Hfind as ([i [b' o']] & Hfind & Heq).
  cbn in Heq. simplify_eq. apply list_find_Some in Hfind as [Hlookup [Ha _]].
  split; last done. apply elem_of_map_to_list. eapply list_elem_of_lookup_2; eauto.
Qed.

Lemma heap_lookup_addr_complete W_heap a b o :
  heap_wf W_heap -> W_heap !! b = Some o -> alloc_object_contains b o a ->
  heap_lookup_addr W_heap a = Some (b,o).
Proof.
  intros Hwf Hb Ha.
  destruct (list_find_elem_of (λ bo : Addr * AllocObject,
    alloc_object_contains bo.1 bo.2 a) (map_to_list W_heap) (b,o))
    as [[i [b' o']] Hfind]; [by apply elem_of_map_to_list|exact Ha|].
  rewrite /heap_lookup_addr Hfind /=.
  apply list_find_Some in Hfind as [Hlookup [Ha' _]].
  assert (W_heap !! b' = Some o') as Hb'.
  { apply elem_of_map_to_list. eapply list_elem_of_lookup_2; eauto. }
  destruct (Hwf b o Hb) as (_ & _ & Hunique).
  assert (b = b') by (eapply Hunique; eauto). simplify_eq. done.
Qed.

Lemma heap_lookup_addr_none W_heap a :
  heap_wf W_heap ->
  (heap_lookup_addr W_heap a = None <-> ∀ b o, W_heap !! b = Some o -> ~ alloc_object_contains b o a).
Proof.
  intros Hwf. split.
  - intros Hnone b o Hb Ha. rewrite (heap_lookup_addr_complete W_heap a b o Hwf Hb Ha) in Hnone.
    discriminate.
  - intros Hnone. destruct (heap_lookup_addr W_heap a) as [[b o]|] eqn:Hfind; last done.
    apply heap_lookup_addr_sound in Hfind as [Hb Ha]. exfalso. exact (Hnone b o Hb Ha).
Qed.

Lemma heap_lookup_addr_future W_heap W_heap' a b o :
  heap_wf W_heap' -> related_sts_heap_std W_heap W_heap' -> heap_lookup_addr W_heap a = Some (b,o) ->
  ∃ o', heap_lookup_addr W_heap' a = Some (b,o') /\ alloc_object_future o o'.
Proof.
  intros Hwf [Hkeep _] Hfind. apply heap_lookup_addr_sound in Hfind as [Hb Ha].
  destruct (Hkeep b o Hb) as (o' & Hb' & Ho').
  exists o'. split; last done. apply heap_lookup_addr_complete; auto.
  unfold alloc_object_contains in *. by rewrite -(proj1 (proj2 Ho')).
Qed.

Definition heap_allocate (W_heap : Heap) (b e : Addr) : Heap :=
  <[b := MkAllocObject b e AllocObjectLive]> W_heap.

Definition heap_fresh (W_heap : Heap) (b e : Addr) : Prop :=
  W_heap !! b = None /\ (b < e)%a /\
  ∀ c o a, W_heap !! c = Some o -> (b <= a < e)%a -> ~ alloc_object_contains c o a.

Lemma heap_allocate_future W_heap b e :
  heap_fresh W_heap b e -> related_sts_heap_std W_heap (heap_allocate W_heap b e).
Proof.
  intros [Hb [Hbe Hdisj]]. split.
  - intros c o Hc. exists o. split; last apply alloc_object_future_refl.
    rewrite /heap_allocate fin_maps.lookup_insert_ne; [exact Hc|intros ->; congruence].
  - intros c o Hc Hnew. rewrite /heap_allocate in Hnew.
    apply fin_maps.lookup_insert_Some in Hnew as [[-> <-]|[_ Hcontra]]; last by rewrite Hc in Hcontra.
    split; first done. split; first done. intros d oc a Hc' Ha Hca.
    rewrite /heap_allocate in Hc'.
    apply fin_maps.lookup_insert_Some in Hc' as [[-> <-]|[_ Hc']]; first done.
    exfalso. eapply Hdisj; eauto.
Qed.

Lemma heap_allocate_wf W_heap b e :
  heap_wf W_heap -> heap_fresh W_heap b e -> heap_wf (heap_allocate W_heap b e).
Proof. eauto using related_sts_heap_std_wf, heap_allocate_future. Qed.

(** Adjusting the one object entry changes the status of its entire interval. *)
Definition heap_quarantine (W_heap : Heap) (b : Addr) : Heap :=
  alter (λ o, MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined) b W_heap.

Definition heap_quarantine_addr (W_heap : Heap) (a : Addr) : option Heap :=
  (λ bo, heap_quarantine W_heap bo.1) <$> heap_lookup_addr W_heap a.

Lemma heap_quarantine_lookup W_heap b o :
  W_heap !! b = Some o ->
  heap_quarantine W_heap b !! b = Some (MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
Proof. intros Hb. by rewrite /heap_quarantine fin_maps.lookup_alter_eq Hb. Qed.

Lemma heap_quarantine_lookup_ne W_heap b c :
  b ≠ c -> heap_quarantine W_heap b !! c = W_heap !! c.
Proof. intros Hne. by rewrite /heap_quarantine fin_maps.lookup_alter_ne. Qed.

Lemma heap_quarantine_future W_heap b : related_sts_heap_std W_heap (heap_quarantine W_heap b).
Proof.
  split.
  - intros c o Hc. destruct (decide (b = c)) as [->|Hne].
    + exists (MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
      split; first by apply heap_quarantine_lookup. repeat split; done.
    + exists o. rewrite heap_quarantine_lookup_ne; last done.
      split; auto using alloc_object_future_refl.
  - intros c o Hc Hnew. destruct (decide (b = c)) as [->|Hne].
    + rewrite /heap_quarantine fin_maps.lookup_alter_eq Hc /= in Hnew. discriminate.
    + rewrite heap_quarantine_lookup_ne // Hc in Hnew. discriminate.
Qed.

Lemma heap_quarantine_wf W_heap b : heap_wf W_heap -> heap_wf (heap_quarantine W_heap b).
Proof. eauto using related_sts_heap_std_wf, heap_quarantine_future. Qed.

Lemma heap_quarantine_idempotent W_heap b :
  heap_quarantine (heap_quarantine W_heap b) b = heap_quarantine W_heap b.
Proof.
  apply map_eq. intros c. destruct (decide (b = c)) as [->|Hne].
  - rewrite /heap_quarantine !fin_maps.lookup_alter_eq. destruct (W_heap !! c) eqn:Hc; by rewrite Hc.
  - by rewrite !heap_quarantine_lookup_ne.
Qed.

Lemma heap_quarantine_addr_whole_object W_heap a b o a' :
  heap_wf W_heap -> heap_lookup_addr W_heap a = Some (b,o) ->
  alloc_object_contains b o a' ->
  heap_quarantine_addr W_heap a = Some (heap_quarantine W_heap b) /\
  heap_lookup_addr (heap_quarantine W_heap b) a' =
    Some (b, MkAllocObject (alloc_object_base o) (alloc_object_end o) AllocObjectQuarantined).
Proof.
  intros Hwf Hfind Ha'. split; first by rewrite /heap_quarantine_addr Hfind.
  apply heap_lookup_addr_sound in Hfind as [Hb Ha].
  apply heap_lookup_addr_complete; eauto using heap_quarantine_wf, heap_quarantine_lookup.
Qed.

Lemma heap_lookup_addr_base W_heap a b o :
  heap_wf W_heap -> heap_lookup_addr W_heap a = Some (b,o) ->
  b = alloc_object_base o.
Proof.
  intros Hwf Hfind. apply heap_lookup_addr_sound in Hfind as [Hb _].
  exact (proj1 (Hwf b o Hb)).
Qed.

Lemma heap_lookup_original_base W_heap b o :
  heap_wf W_heap -> W_heap !! b = Some o ->
  heap_lookup_addr W_heap b = Some (b,o).
Proof.
  intros Hwf Hb. apply heap_lookup_addr_complete; auto.
  destruct (Hwf b o Hb) as (_ & Hnonempty & _).
  unfold alloc_object_contains. split; [reflexivity|exact Hnonempty].
Qed.

Lemma heap_lookup_exclusive_end W_heap b o :
  heap_lookup_addr W_heap (alloc_object_end o) ≠ Some (b,o).
Proof.
  intros Hfind. apply heap_lookup_addr_sound in Hfind as [_ [_ Hlt]].
  unfold finz.lt in Hlt. lia.
Qed.

Lemma heap_fresh_no_reuse W_heap b e o :
  W_heap !! b = Some o -> ~ heap_fresh W_heap b e.
Proof. intros Hb [Hnone _]. rewrite Hb in Hnone. discriminate. Qed.

Lemma heap_quarantine_addr_none W_heap a :
  heap_lookup_addr W_heap a = None -> heap_quarantine_addr W_heap a = None.
Proof. intros Hnone. by rewrite /heap_quarantine_addr Hnone. Qed.

Lemma alloc_object_no_reverse b e :
  ~ alloc_object_future (MkAllocObject b e AllocObjectQuarantined)
      (MkAllocObject b e AllocObjectLive).
Proof. intros (_ & _ & Hs). discriminate (Hs eq_refl). Qed.
