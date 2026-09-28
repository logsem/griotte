From iris.proofmode Require Import proofmode.
From griotte Require Export heap_std allocator_resources.

(** Outside the physical heap, ordinary region resources are unchanged.
    An unrecorded heap address cannot have an active shared resource. *)
Definition heap_addr_status `{HeapRegion} (W_heap : Heap) (a : Addr) : option AllocObjectStatus :=
  if is_heap_address a then
    alloc_object_status ∘ snd <$> heap_lookup_addr W_heap a
  else Some AllocObjectLive.

Definition heap_addr_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  heap_addr_status W_heap a = Some AllocObjectLive.

(** A closed compartment world records every address of a quarantined object.
    Live objects may remain outside this compartment's standard world. *)
Definition heap_quarantine_covered `{HeapRegion} {B : Type}
    (W_heap : Heap) (W_std : gmap Addr B) : Prop :=
  ∀ a, heap_addr_status W_heap a = Some AllocObjectQuarantined →
    a ∈ dom W_std.

Lemma heap_quarantine_covered_empty `{HeapRegion} {B : Type} :
  heap_quarantine_covered (B:=B) ∅ ∅.
Proof.
  intros a Hstatus.
  rewrite /heap_addr_status /= in Hstatus.
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

  Definition heap_addr_resource (W_heap : Heap) (a : Addr) (P : iProp Σ) : iProp Σ :=
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

  Lemma heap_addr_resource_status W_heap a P :
    heap_addr_resource W_heap a P =
    (match heap_addr_status W_heap a with
     | Some AllocObjectLive => P
     | Some AllocObjectQuarantined => reclaim_token a
     | None => False
     end)%I.
  Proof.
    rewrite /heap_addr_resource /heap_addr_status.
    destruct (is_heap_address a); last done.
    destruct (heap_lookup_addr W_heap a) as [[base obj]|]; done.
  Qed.

  Global Instance heap_addr_resource_ne W_heap a : NonExpansive (heap_addr_resource W_heap a).
  Proof. intros n P Q HPQ. rewrite !heap_addr_resource_status.
    destruct (heap_addr_status W_heap a) as [[]|]; done. Qed.

  Lemma heap_addr_resource_live W_heap a P :
    heap_addr_live W_heap a -> heap_addr_resource W_heap a P = P.
  Proof. intros Ha. by rewrite heap_addr_resource_status Ha. Qed.

  Lemma heap_addr_resource_live_elim W_heap a P :
    heap_addr_live W_heap a -> heap_addr_resource W_heap a P -∗ P.
  Proof. intros Ha. rewrite (heap_addr_resource_live _ _ _ Ha). iIntros "$". Qed.

  Lemma heap_addr_resource_live_intro W_heap a P :
    heap_addr_live W_heap a -> P -∗ heap_addr_resource W_heap a P.
  Proof. intros Ha. rewrite (heap_addr_resource_live _ _ _ Ha). iIntros "$". Qed.


  Lemma heap_addr_resource_mono W_heap a P Q :
    (P -∗ Q) -∗ heap_addr_resource W_heap a P -∗ heap_addr_resource W_heap a Q.
  Proof.
    rewrite !heap_addr_resource_status. destruct (heap_addr_status W_heap a) as [[]|];
      iIntros "HPQ HP"; try done. by iApply "HPQ".
  Qed.
End heap_region.

Lemma heap_addr_live_nonheap `{HeapRegion} W_heap a :
  is_heap_address a = false -> heap_addr_live W_heap a.
Proof. intros Ha. by rewrite /heap_addr_live /heap_addr_status Ha. Qed.

Lemma heap_addr_live_lookup `{HeapRegion} W_heap a b o :
  heap_lookup_addr W_heap a = Some (b,o) ->
  alloc_object_status o = AllocObjectLive -> heap_addr_live W_heap a.
Proof.
  intros Ha Ho. rewrite /heap_addr_live /heap_addr_status.
  destruct (is_heap_address a); last done. by rewrite Ha /= Ho.
Qed.

Lemma hts_heap_quarantine_single_status `{HeapRegion} h b e :
    heap_wf h ->
    (b + 1)%a = Some e ->
    h !! b = Some (MkAllocObject b e AllocObjectLive) ->
    forall a, a <> b ->
      heap_addr_status h a = heap_addr_status (heap_quarantine h b) a.
Proof.
  intros Hwf Hsucc Hb a Hne.
    rewrite /heap_addr_status.
    destruct (is_heap_address a) eqn:Ha; last reflexivity.
    destruct (heap_lookup_addr h a) as [ [c o] |] eqn:Hlookup.
    - apply heap_lookup_addr_sound in Hlookup as [Hc Hcontains].
      assert (c <> b) as Hcne.
      { intro Heq. subst c. rewrite Hb in Hc. injection Hc as <-.
        apply Hne. unfold alloc_object_contains in Hcontains.
        simpl in Hcontains. solve_addr. }
      assert (heap_lookup_addr (heap_quarantine h b) a = Some (c,o))
        as Hnew.
      { eapply heap_lookup_addr_complete.
        - apply heap_quarantine_wf. exact Hwf.
        - rewrite heap_quarantine_lookup_ne; [exact Hc|congruence].
        - exact Hcontains. }
      rewrite Hnew. reflexivity.
    - pose proof (proj1 (heap_lookup_addr_none h a Hwf) Hlookup) as Hnone.
      destruct (heap_lookup_addr (heap_quarantine h b) a)
        as [ [c o] |] eqn:Hnew; last reflexivity.
      apply heap_lookup_addr_sound in Hnew as [Hc Hcontains].
      destruct (decide (c = b)) as [->|Hcne].
      + rewrite (heap_quarantine_lookup h b _ Hb) in Hc.
        injection Hc as <-. exfalso. apply Hne.
        unfold alloc_object_contains in Hcontains.
        simpl in Hcontains. solve_addr.
      + rewrite heap_quarantine_lookup_ne in Hc; [|congruence].
        exfalso. exact (Hnone c o Hc Hcontains).
  Qed.

