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

  (** Every logical object is backed by an immutable physical allocation
      receipt. The receipt remains available after the object is quarantined. *)
  Definition heap_provenance (h : Heap) : iProp Σ :=
    [∗ map] b ↦ o ∈ h,
      ∃ reserved : Z * Z, allocator_allocation b (alloc_object_end o) reserved.

  Global Instance heap_provenance_persistent h : Persistent (heap_provenance h).
  Proof. apply _. Qed.

  Lemma heap_provenance_quarantine h b :
    heap_provenance h -∗ heap_provenance (heap_quarantine h b).
  Proof.
    iIntros "#Hprovenance".
    iApply big_sepM_intro.
    iIntros (c o' Hlookup). iModIntro.
    destruct (decide (c = b)) as [->|Hne].
    - destruct (h !! b) as [o|] eqn:Hb.
      + rewrite (heap_quarantine_lookup h b o Hb) in Hlookup.
        injection Hlookup as <-.
        iDestruct (big_sepM_lookup with "Hprovenance") as (reserved) "#Hreceipt";
          first exact Hb.
        iExists reserved. simpl. iFrame "#".
      + rewrite /heap_quarantine fin_maps.lookup_alter_eq Hb in Hlookup.
        discriminate.
    - rewrite (heap_quarantine_lookup_ne h b c (λ Heq, Hne (eq_sym Heq))) in Hlookup.
      iDestruct (big_sepM_lookup with "Hprovenance") as (reserved) "#Hreceipt";
        first exact Hlookup.
      iExists reserved. iFrame "#".
  Qed.

  (** The world holds the right to free of every quarantined object. *)
  Definition heap_quarantine_rights (h : Heap) : iProp Σ :=
    [∗ map] b ↦ o ∈ h,
      match alloc_object_status o with
      | AllocObjectQuarantined => free_right b
      | AllocObjectLive => emp
      end.

  Global Instance heap_quarantine_rights_timeless h :
    Timeless (heap_quarantine_rights h).
  Proof.
    apply big_sepM_timeless. intros b o. destruct (alloc_object_status o); apply _.
  Qed.

  Lemma heap_quarantine_rights_empty : ⊢ heap_quarantine_rights ∅.
  Proof. by rewrite /heap_quarantine_rights big_sepM_empty. Qed.

  (** A freshly allocated object is live: the rights are unchanged. *)
  Lemma heap_quarantine_rights_allocate h b e :
    h !! b = None ->
    heap_quarantine_rights h ⊣⊢ heap_quarantine_rights (heap_allocate h b e).
  Proof.
    intros Hb. rewrite /heap_quarantine_rights /heap_allocate big_sepM_insert //=.
    by rewrite left_id.
  Qed.

  (** Quarantining a live object moves its right to free into the world. *)
  Lemma heap_quarantine_rights_quarantine h b o :
    h !! b = Some o ->
    alloc_object_status o = AllocObjectLive ->
    heap_quarantine_rights h ∗ free_right b ⊣⊢
    heap_quarantine_rights (heap_quarantine h b).
  Proof.
    intros Hb Hlive.
    rewrite /heap_quarantine_rights /heap_quarantine.
    rewrite (big_sepM_delete _ h b o) //.
    rewrite (big_sepM_delete _ (alter _ b h) b); last first.
    { by rewrite fin_maps.lookup_alter_eq Hb. }
    rewrite delete_alter Hlive /= left_id decide_True // comm //.
  Qed.

  (** Quarantining any base with its right to free: the right is either moved
      into the world (live object), contradicts the world (already quarantined)
      or is dropped (no object). *)
  Lemma heap_quarantine_rights_quarantine_right h b :
    heap_quarantine_rights h -∗ free_right b -∗
    heap_quarantine_rights (heap_quarantine h b).
  Proof.
    iIntros "Hrights Hright".
    destruct (h !! b) as [o|] eqn:Hb.
    - destruct (alloc_object_status o) eqn:Hstatus.
      + iApply (heap_quarantine_rights_quarantine h b o Hb Hstatus). iFrame.
      + iDestruct (big_sepM_lookup with "Hrights") as "Hb"; first exact Hb.
        rewrite Hstatus.
        iDestruct (free_right_exclusive with "Hb Hright") as %[].
    - rewrite /heap_quarantine fin_maps.alter_id; first iExact "Hrights".
      intros o Ho. by rewrite Hb in Ho.
  Qed.

  (** A right to free held outside the world belongs to a live object. *)
  Lemma heap_quarantine_rights_free_right_live h b o :
    h !! b = Some o ->
    heap_quarantine_rights h -∗ free_right b -∗
    ⌜alloc_object_status o = AllocObjectLive⌝.
  Proof.
    iIntros (Hb) "Hrights Hright".
    iDestruct (big_sepM_lookup with "Hrights") as "Hb"; first exact Hb.
    destruct (alloc_object_status o); first done.
    iDestruct (free_right_exclusive with "Hb Hright") as %[].
  Qed.

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

Lemma free_heap_quarantine_status_outside `{HeapRegion} h b e :
  heap_wf h ->
  h !! b = Some (MkAllocObject b e AllocObjectLive) ->
  ∀ a, a ∉ finz.seq_between b e ->
    heap_addr_status h a =
    heap_addr_status (heap_quarantine h b) a.
Proof.
  intros Hwf Hb a Houtside.
  rewrite /heap_addr_status.
  destruct (is_heap_address a) eqn:Ha; last reflexivity.
  destruct (heap_lookup_addr h a) as [ [c o] |] eqn:Hlookup.
  - apply heap_lookup_addr_sound in Hlookup as [Hc Hcontains].
    assert (c <> b) as Hcne.
    { intro Heq. subst c. rewrite Hb in Hc. injection Hc as <-.
      apply Houtside. apply elem_of_finz_seq_between.
      unfold alloc_object_contains in Hcontains. simpl in Hcontains.
      exact Hcontains. }
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
      injection Hc as <-. exfalso. apply Houtside.
      apply elem_of_finz_seq_between.
      unfold alloc_object_contains in Hcontains. simpl in Hcontains.
      exact Hcontains.
    + rewrite heap_quarantine_lookup_ne in Hc; [|congruence].
      exfalso. exact (Hnone c o Hc Hcontains).
Qed.
