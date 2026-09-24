From griotte Require Export heap_std.
From iris.algebra Require Import auth agree gmap gset.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.

Definition heap_bounds (W_heap : Heap) : gmap Addr (Addr * Addr) :=
  (λ o, (alloc_object_base o, alloc_object_end o)) <$> W_heap.
Definition heap_quarantined (W_heap : Heap) : gset Addr :=
  dom (filter (λ bo : Addr * AllocObject,
    alloc_object_status bo.2 = AllocObjectQuarantined) W_heap).

Definition heapUR : ucmra := prodUR (gmapUR Addr (agreeR (leibnizO (Addr * Addr)))) (gsetUR Addr).
Definition heap_authUR : ucmra := authUR heapUR.
Definition heap_encode (W_heap : Heap) : heapUR :=
  (to_agree <$> heap_bounds W_heap, heap_quarantined W_heap).

Class heap_preG Σ := { heap_inG :: inG Σ heap_authUR }.
Class heapG Σ := { heap_pre_inG :: heap_preG Σ; heap_name : gname }.
Definition heapΣ := #[GFunctor heap_authUR].
Global Instance subG_heapΣ Σ : subG heapΣ Σ -> heap_preG Σ.
Proof. solve_inG. Qed.

Lemma heap_quarantined_lookup W_heap b :
  b ∈ heap_quarantined W_heap <->
  ∃ o, W_heap !! b = Some o /\ alloc_object_status o = AllocObjectQuarantined.
Proof.
  rewrite /heap_quarantined elem_of_dom.
  split.
  - intros [o Ho]. apply map_lookup_filter_Some in Ho as [Hs Hb].
    exists o. auto.
  - intros (o & Hb & Hs). exists o. apply map_lookup_filter_Some. auto.
Qed.

Global Instance heap_encode_core_id W_heap : CoreId (heap_encode W_heap).
Proof. apply _. Qed.

Lemma heap_encode_valid W_heap : ✓ heap_encode W_heap.
Proof.
  split; last done. intros b. rewrite /heap_encode /= !lookup_fmap.
  destruct (W_heap !! b) eqn:Hb; rewrite Hb /=; done.
Qed.

Lemma heap_encode_mono W_heap W_heap' :
  related_sts_heap_std W_heap W_heap' -> heap_encode W_heap ≼ heap_encode W_heap'.
Proof.
  intros [Hkeep _]. apply prod_included. split.
  - apply lookup_included. intros b.
    rewrite /heap_encode /heap_bounds /= !lookup_fmap.
    destruct (W_heap !! b) as [o|] eqn:Hb; rewrite Hb /=; last by apply option_included; left.
    destruct (Hkeep b o Hb) as (o' & Hb' & Hbase & He & _).
    rewrite Hb' /= Some_included_total to_agree_included. by rewrite Hbase He.
  - apply gset_included. intros b.
    rewrite /heap_encode /= !heap_quarantined_lookup.
    intros (o & Hb & Hs). destruct (Hkeep b o Hb) as (o' & Hb' & _ & _ & Hs').
    exists o'. auto.
Qed.

Lemma heap_encode_future W_heap W_heap' :
  heap_wf W_heap' -> heap_encode W_heap ≼ heap_encode W_heap' -> related_sts_heap_std W_heap W_heap'.
Proof.
  intros Hwf [Hbounds Hquarantine]%prod_included. split.
  - intros b o Hb.
    change ((to_agree <$> heap_bounds W_heap : gmapUR Addr (agreeR (leibnizO (Addr * Addr)))) ≼ to_agree <$> heap_bounds W_heap') in Hbounds.
    pose proof (proj1 (lookup_included
      (to_agree <$> heap_bounds W_heap : gmapUR Addr (agreeR (leibnizO (Addr * Addr))))
      (to_agree <$> heap_bounds W_heap')) Hbounds b) as Hlookup.
    clear Hbounds. rename Hlookup into Hbounds.
    rewrite /heap_encode /heap_bounds /= !lookup_fmap Hb /= in Hbounds.
    destruct (W_heap' !! b) as [o'|] eqn:Hb'; rewrite Hb' /= in Hbounds.
    + exists o'. split; first done.
      move: Hbounds; rewrite Some_included_total to_agree_included leibniz_equiv_iff.
      intros Heq. injection Heq as Hbase Hend.
      split; first done. split; first done.
      intros Hs. change (heap_quarantined W_heap ≼ heap_quarantined W_heap') in Hquarantine.
        apply gset_included in Hquarantine.
        assert (b ∈ heap_quarantined W_heap') as Hq.
        { apply Hquarantine. apply heap_quarantined_lookup. eauto. }
        apply heap_quarantined_lookup in Hq as (oq & Hq & Hsq).
        rewrite Hb' in Hq. by simplify_eq.
    + apply option_included in Hbounds as [Hbad|(? & ? & Hbad & Hbad' & _)]; discriminate.
  - intros b o _ Hb. by apply Hwf.
Qed.

Section heap_ghost.
  Context {Σ : gFunctors} {heapg : heapG Σ}.

  (** Authority is held once for the global heap. Snapshots are lower bounds:
      a live snapshot records bounds but makes no assertion of current liveness. *)
  Definition heap_std_auth (W_heap : Heap) : iProp Σ :=
    ⌜heap_wf W_heap⌝ ∗ own heap_name (● heap_encode W_heap).
  Definition heap_std_full (W_heap : Heap) : iProp Σ :=
    ⌜heap_wf W_heap⌝ ∗ own heap_name (◯ heap_encode W_heap).

  Global Instance heap_std_auth_timeless W_heap : Timeless (heap_std_auth W_heap).
  Proof. apply _. Qed.
  Global Instance heap_std_full_timeless W_heap : Timeless (heap_std_full W_heap).
  Proof. apply _. Qed.
  Global Instance heap_std_full_persistent W_heap : Persistent (heap_std_full W_heap).
  Proof. apply _. Qed.

  Lemma heap_std_auth_full W_heap :
    heap_std_auth W_heap ==∗ heap_std_auth W_heap ∗ heap_std_full W_heap.
  Proof.
    iIntros "[%Hwf Ha]". iMod (own_update _ _ (● heap_encode W_heap ⋅ ◯ heap_encode W_heap) with "Ha") as "[Ha Hs]".
    { apply auth_update_dfrac_alloc; [apply _|reflexivity]. }
    iModIntro. iFrame. auto.
  Qed.

  Lemma heap_std_full_weaken W_heap W_heap' :
    heap_wf W_heap -> related_sts_heap_std W_heap W_heap' ->
    heap_std_full W_heap' -∗ heap_std_full W_heap.
  Proof.
    iIntros (Hwf Hrel) "[_ Hs]". iSplit; first done.
    iApply (own_mono with "Hs"). apply auth_frag_mono, heap_encode_mono; done.
  Qed.

  Lemma heap_std_auth_full_related W_heap W_heap_old :
    heap_std_auth W_heap -∗ heap_std_full W_heap_old -∗ ⌜related_sts_heap_std W_heap_old W_heap⌝.
  Proof.
    iIntros "[%Hwf Ha] [_ Hs]".
    iDestruct (own_valid_2 with "Ha Hs") as %[Hincl _]%auth_both_valid_discrete.
    iPureIntro. by apply heap_encode_future.
  Qed.

  Lemma heap_std_auth_update W_heap W_heap' :
    related_sts_heap_std W_heap W_heap' ->
    heap_std_auth W_heap ==∗ heap_std_auth W_heap' ∗ heap_std_full W_heap'.
  Proof.
    iIntros (Hrel) "[%Hwf Ha]".
    have Hincl := heap_encode_mono W_heap W_heap' Hrel.
    have Hwf' := related_sts_heap_std_wf W_heap W_heap' Hrel Hwf.
    iMod (own_update _ _ (● heap_encode W_heap' ⋅ ◯ heap_encode W_heap') with "Ha") as "[Ha Hs]".
    { apply auth_update_alloc.
      rewrite {1}(core_id_extract (heap_encode W_heap) (heap_encode W_heap') Hincl).
      rewrite -{2}(right_id ε op (heap_encode W_heap')).
      apply op_local_update_discrete. intros _.
      rewrite -(core_id_extract (heap_encode W_heap) (heap_encode W_heap') Hincl).
      apply heap_encode_valid. }
    iModIntro. iFrame. auto.
  Qed.

  Lemma heap_std_auth_allocate W_heap b e :
    heap_fresh W_heap b e ->
    heap_std_auth W_heap ==∗ heap_std_auth (heap_allocate W_heap b e) ∗
      heap_std_full (heap_allocate W_heap b e).
  Proof. intros Hfresh. apply heap_std_auth_update, heap_allocate_future; done. Qed.

  Lemma heap_std_auth_quarantine W_heap b :
    heap_std_auth W_heap ==∗ heap_std_auth (heap_quarantine W_heap b) ∗
      heap_std_full (heap_quarantine W_heap b).
  Proof. apply heap_std_auth_update, heap_quarantine_future. Qed.
End heap_ghost.

Lemma heap_std_init {Σ : gFunctors} {heappreg : heap_preG Σ} :
  ⊢ |==> ∃ heapg : heapG Σ, heap_std_auth ∅ ∗ heap_std_full ∅.
Proof.
  iMod (own_alloc (● heap_encode ∅ ⋅ ◯ heap_encode ∅)) as (γ) "[Ha Hs]".
  { apply auth_both_valid_discrete. split; first done. apply heap_encode_valid. }
  iExists (Build_heapG Σ heappreg γ). iModIntro.
  rewrite /heap_std_auth /heap_std_full /=. iFrame.
  iSplit; iPureIntro; apply heap_wf_empty.
Qed.
