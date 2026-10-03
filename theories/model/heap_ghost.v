From griotte Require Export heap_std compartment_names.
From iris.algebra Require Import auth excl gmap.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.

(** An authoritative map of exclusive allocation objects, with one fragment
    per object, mirrors the standard-state ghost map. *)
Definition heapUR : ucmra := gmapUR AId (exclR (leibnizO AllocObject)).
Definition heap_authUR : ucmra := authUR heapUR.

Lemma heap_local_update (h h' : Heap) :
  dom h ⊆ dom h' ->
  ((Excl <$> h : heapUR), (Excl <$> h : heapUR))
    ~l~> (Excl <$> h', Excl <$> h').
Proof.
  intros Hdom. apply gmap_local_update. intros i.
  rewrite !lookup_fmap.
  destruct (h !! i) as [o|] eqn:Ho;
    destruct (h' !! i) as [o'|] eqn:Ho'.
  - have Hf' : (Excl <$> h' : heapUR) !! i = Some (Excl o')
      by rewrite lookup_fmap Ho'.
    rewrite Ho /= Hf'.
    apply (@option_local_update _ (exclR (leibnizO AllocObject))
      (Excl o) (Excl o) (Excl o') (Excl o')).
    apply exclusive_local_update. done.
  - rewrite Ho /=. exfalso.
    have Hi : i ∈ dom h by apply elem_of_dom; eauto.
    apply Hdom in Hi. apply elem_of_dom in Hi.
    rewrite Ho' in Hi. destruct Hi as [x Hx]. discriminate.
  - have Hf' : (Excl <$> h' : heapUR) !! i = Some (Excl o')
      by rewrite lookup_fmap Ho'.
    rewrite Ho /= Hf'.
    apply (@alloc_option_local_update _ (exclR (leibnizO AllocObject))
      (Excl o') None). done.
  - have Hf' : (Excl <$> h' : heapUR) !! i = None
      by rewrite lookup_fmap Ho'.
    rewrite Ho /= Hf'. reflexivity.
Qed.

Class heap_preG Σ := { heap_inG :: inG Σ heap_authUR }.
Class heapG Σ `{CmptNameG} := {
  heap_pre_inG :: heap_preG Σ;
  heap_name : CmptName -> gname;
}.
Definition heapΣ := #[GFunctor heap_authUR].
Global Instance subG_heapΣ Σ : subG heapΣ Σ -> heap_preG Σ.
Proof. solve_inG. Qed.

Section heap_ghost.
  Context {Σ : gFunctors} {Cname : CmptNameG} {heapg : heapG Σ}.

  Definition heap_std_full (C : CmptName) (h : Heap) : iProp Σ :=
    own (heap_name C) (● (Excl <$> h : heapUR)).
  Definition heap_std_auth (C : CmptName) (ι : AId) (o : AllocObject) : iProp Σ :=
    own (heap_name C) (◯ ({[ι := Excl o]} : heapUR)).
  Definition heap_std_fragments (C : CmptName) (h : Heap) : iProp Σ :=
    [∗ map] b ↦ o ∈ h, heap_std_auth C b o.

  Global Instance heap_std_full_timeless C h : Timeless (heap_std_full C h).
  Proof. apply _. Qed.
  Global Instance heap_std_auth_timeless C b o : Timeless (heap_std_auth C b o).
  Proof. apply _. Qed.

  Lemma heap_auth_fragments_pack γ (a : heapUR) h :
    own γ (● a) ∗
    ([∗ map] b ↦ o ∈ h, own γ (◯ ({[b := Excl o]} : heapUR)))
    ⊣⊢ own γ (● a ⋅ ◯ (Excl <$> h)).
  Proof.
    induction h as [|b o h Hb IH] using map_ind.
    - rewrite big_sepM_empty fmap_empty bi.sep_emp.
      change (own γ (● a) ⊣⊢ own γ (● a ⋅ ε)).
      by rewrite right_id.
    - rewrite big_sepM_insert // fmap_insert.
      rewrite (bi.sep_comm (own γ (◯ ({[b := Excl o]} : heapUR)))).
      rewrite bi.sep_assoc IH -own_op.
      rewrite -assoc -auth_frag_op.
      rewrite insert_singleton_op; last by rewrite lookup_fmap Hb.
      by rewrite (comm _ (Excl <$> h)).
  Qed.

  Lemma heap_std_full_auth C h b o :
    heap_std_full C h -∗ heap_std_auth C b o -∗ ⌜h !! b = Some o⌝.
  Proof.
    iIntros "Ha Hs".
    iDestruct (own_valid_2 with "Ha Hs") as %[Hi Hv]%auth_both_valid_discrete.
    iPureIntro.
    apply (singleton_included_exclusive_l _ _ _ _ Hv) in Hi.
    rewrite lookup_fmap in Hi.
    apply leibniz_equiv in Hi.
    destruct (h !! b) eqn:Hb; cbn in Hi;
      rewrite Hb /= in Hi; congruence.
  Qed.

  Lemma heap_std_full_allocate C h ι b e :
    heap_fresh h ι b e ->
    heap_std_full C h ==∗
    heap_std_full C (heap_allocate h ι b e) ∗
    heap_std_auth C ι (MkAllocObject b e AllocObjectLive).
  Proof.
    iIntros (Hfresh) "Ha".
    iMod (own_update _ _
      (● (Excl <$> heap_allocate h ι b e : heapUR) ⋅
       ◯ {[ι := Excl (MkAllocObject b e AllocObjectLive)]})
      with "Ha") as "[Ha Hs]".
    { apply auth_update_alloc. rewrite /heap_allocate fmap_insert.
      apply alloc_singleton_local_update.
      - rewrite lookup_fmap (proj1 Hfresh). done.
      - done. }
    by iFrame.
  Qed.

  Lemma heap_std_full_update_one C h b o o' :
    heap_std_full C h -∗ heap_std_auth C b o ==∗
    heap_std_full C (<[b := o']> h) ∗ heap_std_auth C b o'.
  Proof.
    iIntros "Ha Hs".
    iDestruct (heap_std_full_auth with "Ha Hs") as %Hb.
    iCombine "Ha Hs" as "H".
    iMod (own_update _ _
      (● (Excl <$> <[b := o']> h : heapUR) ⋅ ◯ {[b := Excl o']})
      with "H") as "[Ha Hs]".
    { apply auth_update. rewrite fmap_insert.
      apply singleton_local_update with (x := Excl o).
      - rewrite lookup_fmap Hb. done.
      - apply exclusive_local_update. done. }
    by iFrame.
  Qed.

  Lemma heap_std_full_quarantine C h b o :
    h !! b = Some o ->
    heap_std_full C h -∗ heap_std_auth C b o ==∗
    heap_std_full C (heap_quarantine h b) ∗
    heap_std_auth C b
      (MkAllocObject (alloc_object_base o) (alloc_object_end o)
        AllocObjectQuarantined).
  Proof.
    iIntros (Hb) "Ha Hs".
    assert (heap_quarantine h b =
      <[b := MkAllocObject (alloc_object_base o) (alloc_object_end o)
        AllocObjectQuarantined]> h) as Hq.
    { rewrite /heap_quarantine -(insert_id h b o Hb) alter_insert.
      case_decide; last congruence.
      rewrite insert_insert. case_decide; [done|congruence]. }
    rewrite Hq.
    iApply (heap_std_full_update_one with "Ha Hs").
  Qed.

  Lemma heap_std_full_update C h h' :
    related_sts_heap_std h h' ->
    heap_std_full C h -∗ heap_std_fragments C h ==∗
    heap_std_full C h' ∗ heap_std_fragments C h'.
  Proof.
    iIntros (Hrel) "Ha Hfrags".
    have Hdom := related_sts_heap_std_dom h h' Hrel.
    iAssert (own (heap_name C)
      (● (Excl <$> h : heapUR) ⋅ ◯ (Excl <$> h : heapUR)))%I
      with "[Ha Hfrags]" as "H".
    { rewrite -(heap_auth_fragments_pack (heap_name C) (Excl <$> h) h)
        /heap_std_fragments. iFrame. }
    iMod (own_update _ _
      (● (Excl <$> h' : heapUR) ⋅ ◯ (Excl <$> h' : heapUR))
      with "H") as "H".
    { apply auth_update. by apply heap_local_update. }
    iDestruct (heap_auth_fragments_pack (heap_name C) (Excl <$> h') h'
      with "H") as "[Ha Hfrags]".
    by iFrame.
  Qed.
End heap_ghost.

Lemma heap_std_init {Σ : gFunctors} {Cname : CmptNameG} {heappreg : heap_preG Σ} :
  ⊢ |==> ∃ heapg : heapG Σ,
    [∗ set] C ∈ CNames, heap_std_full C ∅.
Proof.
  assert (⊢ |==> ∃ γ : CmptName -> gname,
    [∗ set] C ∈ CNames, own (γ C) (● (∅ : heapUR)))%I as Hinit.
  { induction CNames as [|C Cs HC IH] using set_ind_L.
    - iModIntro. iExists (λ C, encode C). by iApply big_sepS_empty.
    - iMod IH as (γ) "Hnames".
      iMod (own_alloc (● (∅ : heapUR))) as (γC) "Hnew".
      { apply auth_auth_valid. done. }
      iModIntro.
      iExists (λ C', if bool_decide (C' = C) then γC else γ C').
      iApply (big_sepS_union_2 with "[Hnew]").
      + iApply big_sepS_singleton. by rewrite bool_decide_eq_true_2.
      + iApply (big_sepS_mono with "Hnames").
        iIntros (C' HC') "Hname".
        rewrite bool_decide_eq_false_2; [done|set_solver]. }
  iMod Hinit as (γ) "Hnames".
  iExists (Build_heapG Σ Cname heappreg γ). iModIntro.
  iApply (big_sepS_mono with "Hnames").
  iIntros (C HC) "Ha".
  rewrite /heap_std_full /= fmap_empty. iFrame.
Qed.
