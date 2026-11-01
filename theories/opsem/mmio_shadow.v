From griotte Require Import machine_base heap_layout.

(** Entries are keyed by heap addresses. Direct accesses through a capability
    into the shadow region use [shadow_to_heap] to obtain this key. Loading a
    heap capability consults its base directly. *)
Inductive AllocStatus := ShadowLive | ShadowQuarantined.

#[global] Instance alloc_status_eq_dec : EqDecision AllocStatus.
Proof. solve_decision. Defined.

Definition ShadowTbl := gmap Addr AllocStatus.

Class ShadowRegion := {
    shadow_b : Addr;
    shadow_e : Addr;
    shadow_valid : (shadow_b < shadow_e)%a;
  }.

(** Shadow memory is addressed through a separate region, while [ShadowTbl]
    and shadow points-to are indexed by heap addresses. The machine may use
    any bijection between these equally sized regions. Translation is checked:
    precisely the addresses in the source region have an image. *)
Class HeapShadowTranslation `{HeapRegion} `{ShadowRegion} := {
    heap_to_shadow : Addr -> option Addr;
    shadow_to_heap : Addr -> option Addr;
    heap_shadow_same_size : (heap_e - heap_b = shadow_e - shadow_b)%Z;
    heap_to_shadow_domain a :
      is_Some (heap_to_shadow a) <-> withinBounds heap_b heap_e a = true;
    shadow_to_heap_domain a :
      is_Some (shadow_to_heap a) <-> withinBounds shadow_b shadow_e a = true;
    heap_shadow_inverse a s :
      heap_to_shadow a = Some s <-> shadow_to_heap s = Some a;
  }.
#[export] Hint Mode HeapShadowTranslation - - : typeclass_instances.

(** The default translation preserves the offset from the region's base.
    Checked addition prevents an out-of-range address from wrapping around. *)
Definition translate_region (b e target a : Addr) : option Addr :=
  if withinBounds b e a then (target + (a - b))%a else None.

Lemma translate_region_spec (b e target target_e a a' : Addr) :
  (e - b = target_e - target)%Z ->
  translate_region b e target a = Some a' <->
  a ∈ₐ [b, e) ∧ a' ∈ₐ [target, target_e) ∧
  (a' : Z) = (target + (a - b))%Z.
Proof.
  intros Hsize. unfold translate_region.
  destruct (withinBounds b e a) eqn:Hbounds.
  - apply withinBounds_true_iff in Hbounds. split.
    + intros Hadd. split; first done. split; solve_addr.
    + intros (_ & _ & Heq). solve_addr.
  - split; first discriminate.
    intros (Hbounds' & _). apply withinBounds_true_iff in Hbounds'. congruence.
Qed.

Lemma translate_region_domain (b e target target_e a : Addr) :
  (e - b = target_e - target)%Z ->
  is_Some (translate_region b e target a) <-> withinBounds b e a = true.
Proof.
  intros Hsize. split.
  - intros [a' Ha']. apply (translate_region_spec b e target target_e) in Ha'; last done.
    apply withinBounds_true_iff. exact (proj1 Ha').
  - intros Hb. unfold translate_region. rewrite Hb.
    apply withinBounds_true_iff in Hb.
    destruct (finz_incr_spec MemNum target (a - b)%Z)
      as [(a' & Ha' & _)|[Hnone Hbad] ].
    + by exists a'.
    + solve_addr.
Qed.

Lemma translate_region_inverse (b e target target_e a a' : Addr) :
  (e - b = target_e - target)%Z ->
  translate_region b e target a = Some a' <->
  translate_region target target_e b a' = Some a.
Proof.
  intros Hsize.
  rewrite (translate_region_spec b e target target_e) //.
  rewrite (translate_region_spec target target_e b e); last lia.
  split; intros (? & ? & ?); repeat split; solve_addr.
Qed.

Definition affine_heap_shadow_translation `{HeapRegion} `{ShadowRegion}
    (Hsize : (heap_e - heap_b = shadow_e - shadow_b)%Z) : HeapShadowTranslation.
Proof.
  refine {| heap_to_shadow := translate_region heap_b heap_e shadow_b;
            shadow_to_heap := translate_region shadow_b shadow_e heap_b;
            heap_shadow_same_size := Hsize |}.
  - intros a. apply (translate_region_domain _ _ _ shadow_e). done.
  - intros a. apply (translate_region_domain _ _ _ heap_e). lia.
  - intros a s. apply translate_region_inverse. done.
Defined.

Section Translation.
  Context `{HeapRegion} `{ShadowRegion} `{!HeapShadowTranslation}.

  Lemma heap_to_shadow_bounds a s : heap_to_shadow a = Some s ->
    withinBounds heap_b heap_e a = true ∧ withinBounds shadow_b shadow_e s = true.
  Proof.
    intros Ha. split.
    - apply heap_to_shadow_domain. by exists s.
    - apply shadow_to_heap_domain. exists a. by apply heap_shadow_inverse.
  Qed.

  Lemma shadow_to_heap_bounds s a : shadow_to_heap s = Some a ->
    withinBounds shadow_b shadow_e s = true ∧ withinBounds heap_b heap_e a = true.
  Proof.
    intros Ha. apply heap_shadow_inverse in Ha.
    apply heap_to_shadow_bounds in Ha. tauto.
  Qed.

  Lemma heap_to_shadow_inj a a' s :
    heap_to_shadow a = Some s -> heap_to_shadow a' = Some s -> a = a'.
  Proof. intros Ha Ha'. apply heap_shadow_inverse in Ha, Ha'. congruence. Qed.

  Lemma shadow_to_heap_inj s s' a :
    shadow_to_heap s = Some a -> shadow_to_heap s' = Some a -> s = s'.
  Proof. intros Ha Ha'. apply heap_shadow_inverse in Ha, Ha'. congruence. Qed.
End Translation.

Definition is_shadow_address `{ShadowRegion} (a : Addr) : bool :=
  withinBounds shadow_b shadow_e a.

Definition disjoint_from_shadow `{ShadowRegion} (b e : Addr) : Prop :=
  finz.seq_between b e ## finz.seq_between shadow_b shadow_e.

Lemma disjoint_from_shadow_not_in `{ShadowRegion} (b e a : Addr) :
  disjoint_from_shadow b e →
  withinBounds b e a = true →
  is_shadow_address a = false.
Proof.
  intros Hdisjoint Hbounds. apply not_true_is_false. intros Hshadow.
  apply withinBounds_true_iff in Hbounds, Hshadow.
  rewrite /disjoint_from_shadow elem_of_disjoint in Hdisjoint.
  eapply Hdisjoint; apply elem_of_finz_seq_between; eauto.
Qed.
