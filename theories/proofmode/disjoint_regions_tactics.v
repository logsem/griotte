From iris.proofmode Require Import proofmode.
From stdpp Require Import sets list.
From griotte Require Import addresses memory_region.

Definition ByReflexivity (P: Prop) :=
  P.
#[export] Hint Extern 1 (ByReflexivity _) => reflexivity : disj_regions.

Definition AddrRegionRange (l: list Addr) (b e: Addr) :=
  ∀ a, a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionRange_singleton a :
  ByReflexivity (eqb_addr a addresses.top = false) →
  AddrRegionRange [a] a (a^+1)%a.
Proof.
  unfold ByReflexivity. cbn. intros ?%Z.eqb_neq.
  intros a' ->%list_elem_of_singleton. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionRange_singleton : disj_regions.

Lemma AddrRegionRange_region_addrs b e :
  AddrRegionRange (finz.seq_between b e) b e.
Proof.
  intros a ?%elem_of_finz_seq_between. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionRange_region_addrs : disj_regions.

Definition AddrRegionsRange (ll: list (list Addr)) (b e: Addr) :=
  ∀ l a, l ∈ ll → a ∈ l → (b <= a)%a ∧ (a < e)%a.

Lemma AddrRegionsRange_single l b e :
  AddrRegionRange l b e →
  AddrRegionsRange [l] b e.
Proof.
  intros Hl l' a ->%list_elem_of_singleton ?%Hl. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionsRange_single | 1 : disj_regions.

Lemma AddrRegionsRange_cons l ll b e b' e' :
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  AddrRegionsRange (l :: ll) (finz.min b b') (finz.max e e').
Proof.
  intros Hl Hll l' a [->|H]%elem_of_cons.
  - intros ?%Hl. solve_addr.
  - intros ?%Hll; auto. solve_addr.
Qed.
#[export] Hint Resolve AddrRegionsRange_cons | 10 : disj_regions.

Lemma addr_range_union_incl_range (ll: list (list Addr)) (b e: Addr):
  AddrRegionsRange ll b e →
  ⋃ ll ⊆ finz.seq_between b e.
Proof.
  revert b e. induction ll as [| l ll].
  - intros. cbn. unfold subseteq, list_subseteq. unfold empty, Empty_list.
    inversion 1.
  - intros b e HInd. cbn. unfold union, Union_list, subseteq, list_subseteq.
    intros x. intros [Hx|Hx]%elem_of_app.
    + specialize (HInd l x ltac:(constructor) Hx). apply elem_of_finz_seq_between.
      solve_addr.
    + assert (HI: AddrRegionsRange ll b e).
      { intros ? ? ? ?. eapply HInd.
        + apply list_elem_of_further; eassumption.
        + auto.
      }
      specialize (IHll _ _ HI).
      rewrite elem_of_subseteq in IHll.
      by apply IHll.
Qed.

Lemma AddrRegionRange_iff_incl_region_addrs l b e :
  AddrRegionRange l b e ↔ (l ⊆ finz.seq_between b e).
Proof.
  unfold AddrRegionRange, subseteq, list_subseteq.
  split.
  - intros H **. rewrite elem_of_finz_seq_between. by apply H.
  - intros H **. apply elem_of_finz_seq_between. by apply H.
Qed.

Lemma addr_range_disj_union_empty (l: list Addr) :
  l ## ⋃ [].
Proof.
  cbn. unfold empty, Empty_list, disjoint.
  unfold set_disjoint_instance. intros * ? ?%elem_of_nil. auto.
Qed.
#[export] Hint Resolve addr_range_disj_union_empty | 1 : disj_regions.

Lemma addr_range_disj_range_union (l: list Addr) ll b e b' e':
  AddrRegionRange l b e →
  AddrRegionsRange ll b' e' →
  ByReflexivity ((e <=? b') || (e' <=? b) = true)%a →
  l ## ⋃ ll.
Proof.
  intros Hl Hll. unfold ByReflexivity.
  rewrite orb_true_iff !Z.leb_le.
  intros.
  rewrite AddrRegionRange_iff_incl_region_addrs in Hl.
  eapply disjoint_mono_l; eauto.
  eapply disjoint_mono_r.
  + eapply addr_range_union_incl_range; eauto.
  + unfold disjoint. intro. rewrite !elem_of_finz_seq_between. solve_addr.
Qed.
#[export] Hint Resolve addr_range_disj_range_union | 10 : disj_regions.

Lemma addr_disjoint_list_empty : ## ([]: list (list Addr)).
Proof. constructor. Qed.
#[export] Hint Resolve addr_disjoint_list_empty : disj_regions.

Lemma addr_disjoint_list_cons (l: list Addr) ll :
  l ## ⋃ ll →
  ## ll →
  ## (l :: ll).
Proof. intros. rewrite disjoint_list_cons; auto. Qed.
#[export] Hint Resolve addr_disjoint_list_cons : disj_regions.

(** Select a pair of distinct address regions from one opaque
    [disjoint_list] certificate. The concrete-layout proofs use this lemma to
    share one ordered partition without unfolding its proof at every layout
    field. *)
Local Lemma addr_disjoint_list_lookup_lt
    (regions : list (list Addr)) (i j : nat)
    (ri rj : list Addr) :
  ## regions ->
  regions !! i = Some ri ->
  regions !! j = Some rj ->
  (i < j)%nat ->
  ri ## rj.
Proof.
  revert regions j ri rj.
  induction i as [|i IHi];
    intros regions j ri rj Hdis Hi Hj Hij.
  - destruct regions as [|r regions]; simpl in Hi; [done |].
    simplify_eq.
    destruct j as [|j]; [lia |].
    simpl in Hj.
    rewrite disjoint_list_cons in Hdis.
    destruct Hdis as [Hr _].
    eapply disjoint_mono_r; [| exact Hr].
    intros x Hx.
    rewrite elem_of_union_list.
    exists rj; split; [eapply list_elem_of_lookup_2; exact Hj | exact Hx].
  - destruct regions as [|r regions]; simpl in Hi; [done |].
    destruct j as [|j]; [lia |].
    simpl in Hi, Hj.
    rewrite disjoint_list_cons in Hdis.
    destruct Hdis as [_ Hdis].
    eapply IHi; [exact Hdis | exact Hi | exact Hj | lia].
Qed.

Lemma addr_disjoint_list_lookup
    (regions : list (list Addr)) (i j : nat)
    (ri rj : list Addr) :
  ## regions ->
  regions !! i = Some ri ->
  regions !! j = Some rj ->
  i <> j ->
  ri ## rj.
Proof.
  intros Hdis Hi Hj Hij.
  destruct (Nat.lt_trichotomy i j) as [Hij' | Heq_or].
  - eapply addr_disjoint_list_lookup_lt; eauto.
  - destruct Heq_or as [Hij' | Hji].
    + exfalso. apply Hij. exact Hij'.
    + symmetry. eapply addr_disjoint_list_lookup_lt; eauto.
Qed.

(** Find an atomic region in a transparent partition. Matching is
    intentionally syntactic: a missing or duplicated atom should make a
    concrete-layout proof fail immediately instead of starting broad proof
    search. *)
Ltac addr_partition_index region regions :=
  lazymatch regions with
  | region :: _ => constr:(0%nat)
  | _ :: ?regions' =>
      let i := addr_partition_index region regions' in
      constr:(S i)
  end.

Ltac solve_addr_partition_pair regions Hdis :=
  lazymatch goal with
  | |- ?r1 ## ?r2 =>
      let regions' := eval hnf in regions in
      let i := addr_partition_index r1 regions' in
      let j := addr_partition_index r2 regions' in
      eapply (addr_disjoint_list_lookup regions i j r1 r2);
      [ exact Hdis | reflexivity | reflexivity | lia ]
  end.

Ltac solve_addr_partition_disjoint regions Hdis :=
  rewrite !(@disjoint_union_l Addr (list Addr) _ _ _ _ _)
          !(@disjoint_union_r Addr (list Addr) _ _ _ _ _);
  repeat split; solve_addr_partition_pair regions Hdis.

Ltac disj_regions :=
  once (typeclasses eauto with disj_regions).
