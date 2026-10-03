From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Export world_ghost_theory.
From griotte Require Import logrel.

Section stack_object_helpers.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {relg : relGS Σ}

    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Definition so_object_addresses (b e : Addr) :=
    finz.seq_between b e.

  Definition so_object_temporaries (W : WORLD) (π : option AId) (b e : Addr) :=
    filter
      (fun a => std W !! addr_key π a = Some Temporary)
      (so_object_addresses b e).

  Definition so_object_permanents (W : WORLD) (π : option AId) (b e : Addr) :=
    filter
      (fun a => std W !! addr_key π a = Some Permanent)
      (so_object_addresses b e).

  Definition so_revoked_without_object
      (W : WORLD) (π : option AId) (b e : Addr) (l : list LAddr) :=
    filter
      (fun a => a ∉ addr_key π <$> so_object_temporaries W π b e)
      l.

  (** The object may be a heap object: its addresses are keyed by [addr_key π]. *)
  Global Instance addr_key_inj π : Inj eq eq (addr_key π).
  Proof.
    intros a a' Heq.
    rewrite -(addr_key_addr π a) -(addr_key_addr π a'). by rewrite Heq.
  Qed.

  Lemma NoDup_addr_key_fmap π (l : list Addr) : NoDup l -> NoDup (addr_key π <$> l).
  Proof. intros Hl. apply NoDup_fmap_2; [apply _|done]. Qed.

  Lemma elem_of_addr_key_fmap π a (l : list Addr) :
    addr_key π a ∈ addr_key π <$> l <-> a ∈ l.
  Proof. apply (list_elem_of_fmap_inj (addr_key π)). Qed.

  Lemma addr_key_LNonHeap_eq π a b : addr_key π a = LNonHeap b -> a = b.
  Proof. intros Heq. rewrite -(addr_key_addr π a). by rewrite Heq. Qed.

  Lemma addr_key_elem_of_LNonHeap_fmap π a (l : list Addr) :
    addr_key π a ∈ LNonHeap <$> l -> a ∈ l.
  Proof.
    intros (b & Heq & Hb)%list_elem_of_fmap.
    by apply addr_key_LNonHeap_eq in Heq as ->.
  Qed.

  Lemma LNonHeap_elem_of_addr_key_fmap π b (l : list Addr) :
    LNonHeap b ∈ addr_key π <$> l -> b ∈ l.
  Proof.
    intros (a & Heq & Ha)%list_elem_of_fmap. symmetry in Heq.
    by apply addr_key_LNonHeap_eq in Heq as ->.
  Qed.

  Lemma addr_key_pointsto_list π (la : list Addr) (lv : list LWord) :
    ([∗ list] k;v ∈ addr_key π <$> la;lv, k ↦ₖ v) ⊣⊢
    ([∗ list] a;v ∈ la;lv, a ↦ₐ v) ∗ ([∗ list] a ∈ la, key_share (addr_key π a)).
  Proof.
    rewrite big_sepL2_fmap_l.
    setoid_rewrite addr_key_pointsto.
    rewrite big_sepL2_sep big_sepL2_const_sepL_l.
    iSplit.
    - iIntros "[$ [_ $]]".
    - iIntros "[Hv $]". iDestruct (big_sepL2_length with "Hv") as %Hlen. by iFrame.
  Qed.

  Lemma so_invs_pointsto
      (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
      (lk : list LAddr) (lv : list LWord) :
    (λ '(k,_,_,_), k) <$> l = lk ->
    ([∗ list] '(k,_,_,_);v ∈ l;lv, k ↦ₖ v) ⊣⊢ [∗ list] k;v ∈ lk;lv, k ↦ₖ v.
  Proof.
    intros <-. rewrite big_sepL2_fmap_l.
    apply big_sepL2_proper. by intros ? [ [ [k p] phi] rho] v _ _.
  Qed.

  Lemma NoDup_subset_filter_membership
      {A} `{EqDecision0 : EqDecision A} (xs ys : list A) :
    NoDup xs ->
    NoDup ys ->
    xs ⊆ ys ->
    xs ≡ₚ filter (fun y => y ∈ xs) ys.
  Proof.
    intros Hnodup_xs Hnodup_ys Hsubset.
    generalize dependent xs.
    induction ys as [|y ys]; intros xs Hnodup_xs Hsubset.
    - destruct xs; last set_solver.
      done.
    - cbn.
      apply NoDup_cons in Hnodup_ys as [Hy_ys Hnodup_ys].
      destruct (decide (y ∈ xs)) as [Hy_xs | Hy_xs].
      + apply elem_of_Permutation in Hy_xs as [xs' Hxs].
        setoid_rewrite Hxs in Hnodup_xs.
        apply NoDup_cons in Hnodup_xs as [Hy_xs' Hnodup_xs'].
        setoid_rewrite Hxs in Hsubset.
        setoid_rewrite Hxs at 1.
        assert (xs' ⊆ ys) as Hsubset'.
        { intros x Hx.
          assert (x ≠ y) by (intro; simplify_eq; done).
          apply (list_elem_of_further _ y) in Hx.
          apply Hsubset in Hx.
          apply elem_of_cons in Hx as [Hx|Hx]; auto.
          done.
        }
        eapply IHys in Hsubset'; eauto.
        apply Permutation_cons; first done.
        rewrite Hsubset'.
        clear -Hnodup_ys Hxs Hy_ys.
        induction ys; cbn; first done.
        apply not_elem_of_cons in Hy_ys as [Hy_a Hy_ys].
        apply NoDup_cons in Hnodup_ys as [_ Hnodup_ys].
        destruct (decide (a ∈ xs')) as [Ha|Ha].
        * apply (list_elem_of_further _ y) in Ha.
          setoid_rewrite <- Hxs in Ha.
          rewrite decide_True; last done.
          rewrite IHys; auto.
        * rewrite decide_False; first (rewrite IHys; auto).
          intros Ha'.
          setoid_rewrite Hxs in Ha'.
          apply elem_of_cons in Ha' as [Ha'|?]; auto.
      + eapply IHys; auto.
        intros x Hx.
        assert (x ≠ y) by (intro; simplify_eq; done).
        apply Hsubset in Hx.
        apply elem_of_cons in Hx as [Hx|Hx]; auto.
        done.
  Qed.

  Lemma so_object_addresses_partition W π b e :
    Forall
      (fun a =>
         std W !! addr_key π a = Some Permanent \/
         std W !! addr_key π a = Some Temporary)
      (so_object_addresses b e) ->
    so_object_addresses b e
      ≡ₚ so_object_permanents W π b e ++
          so_object_temporaries W π b e.
  Proof.
    intros Hstates.
    rewrite /so_object_permanents /so_object_temporaries
      /so_object_addresses in Hstates |- *.
    generalize (finz.seq_between b e), Hstates.
    clear Hstates.
    induction l; intros Hl; cbn; first done.
    apply Forall_cons in Hl as [Ha Hl].
    apply IHl in Hl.
    destruct Ha as [Ha | Ha].
    - assert (std W !! addr_key π a <> Some Temporary) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Hl. done.
    - assert (std W !! addr_key π a <> Some Permanent) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Permutation_middle -Hl. done.
  Qed.

  Lemma so_object_temporaries_NoDup W π b e :
    NoDup (so_object_temporaries W π b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma so_object_permanents_NoDup W π b e :
    NoDup (so_object_permanents W π b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma open_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
    (l' : list LAddr)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    Forall (fun '(a,p,φ,ρ) => heap_key_live (heap_std W) a) l ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => (std W) !! a = Some ρ) l ->

    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ world_interp_open W C' l' -∗

    ∃ lv,
      world_interp_open W C' (la++l')
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
      ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
      ∗ ⌜ length lv = length la ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
  .
  Proof.
    intros la Hlive.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (????) "(Hrels & [Hr [Hsts Hseals] ])".
    iDestruct (region_open_list W C' l l' with "[$Hrels $Hr $Hsts]") as
      "(% & $ & $ & $ & $ & $ & $ & $)"; auto.
  Qed.

  Lemma close_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (LAddr * Perm * (WORLD * CmptName * LWord → iProp Σ) * region_type))
    (l' : list LAddr)
    (lv : list LWord)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    Forall (fun '(a,p,φ,ρ) => heap_key_live (heap_std W) a) l ->
    length l = length lv ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * LWord, Persistent (φ Wv)) l ->

    world_interp_open W C' (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₖ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ world_interp_open W C' l'.
  Proof.
    intros la Hlive.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (?????) "([Hr $ ] & Hstd & Hv & Hmono & Hφ & Hrel & Hp)".
    iDestruct (region_close_list with "[$Hr $Hstd $Hv $Hmono $Hφ $Hrel $Hp]") as "$"; auto.
  Qed.

End stack_object_helpers.
