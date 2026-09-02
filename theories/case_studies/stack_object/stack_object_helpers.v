From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From griotte Require Import region_invariants_revocation region_invariants_allocation.
From griotte Require Export world_ghost_theory.

Section stack_object_helpers.

  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
  .
  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (* TODO This theorem is essentially [reinstate_world], but with different RevokedResources *)
  (* Lemma reinstate_close_list W W' C' (l : list Addr) : *)
  (*   related_sts_pub_world W (close_list l W') -> *)
  (*   world_interp W' C' ∗ (close_list_resources C' W l false) *)
  (*   ==∗ *)
  (*   world_interp (reinstate W' l) C'. *)
  (* Proof. *)
  (*   rewrite world_interp_eq /world_interp_def. *)
  (*   iIntros (Hrelated) "( [Hr Hsts] & Htemp)". *)
  (*   iMod (monotone_close_list_region with "[] [$Hsts $Hr $Htemp]") as "[$ $]"; auto. *)
  (* Qed. *)

  Definition so_object_addresses (b e : Addr) :=
    finz.seq_between b e.

  Definition so_object_temporaries (W : WORLD) (b e : Addr) :=
    filter
      (fun a => std W !! a = Some Temporary)
      (so_object_addresses b e).

  Definition so_object_permanents (W : WORLD) (b e : Addr) :=
    filter
      (fun a => std W !! a = Some Permanent)
      (so_object_addresses b e).

  Definition so_revoked_without_object
      (W : WORLD) (b e : Addr) (l : list Addr) :=
    filter
      (fun a => a ∉ so_object_temporaries W b e)
      l.

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

  Lemma so_object_addresses_partition W b e :
    Forall
      (fun a =>
         std W !! a = Some Permanent \/
         std W !! a = Some Temporary)
      (so_object_addresses b e) ->
    so_object_addresses b e
      ≡ₚ so_object_permanents W b e ++
          so_object_temporaries W b e.
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
    - assert (std W !! a <> Some Temporary) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Hl. done.
    - assert (std W !! a <> Some Permanent) as Ha'
        by (intro; simplify_map_eq).
      rewrite (decide_True _ _ Ha); auto.
      rewrite (decide_False _ _ Ha'); auto.
      cbn. rewrite -Permutation_middle -Hl. done.
  Qed.

  Lemma so_object_temporaries_NoDup W b e :
    NoDup (so_object_temporaries W b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma so_object_permanents_NoDup W b e :
    NoDup (so_object_permanents W b e).
  Proof.
    apply NoDup_filter, finz_seq_between_NoDup.
  Qed.

  Lemma open_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => (std W) !! a = Some ρ) l ->

    ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ world_interp_open W C' l' -∗

    ∃ lv,
      world_interp_open W C' (la++l')
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
      ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
      ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
      ∗ ⌜ length lv = length la ⌝
      ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
  .
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (????) "(Hrels & [Hr Hsts])".
    iDestruct (region_open_list W C' l l' with "[$Hrels $Hr $Hsts]") as
      "(% & $ & $ & $ & $ & $ & $ & $)"; auto.
  Qed.

  Lemma close_world_interp_list (W : WORLD) (C' : CmptName)
    (l : list (Addr * Perm * (WORLD * CmptName * Word → iProp Σ) * region_type))
    (l' : list Addr)
    (lv : list Word)
    :

    let la  := (fmap (fun '(a,p,φ,ρ) => a) l) in
    length l = length lv ->
    NoDup la ->
    la ## l' ->
    Forall (fun '(a,p,φ,ρ) => ρ ≠ Revoked) l ->
    Forall (fun '(a,p,φ,ρ) => ∀ Wv : WORLD * CmptName * Word, Persistent (φ Wv)) l ->

    world_interp_open W C' (la++l')
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, sts_state_std C' a ρ)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, a ↦ₐ v)
    ∗ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, monotonicity_guarantees_region C' φ p v ρ)
    ∗ ▷ ([∗ list] '(a,p,φ,ρ) ; v ∈ l ; lv, φ (W,C',v))
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l, rel C' a p φ)
    ∗ ([∗ list] '(a,p,φ,ρ) ∈ l , ⌜ isO p = false ⌝)
      -∗ world_interp_open W C' l'.
  Proof.
    intros la.
    rewrite world_interp_open_eq /world_interp_open_def.
    iIntros (?????) "([Hr $] & Hstd & Hv & Hmono & Hφ & Hrel & Hp)".
    iDestruct (region_close_list with "[$Hr $Hstd $Hv $Hmono $Hφ $Hrel $Hp]") as "$"; auto.
  Qed.

End stack_object_helpers.
