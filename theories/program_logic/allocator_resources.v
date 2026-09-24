From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From griotte Require Export cerise_instance machine_parameters machine_base.

(** The allocator owns one shadow entry for every address of the heap.
    [Free] and [Live] both have a live shadow status; only [Quarantined] causes
    loading a capability based at that address to clear its tag. *)
Inductive AllocState := Free | Live | Quarantined.

#[global] Instance alloc_state_inhabited : Inhabited AllocState := populate Free.

Definition heap_addresses `{HeapRegion} : gset Addr :=
  list_to_set (finz.seq_between heap_b heap_e).

(** Case studies start with zeroed free memory and a live shadow entry for
    every heap address. Program memory is kept disjoint from this region. *)
Definition initial_heap_memory `{HeapRegion} : Mem :=
  gset_to_gmap (WInt 0) heap_addresses.

Definition initial_heap_shadow `{HeapRegion} : ShadowTbl :=
  (fun _ => ShadowLive) <$> initial_heap_memory.

Definition shadow_status (s : AllocState) : AllocStatus :=
  match s with Free | Live => ShadowLive | Quarantined => ShadowQuarantined end.

Lemma elem_of_heap_addresses `{HeapRegion} a :
  a ∈ heap_addresses <-> is_heap_address a = true.
Proof.
  rewrite /heap_addresses elem_of_list_to_set elem_of_finz_seq_between.
  symmetry. apply withinBounds_true_iff.
Qed.

Class allocator_preG Σ := {
  allocator_token_inG :: inG Σ (gset_disjUR Addr);
}.

Class allocatorG Σ := {
  allocator_preG_inG :: allocator_preG Σ;
  allocator_name : gname;
  allocator_free_name : gname;
}.

Definition allocator_preΣ : gFunctors := #[GFunctor (gset_disjUR Addr)].

#[global] Instance subG_allocator_preΣ {Σ} :
  subG allocator_preΣ Σ -> allocator_preG Σ.
Proof. solve_inG. Qed.

Definition Nallocator : namespace := nroot .@ "allocator".

Section Allocator.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  (** The token is exclusive for each heap address. Outside the allocator
      invariant, it witnesses quarantine: both other states keep it inside.
      It does not by itself grant access to the quarantined memory. *)
  Definition reclaim_token (a : Addr) : iProp Σ :=
    own allocator_name (GSet {[a]}).

  (** Outside the shared invariant this token witnesses [Free]. The service
      keeps these tokens for its unused suffix and the reserved first cell. *)
  Definition free_cell_token (a : Addr) : iProp Σ :=
    own allocator_free_name (GSet {[a]}).

  Definition allocator_state_resources (a : Addr) (s : AllocState) : iProp Σ :=
    match s with
    | Free => a ↦ₐ - ∗ reclaim_token a
    | Live => reclaim_token a ∗ free_cell_token a
    | Quarantined => a ↦ₐ - ∗ free_cell_token a
    end%I.

  Definition allocator_entry (a : Addr) (s : AllocState) : iProp Σ :=
    a ↦ₛ shadow_status s ∗ allocator_state_resources a s.

  Definition allocator_inv_body : iProp Σ :=
    ∃ alloc_map : gmap Addr AllocState,
      ⌜dom alloc_map = heap_addresses⌝ ∗
      ([∗ map] a ↦ s ∈ alloc_map, allocator_entry a s).

  Definition allocator_ctx : iProp Σ := inv Nallocator allocator_inv_body.

  #[global] Instance allocator_ctx_persistent : Persistent allocator_ctx.
  Proof. apply _. Qed.

  Lemma reclaim_token_exclusive a :
    reclaim_token a -∗ reclaim_token a -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite gset_disj_valid_op in Hvalid. set_solver.
  Qed.
  Lemma free_cell_token_exclusive a :
    free_cell_token a -∗ free_cell_token a -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite gset_disj_valid_op in Hvalid. set_solver.
  Qed.

  (** These observations are made while the invariant is open. They do not
      expose a persistent assertion about a mutable allocation state. *)
  Lemma allocator_entry_memory_live a s v :
    allocator_entry a s -∗ a ↦ₐ v -∗ ⌜s = Live⌝.
  Proof.
    iIntros "[Hs Hres] Ha". destruct s; simpl.
    - iDestruct "Hres" as "[Hmem _]". iDestruct "Hmem" as (w) "Hmem".
      iDestruct (pointsto_valid_2 with "Ha Hmem") as %[Hbad _]. done.
    - done.
    - iDestruct "Hres" as "[Hmem _]". iDestruct "Hmem" as (w) "Hmem".
      iDestruct (pointsto_valid_2 with "Ha Hmem") as %[Hbad _]. done.
  Qed.

  Lemma allocator_entry_token_quarantined a s :
    allocator_entry a s -∗ reclaim_token a -∗ ⌜s = Quarantined⌝.
  Proof.
    iIntros "[Hs Hres] Htoken". destruct s; simpl.
    - iDestruct "Hres" as "[_ Htoken']".
      iDestruct (reclaim_token_exclusive with "Htoken Htoken'") as %[].
    - iDestruct "Hres" as "[Htoken' _]".
      iDestruct (reclaim_token_exclusive with "Htoken Htoken'") as %[].
    - done.
  Qed.

  Lemma allocator_entry_free_token a s :
    allocator_entry a s -∗ free_cell_token a -∗ ⌜s = Free⌝.
  Proof.
    iIntros "[_ Hres] Hfree". destruct s; simpl; first done.
    all: iDestruct "Hres" as "[_ Hfree']";
      iDestruct (free_cell_token_exclusive with "Hfree Hfree'") as %[].
  Qed.

  Lemma allocator_entry_allocate a :
    allocator_entry a Free -∗ free_cell_token a -∗
    allocator_entry a Live ∗ a ↦ₐ -.
  Proof. iIntros "[Hs [Ha Htoken]] Hfree". iFrame. Qed.

  Lemma allocator_inv_lookup a :
    a ∈ heap_addresses -> allocator_inv_body -∗
    ∃ s, allocator_entry a s ∗
      (∀ s', allocator_entry a s' -∗ allocator_inv_body).
  Proof.
    iIntros (Ha) "Halloc". iDestruct "Halloc" as (m Hdom) "Hm".
    assert (is_Some (m !! a)) as [s Hs].
    { apply elem_of_dom. by rewrite Hdom. }
    iDestruct (big_sepM_delete with "Hm") as "[Ha Hm]"; first exact Hs.
    iExists s. iFrame "Ha". iIntros (s') "Ha".
    iExists (<[a:=s']> m). iSplit.
    { iPureIntro. rewrite dom_insert_L Hdom. set_solver. }
    rewrite big_sepM_insert_delete. iFrame.
  Qed.

  #[global] Instance reclaim_token_timeless a : Timeless (reclaim_token a).
  Proof. apply _. Qed.

  #[global] Instance free_cell_token_timeless a : Timeless (free_cell_token a).
  Proof. apply _. Qed.

  #[global] Instance allocator_state_resources_timeless a s :
    Timeless (allocator_state_resources a s).
  Proof. destruct s; apply _. Qed.

  #[global] Instance allocator_entry_timeless a s : Timeless (allocator_entry a s).
  Proof. apply _. Qed.

  #[global] Instance allocator_inv_body_timeless : Timeless allocator_inv_body.
  Proof. apply _. Qed.

  Lemma reclaim_tokens_split (A : gset Addr) :
    own allocator_name (GSet A) -∗ [∗ set] a ∈ A, reclaim_token a.
  Proof.
    induction A as [|a A Ha IH] using set_ind_L.
    - iIntros "_". done.
    - rewrite big_sepS_union; last set_solver.
      rewrite big_sepS_singleton.
      rewrite -gset_disj_union; last set_solver.
      rewrite own_op. iIntros "[Ha HA]". iFrame "Ha". by iApply IH.
  Qed.
  Lemma free_cell_tokens_split (A : gset Addr) :
    own allocator_free_name (GSet A) -∗ [∗ set] a ∈ A, free_cell_token a.
  Proof.
    induction A as [|a A Ha IH] using set_ind_L.
    - iIntros "_". done.
    - rewrite big_sepS_union; last set_solver.
      rewrite big_sepS_singleton.
      rewrite -gset_disj_union; last set_solver.
      rewrite own_op. iIntros "[Ha HA]". iFrame "Ha". by iApply IH.
  Qed.
End Allocator.

Section Initialization.
  Context {Σ : gFunctors} `{!ceriseG Σ} `{!allocator_preG Σ} `{MP : MachineParameters}.

  (** Initialization supplies every heap cell and its corresponding shadow
      entry. The state map determines which resources remain with the client:
      live cells return their memory, quarantined cells return their tokens,
      and free cells keep both resources in the invariant. *)
  Definition allocator_initial_resources (m : gmap Addr (AllocState * Word)) : iProp Σ :=
    ([∗ map] a ↦ sv ∈ m, a ↦ₐ sv.2 ∗ a ↦ₛ shadow_status sv.1)%I.

  Definition allocator_client_resources {allocatorg : allocatorG Σ}
    (m : gmap Addr (AllocState * Word)) : iProp Σ :=
    ([∗ map] a ↦ sv ∈ m,
      match sv.1 with
      | Free => emp
      | Live => a ↦ₐ sv.2
      | Quarantined => reclaim_token a
      end)%I.

  Definition allocator_initial_free_tokens {allocatorg : allocatorG Σ}
    (m : gmap Addr (AllocState * Word)) : iProp Σ :=
    ([∗ map] a ↦ sv ∈ m,
      match sv.1 with
      | Free => free_cell_token a
      | Live | Quarantined => emp
      end)%I.

  Lemma allocator_init_with_free_tokens E (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    allocator_initial_resources m ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP ∗ @allocator_client_resources ag m ∗
      @allocator_initial_free_tokens ag m.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (own_alloc (GSet (dom m))) as (γ) "Htokens"; first done.
    iMod (own_alloc (GSet (dom m))) as (γfree) "Hfree"; first done.
    pose (ag := {| allocator_preG_inG := allocator_preG0; allocator_name := γ;
                  allocator_free_name := γfree |}).
    iExists ag.
    iDestruct (@reclaim_tokens_split Σ ag with "Htokens") as "Htokens".
    iDestruct (@free_cell_tokens_split Σ ag with "Hfree") as "Hfree".
    iAssert (([∗ map] a ↦ sv ∈ m, @allocator_entry Σ ceriseG0 ag a sv.1) ∗
      @allocator_client_resources ag m ∗ @allocator_initial_free_tokens ag m)%I
      with "[Hm Htokens Hfree]" as "[Hinv [Hclient Hfree]]".
    { rewrite /allocator_initial_resources /allocator_client_resources /allocator_initial_free_tokens -!big_sepM_sep.
      rewrite -!big_sepM_dom.
      iCombine "Hm Htokens Hfree" as "Hm". rewrite -!big_sepM_sep.
      iApply (big_sepM_mono with "Hm").
      iIntros (a [s v] Hlookup) "[[Ha Hs] [Htoken Hfree]]".
      destruct s; simpl; iFrame. }
    iMod (inv_alloc Nallocator E (@allocator_inv_body Σ ceriseG0 ag MP)
      with "[Hinv]") as "#Halloc".
    { iNext. iExists (fst <$> m).
      rewrite dom_fmap_L Hdom big_sepM_fmap. iFrame. done. }
    iModIntro. iFrame "Hclient Halloc Hfree".
  Qed.

  Lemma allocator_init E (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    allocator_initial_resources m ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP ∗ @allocator_client_resources ag m.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (allocator_init_with_free_tokens E m with "Hm") as (ag) "[Halloc [Hclient _]]";
      first done.
    iModIntro. iExists ag. iFrame.
  Qed.

  (** In the initial all-free heap, no memory or tokens escape the invariant. *)
  Lemma allocator_init_free E (mem : gmap Addr Word) :
    dom mem = heap_addresses ->
    ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ ShadowLive) ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (allocator_init E ((fun v => (Free,v)) <$> mem) with "[Hm]")
      as (ag) "[Halloc _]".
    { by rewrite dom_fmap_L. }
    { rewrite /allocator_initial_resources big_sepM_fmap. iExact "Hm". }
    iModIntro. iExists ag. iExact "Halloc".
  Qed.
  Lemma allocator_init_free_maps E :
    ([∗ map] a ↦ v ∈ initial_heap_memory, a ↦ₐ v) -∗
    ([∗ map] a ↦ bit ∈ initial_heap_shadow, a ↦ₛ bit) ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP.
  Proof.
    iIntros "Hm Hs".
    iApply (allocator_init_free E initial_heap_memory).
    { apply dom_gset_to_gmap. }
    rewrite /initial_heap_shadow big_sepM_fmap big_sepM_sep. iFrame.
  Qed.
End Initialization.
