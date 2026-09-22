From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From griotte Require Export cerise_instance machine_parameters machine_base.

(** The allocator owns one shadow entry for every address of the heap.
    [Free] and [Live] both have a clear shadow bit; only [Quarantined] causes
    loading a capability based at that address to clear its tag. *)
Inductive AllocState := Free | Live | Quarantined.

#[global] Instance alloc_state_inhabited : Inhabited AllocState := populate Free.

Definition heap_addresses `{HeapRegion} : gset Addr :=
  list_to_set (finz.seq_between heap_b heap_e).

(** Case studies start with zeroed free memory and a clear shadow entry for
    every heap address. Program memory is kept disjoint from this region. *)
Definition initial_heap_memory `{HeapRegion} : Mem :=
  gset_to_gmap (WInt 0) heap_addresses.

Definition initial_heap_shadow `{HeapRegion} : ShadowTbl :=
  (fun _ => false) <$> initial_heap_memory.

Definition shadow_bit (s : AllocState) : bool :=
  match s with Free | Live => false | Quarantined => true end.

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
}.

Definition allocator_preΣ : gFunctors := #[GFunctor (gset_disjUR Addr)].

#[global] Instance subG_allocator_preΣ {Σ} :
  subG allocator_preΣ Σ -> allocator_preG Σ.
Proof. solve_inG. Qed.

Definition Nallocator : namespace := nroot .@ "allocator".

Section Allocator.
  Context {Σ : gFunctors} `{!ceriseG Σ} `{!allocatorG Σ} `{MP : MachineParameters}.

  (** The token is exclusive for each heap address. Outside the allocator
      invariant, it witnesses quarantine: both other states keep it inside.
      It does not by itself grant access to the quarantined memory. *)
  Definition reclaim_token (a : Addr) : iProp Σ :=
    own allocator_name (GSet {[a]}).

  Definition allocator_state_resources (a : Addr) (s : AllocState) : iProp Σ :=
    match s with
    | Free => a ↦ₐ - ∗ reclaim_token a
    | Live => reclaim_token a
    | Quarantined => a ↦ₐ -
    end%I.

  Definition allocator_entry (a : Addr) (s : AllocState) : iProp Σ :=
    a ↦ₛ shadow_bit s ∗ allocator_state_resources a s.

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
  (** These observations are made while the invariant is open. They do not
      expose a persistent assertion about a mutable allocation state. *)
  Lemma allocator_entry_memory_live a s v :
    allocator_entry a s -∗ a ↦ₐ v -∗ ⌜s = Live⌝.
  Proof.
    iIntros "[Hs Hres] Ha". destruct s; simpl.
    - iDestruct "Hres" as "[Hmem _]". iDestruct "Hmem" as (w) "Hmem".
      iDestruct (pointsto_valid_2 with "Ha Hmem") as %[Hbad _]. done.
    - done.
    - iDestruct "Hres" as (w) "Hmem".
      iDestruct (pointsto_valid_2 with "Ha Hmem") as %[Hbad _]. done.
  Qed.

  Lemma allocator_entry_token_quarantined a s :
    allocator_entry a s -∗ reclaim_token a -∗ ⌜s = Quarantined⌝.
  Proof.
    iIntros "[Hs Hres] Htoken". destruct s; simpl.
    - iDestruct "Hres" as "[_ Htoken']".
      iDestruct (reclaim_token_exclusive with "Htoken Htoken'") as %[].
    - iDestruct (reclaim_token_exclusive with "Htoken Hres") as %[].
    - done.
  Qed.

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

  (** A reusable read accessor borrows the entry for one atomic instruction.
      Its bit may differ at the next use, but each use returns the same bit
      before re-enabling [Nallocator]. All other entries remain in the closure. *)
  Definition allocator_shadow_access (a : Addr) : iProp Σ :=
    (□ ∀ E : coPset, ⌜↑Nallocator ⊆ E⌝ -∗
       |={E,E ∖ ↑Nallocator}=> ∃ bit : bool,
       ▷ (a ↦ₛ bit) ∗ (▷ (a ↦ₛ bit) ={E ∖ ↑Nallocator,E}=∗ emp))%I.

  Lemma allocator_ctx_shadow_access a :
    a ∈ heap_addresses -> allocator_ctx -∗ allocator_shadow_access a.
  Proof.
    iIntros (Ha) "#Halloc". iModIntro. iIntros (E) "%HE".
    iInv Nallocator as "Hbody" "Hclose".
    iDestruct (allocator_inv_lookup a with "Hbody") as (s) "[[Hs Hres] Hput]"; first done.
    iModIntro. iExists (shadow_bit s). iFrame "Hs".
    iIntros "Hs". iMod ("Hclose" with "[Hs Hres Hput]").
    { iNext. iApply ("Hput" $! s). iFrame. }
    done.
  Qed.
  #[global] Instance reclaim_token_timeless a : Timeless (reclaim_token a).
  Proof. apply _. Qed.

  #[global] Instance allocator_state_resources_timeless a s :
    Timeless (allocator_state_resources a s).
  Proof. destruct s; apply _. Qed.

  #[global] Instance allocator_entry_timeless a s : Timeless (allocator_entry a s).
  Proof. apply _. Qed.

  #[global] Instance allocator_inv_body_timeless : Timeless allocator_inv_body.
  Proof. apply _. Qed.

  (** An evidence-carrying accessor returns its linear resource after each
      use. Keeping memory proves that the bit is clear; keeping the reclaim
      token proves that it is set. The accessor itself is persistent, so the
      same evidence can serve successive loads, including aliased bases. *)
  Definition allocator_shadow_access_with (a : Addr)
    (saved_heap_allocated_resources : iProp Σ) (P : bool -> Prop) : iProp Σ :=
   (□ ∀ E : coPset, ⌜↑Nallocator ⊆ E⌝ -∗
   saved_heap_allocated_resources ={E,E ∖ ↑Nallocator}=∗ ∃ bit : bool,
   ⌜P bit⌝ ∗ ▷ (a ↦ₛ bit) ∗
   (▷ (a ↦ₛ bit) ={E ∖ ↑Nallocator,E}=∗ saved_heap_allocated_resources))%I.
  Lemma allocator_ctx_shadow_access_with a :
   a ∈ heap_addresses ->
   allocator_ctx -∗ allocator_shadow_access_with a emp (fun _ => True%type).
  Proof.
   iIntros (Ha) "#Halloc".
   iDestruct (allocator_ctx_shadow_access a with "Halloc") as "#Haccess"; first done.
   iModIntro. iIntros (E HE) "_".
   iMod ("Haccess" $! E HE) as (bit) "[Hs Hclose]".
   iModIntro. iExists bit. iSplit; first done. iFrame.
  Qed.

  Lemma allocator_memory_shadow_access a v :
   a ∈ heap_addresses ->
   allocator_ctx -∗ allocator_shadow_access_with a (a ↦ₐ v) (fun bit => bit = false).
  Proof.
   iIntros (Ha) "#Halloc". iModIntro. iIntros (E HE) "Ha".
   iInv Nallocator as ">Hbody" "Hclose".
   iDestruct (allocator_inv_lookup a with "Hbody") as (s) "[Hentry Hput]"; first done.
   iDestruct (allocator_entry_memory_live with "Hentry Ha") as %->.
   iDestruct "Hentry" as "[Hs Hres]".
   iModIntro. iExists false. iSplit; first done. iFrame "Hs".
   iIntros "Hs". iMod ("Hclose" with "[Hs Hres Hput]").
   { iNext. iApply ("Hput" $! Live). iFrame. }
   iModIntro. iFrame.
  Qed.
  Lemma allocator_token_shadow_access a :
   a ∈ heap_addresses ->
   allocator_ctx -∗ allocator_shadow_access_with a (reclaim_token a) (fun bit => bit = true).
  Proof.
   iIntros (Ha) "#Halloc". iModIntro. iIntros (E HE) "Ha".
   iInv Nallocator as ">Hbody" "Hclose".
   iDestruct (allocator_inv_lookup a with "Hbody") as (s) "[Hentry Hput]"; first done.
   iDestruct (allocator_entry_token_quarantined with "Hentry Ha") as %->.
   iDestruct "Hentry" as "[Hs Hres]".
   iModIntro. iExists true. iSplit; first done. iFrame "Hs".
   iIntros "Hs". iMod ("Hclose" with "[Hs Hres Hput]").
   { iNext. iApply ("Hput" $! Quarantined). iFrame. }
   iModIntro. iFrame.
  Qed.
  Lemma allocator_shadow_access_with_frame a saved_heap_allocated_resources P S :
   allocator_shadow_access_with a saved_heap_allocated_resources P -∗ allocator_shadow_access_with a (saved_heap_allocated_resources ∗ S) P.
  Proof.
   iIntros "#Haccess". iModIntro. iIntros (E HE) "[HR HS]".
   iMod ("Haccess" $! E HE with "HR") as (bit HP) "[Hs Hclose]".
   iModIntro. iExists bit. iSplit; first done. iFrame "Hs".
   iIntros "Hs". iMod ("Hclose" with "Hs") as "HR". iModIntro. iFrame.
  Qed.
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
End Allocator.

Section Initialization.
  Context {Σ : gFunctors} `{!ceriseG Σ} `{!allocator_preG Σ} `{MP : MachineParameters}.

  (** Initialization supplies every heap cell and its corresponding shadow
      entry. The state map determines which resources remain with the client:
      live cells return their memory, quarantined cells return their tokens,
      and free cells keep both resources in the invariant. *)
  Definition allocator_initial_resources (m : gmap Addr (AllocState * Word)) : iProp Σ :=
    ([∗ map] a ↦ sv ∈ m, a ↦ₐ sv.2 ∗ a ↦ₛ shadow_bit sv.1)%I.

  Definition allocator_client_resources `{!allocatorG Σ}
    (m : gmap Addr (AllocState * Word)) : iProp Σ :=
    ([∗ map] a ↦ sv ∈ m,
      match sv.1 with
      | Free => emp
      | Live => a ↦ₐ sv.2
      | Quarantined => reclaim_token a
      end)%I.

  Lemma allocator_init E (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    allocator_initial_resources m ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP ∗ @allocator_client_resources ag m.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (own_alloc (GSet (dom m))) as (γ) "Htokens"; first done.
    pose (ag := {| allocator_preG_inG := allocator_preG0; allocator_name := γ |}).
    iExists ag.
    iDestruct (@reclaim_tokens_split Σ ag with "Htokens") as "Htokens".
    iAssert (([∗ map] a ↦ sv ∈ m, @allocator_entry Σ ceriseG0 ag a sv.1) ∗
      @allocator_client_resources ag m)%I with "[Hm Htokens]" as "[Hinv Hclient]".
    { rewrite /allocator_initial_resources /allocator_client_resources -big_sepM_sep.
      rewrite -big_sepM_dom.
      iCombine "Hm Htokens" as "Hm". rewrite -big_sepM_sep.
      iApply (big_sepM_mono with "Hm").
      iIntros (a [s v] Hlookup) "[[Ha Hs] Htoken]".
      destruct s; simpl; iFrame. }
    iMod (inv_alloc Nallocator E (@allocator_inv_body Σ ceriseG0 ag MP)
      with "[Hinv]") as "#Halloc".
    { iNext. iExists (fst <$> m).
      rewrite dom_fmap_L Hdom big_sepM_fmap. iFrame. done. }
    iModIntro. iFrame "Hclient Halloc".
  Qed.

  (** In the initial all-free heap, no memory or tokens escape the invariant. *)
  Lemma allocator_init_free E (mem : gmap Addr Word) :
    dom mem = heap_addresses ->
    ([∗ map] a ↦ v ∈ mem, a ↦ₐ v ∗ a ↦ₛ false) ={E}=∗
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
