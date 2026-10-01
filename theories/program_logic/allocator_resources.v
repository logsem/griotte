From iris.algebra Require Import gset gmap excl auth.
From iris.base_logic.lib Require Import ghost_map.
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

Class allocatorHistoryG Σ := {
  allocator_history_inG :: ghost_mapG Σ Addr (Addr * (Z * Z));
  allocator_history_gname : gname;
}.

Definition allocator_historyΣ : gFunctors := ghost_mapΣ Addr (Addr * (Z * Z)).

Definition allocator_allocation {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}
    (b e : Addr) (reserved : Z * Z) : iProp Σ :=
  @ghost_map_elem Σ Addr (Addr * (Z * Z)) _ _ allocator_history_inG
    allocator_history_gname b DfracDiscarded (e, reserved).

Class allocator_preG Σ := {
  allocator_token_inG :: inG Σ (gset_disjUR Addr);
  allocator_history_preG :: ghost_mapG Σ Addr (Addr * (Z * Z));
}.

Class allocatorG Σ := {
  allocator_preG_inG :: allocator_preG Σ;
  allocator_name : gname;
  allocator_free_name : gname;
  allocator_right_name : gname;
  allocator_historyG_instance :: allocatorHistoryG Σ;
}.

Definition allocator_history_empty {Σ : gFunctors} {allocatorg : allocatorG Σ} : iProp Σ :=
  @ghost_map_auth Σ Addr (Addr * (Z * Z)) _ _
    (@allocator_history_inG Σ (@allocator_historyG_instance Σ allocatorg))
    (@allocator_history_gname Σ (@allocator_historyG_instance Σ allocatorg))
    1 (∅ : gmap Addr (Addr * (Z * Z))).

Definition allocator_preΣ : gFunctors := #[GFunctor (gset_disjUR Addr); allocator_historyΣ].

#[global] Instance subG_allocator_preΣ {Σ} :
  subG allocator_preΣ Σ -> allocator_preG Σ.
Proof. solve_inG. Qed.

(** Owner identifiers. An allocator capability points to a word holding an
    owner identifier. The exclusive token [allocator_owner_id id S] grants the
    authority to act as owner [id]; specifications require it together with the
    matching physical owner word. The set [S] is an exact view of the bases
    allocated by owner [id]; the authoritative copy [allocator_owners O] is kept
    by the allocator service. Exclusivity makes owner identifiers of distinct
    token holders distinct. *)
Class allocatorOwnerPreG Σ := {
  allocator_owner_preG_inG :: inG Σ (authR (gmapUR Z (exclR (gsetO Addr))));
}.

Class allocatorOwnerG Σ := {
  allocator_owner_inG :: allocatorOwnerPreG Σ;
  allocator_owner_name : gname;
}.

Definition allocator_ownerΣ : gFunctors :=
  #[GFunctor (authR (gmapUR Z (exclR (gsetO Addr))))].

#[global] Instance subG_allocator_ownerΣ {Σ} :
  subG allocator_ownerΣ Σ -> allocatorOwnerPreG Σ.
Proof. solve_inG. Qed.

Section AllocatorOwner.
  Context {Σ : gFunctors} {allocator_ownerg : allocatorOwnerG Σ}.

  Definition allocator_owners (O : gmap Z (gset Addr)) : iProp Σ :=
    own allocator_owner_name (● (Excl <$> O : gmap Z (excl (gset Addr)))).

  Definition allocator_owner_id (id : Z) (S : gset Addr) : iProp Σ :=
    own allocator_owner_name (◯ {[id := Excl S]}).

  #[global] Instance allocator_owners_timeless O : Timeless (allocator_owners O).
  Proof. apply _. Qed.

  #[global] Instance allocator_owner_id_timeless id S : Timeless (allocator_owner_id id S).
  Proof. apply _. Qed.

  Lemma allocator_owner_id_exclusive id S1 S2 :
    allocator_owner_id id S1 -∗ allocator_owner_id id S2 -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite auth_frag_valid singleton_op singleton_valid in Hvalid.
    by destruct Hvalid.
  Qed.

  Lemma allocator_owner_id_ne id1 id2 S1 S2 :
    allocator_owner_id id1 S1 -∗ allocator_owner_id id2 S2 -∗ ⌜id1 ≠ id2⌝.
  Proof.
    iIntros "H1 H2" (->). iApply (allocator_owner_id_exclusive with "H1 H2").
  Qed.

  Lemma allocator_owners_agree O id S :
    allocator_owners O -∗ allocator_owner_id id S -∗ ⌜O !! id = Some S⌝.
  Proof.
    iIntros "HO Hid". iDestruct (own_valid_2 with "HO Hid") as %Hvalid.
    apply auth_both_valid_discrete in Hvalid as [Hincl Hvalid].
    apply singleton_included_exclusive_l in Hincl; [|apply _|done].
    rewrite lookup_fmap in Hincl.
    destruct (O !! id) as [S'|]; simpl in Hincl; last by inversion Hincl.
    apply (inj Some), (inj Excl) in Hincl. iPureIntro. f_equal.
    by apply leibniz_equiv.
  Qed.

  Lemma allocator_owners_update O id S b :
    allocator_owners O ∗ allocator_owner_id id S
    ==∗
    allocator_owners (<[id := S ∪ {[b]}]> O) ∗ allocator_owner_id id (S ∪ {[b]}).
  Proof.
    iIntros "[HO Hid]".
    iDestruct (allocator_owners_agree with "HO Hid") as %HS.
    rewrite /allocator_owners /allocator_owner_id -own_op.
    iApply (own_update_2 with "HO Hid").
    apply auth_update. rewrite fmap_insert.
    eapply singleton_local_update.
    - by rewrite lookup_fmap HS.
    - by apply exclusive_local_update.
  Qed.
End AllocatorOwner.

Section AllocatorOwnerInit.
  Context {Σ : gFunctors} `{!allocatorOwnerPreG Σ}.

  (** Allocate the authoritative owner map and one empty token for each
      identifier of the finite set [ids]. *)
  Lemma allocator_owners_init (ids : gset Z) :
    ⊢ |==> ∃ og : allocatorOwnerG Σ,
      @allocator_owners Σ og (gset_to_gmap ∅ ids) ∗
      [∗ set] id ∈ ids, @allocator_owner_id Σ og id ∅.
  Proof.
    iMod (own_alloc (● (Excl <$> gset_to_gmap ∅ ids : gmap Z (excl (gset Addr))) ⋅
                     ◯ (Excl <$> gset_to_gmap ∅ ids : gmap Z (excl (gset Addr)))))
      as (γ) "[HO Hids]".
    { apply auth_both_valid_discrete. split; first done.
      intros i. rewrite lookup_fmap.
      by destruct (gset_to_gmap ∅ ids !! i). }
    iModIntro. iExists {| allocator_owner_name := γ |}. iFrame "HO".
    iInduction ids as [|id ids Hid] "IH" using set_ind_L; first done.
    rewrite big_sepS_union; last set_solver.
    rewrite big_sepS_singleton gset_to_gmap_union_singleton fmap_insert.
    rewrite insert_singleton_op; last first.
    { rewrite lookup_fmap lookup_gset_to_gmap option_guard_False //. }
    rewrite auth_frag_op own_op. iDestruct "Hids" as "[$ Hids]". by iApply "IH".
  Qed.
End AllocatorOwnerInit.

(** Rights to free. Every allocated object has one exclusive right, keyed by
    its base. The allocator service keeps the pool of rights of the addresses
    that were never allocated; the world holds the right of every quarantined
    object. *)
Section FreeRights.
  Context {Σ : gFunctors} {allocatorg : allocatorG Σ}.

  Definition free_right (b : Addr) : iProp Σ :=
    own allocator_right_name (GSet {[b]}).

  Definition free_rights_pool (B : gset Addr) : iProp Σ :=
    own allocator_right_name (GSet B).

  #[global] Instance free_right_timeless b : Timeless (free_right b).
  Proof. apply _. Qed.

  #[global] Instance free_rights_pool_timeless B : Timeless (free_rights_pool B).
  Proof. apply _. Qed.

  Lemma free_right_exclusive b :
    free_right b -∗ free_right b -∗ False.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite gset_disj_valid_op in Hvalid. set_solver.
  Qed.

  Lemma free_rights_pool_split B b :
    b ∈ B ->
    free_rights_pool B ⊣⊢ free_right b ∗ free_rights_pool (B ∖ {[b]}).
  Proof.
    intros Hb. rewrite /free_right /free_rights_pool -own_op gset_disj_union;
      last set_solver.
    by rewrite -union_difference_singleton_L.
  Qed.
End FreeRights.

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
      keeps these tokens for its unused suffix and the reserved first address. *)
  Definition free_addr_token (a : Addr) : iProp Σ :=
    own allocator_free_name (GSet {[a]}).

  Definition allocator_state_resources (a : Addr) (s : AllocState) : iProp Σ :=
    match s with
    | Free => a ↦ₐ - ∗ reclaim_token a
    | Live => reclaim_token a ∗ free_addr_token a
    | Quarantined => a ↦ₐ - ∗ free_addr_token a
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
  Lemma free_addr_token_exclusive a :
    free_addr_token a -∗ free_addr_token a -∗ False.
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
    allocator_entry a s -∗ free_addr_token a -∗ ⌜s = Free⌝.
  Proof.
    iIntros "[_ Hres] Hfree". destruct s; simpl; first done.
    all: iDestruct "Hres" as "[_ Hfree']";
      iDestruct (free_addr_token_exclusive with "Hfree Hfree'") as %[].
  Qed.

  Lemma allocator_entry_allocate a :
    allocator_entry a Free -∗ free_addr_token a -∗
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

  #[global] Instance free_addr_token_timeless a : Timeless (free_addr_token a).
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
  Lemma free_addr_tokens_split (A : gset Addr) :
    own allocator_free_name (GSet A) -∗ [∗ set] a ∈ A, free_addr_token a.
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

  (** Initialization supplies every heap address and its corresponding shadow
      entry. The state map determines which resources remain with the client:
      live addresses return their memory, quarantined addresses return their tokens,
      and free addresses keep both resources in the invariant. *)
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
      | Free => free_addr_token a
      | Live | Quarantined => emp
      end)%I.

  Lemma allocator_init_with_free_tokens E (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    allocator_initial_resources m ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP ∗ @allocator_client_resources ag m ∗
      @allocator_initial_free_tokens ag m ∗
      @allocator_history_empty Σ ag ∗
      @free_rights_pool Σ ag heap_addresses.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (own_alloc (GSet (dom m))) as (γ) "Htokens"; first done.
    iMod (own_alloc (GSet (dom m))) as (γfree) "Hfree"; first done.
    iMod (own_alloc (GSet heap_addresses)) as (γright) "Hrights"; first done.
    iMod (ghost_map_alloc_empty (K := Addr) (V := (Addr * (Z * Z))%type))
      as (γhistory) "Hhistory".
    pose (hg := {| allocator_history_inG := allocator_history_preG;
                   allocator_history_gname := γhistory |}).
    pose (ag := {| allocator_preG_inG := allocator_preG0; allocator_name := γ;
                  allocator_free_name := γfree;
                  allocator_right_name := γright;
                  allocator_historyG_instance := hg |}).
    iExists ag.
    iDestruct (@reclaim_tokens_split Σ ag with "Htokens") as "Htokens".
    iDestruct (@free_addr_tokens_split Σ ag with "Hfree") as "Hfree".
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
    iModIntro. iFrame "Hclient Halloc Hfree Hhistory Hrights".
  Qed.

  Lemma allocator_init E (m : gmap Addr (AllocState * Word)) :
    dom m = heap_addresses ->
    allocator_initial_resources m ={E}=∗
    ∃ ag : allocatorG Σ, @allocator_ctx Σ _ ag MP ∗ @allocator_client_resources ag m.
  Proof.
    iIntros (Hdom) "Hm".
    iMod (allocator_init_with_free_tokens E m with "Hm") as (ag) "(Halloc & Hclient & _ & _ & _)";
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
