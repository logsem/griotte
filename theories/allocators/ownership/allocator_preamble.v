From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocators.common Require Export allocator_common_preamble.
From griotte.allocators.ownership Require Export allocator allocator_owners.
From griotte Require Import memory_region region_keys named_props_extra.

(** The resources of the allocator service that are specific to this
    allocator. The shared ones are in [allocator_common_preamble]. *)

(** The allocation [(b, e)] exists and its header records the owner [o]. *)

Definition allocator_owned_bounds (allocations : list allocator_header_entry)
  (o : Z) (b e : Addr) : Prop :=
  ∃ (r : Z) (ι : AId), (b, e, (o, r), ι) ∈ allocations.

(** The invariant of the ghost header entries: header word 1 is the owner
    identifier (constrained by [allocator_owners_wf]), the last reserved word
    is 0 (malloc writes 0, free never reads it), and the identifiers are
    pairwise distinct (each is fresh when malloc issues it). *)
Definition allocator_entries_wf (allocations : list allocator_header_entry) : Prop :=
  Forall (λ '(_, _, reserved, _), reserved.2 = 0%Z) allocations ∧
  NoDup (allocator_entry_ids allocations).

(** Whole-allocation bounds validity for the owner [o]: the bounds of a ghost
    header entry recorded with [o]. It also holds after free, since headers
    are never removed. *)

Definition allocator_free_valid {MP : MachineParameters}
  (next : Addr) (allocations : list allocator_header_entry) (o : Z) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧
    (heap_b < b /\ b < e /\ e <= next)%a ∧ allocator_owned_bounds allocations o b e.

(** The identifiers of the entries recorded with owner [id]. *)

Definition allocator_owner_ids (allocations : list allocator_header_entry)
  (id : Z) : gset AId :=
  list_to_set (allocator_entry_ids
    (filter (λ entry : allocator_header_entry, entry.1.2.1 = id) allocations)).

(** The authoritative owner map [O] is an exact view of the header list:
    each owner's set holds every identifier it has ever allocated, freed ones
    included, and every recorded owner has an entry. *)

Definition allocator_owners_wf (O : gmap Z (gset AId))
  (allocations : list allocator_header_entry) : Prop :=
  (∀ id Ω, O !! id = Some Ω -> Ω = allocator_owner_ids allocations id) ∧
  (∀ b e id r ι, (b, e, (id, r), ι) ∈ allocations -> id ∈ dom O).

Lemma allocator_owners_wf_empty (ids : gset Z) :
  allocator_owners_wf (gset_to_gmap ∅ ids) [].
Proof.
  split.
  - intros id Ω Hlookup. apply lookup_gset_to_gmap_Some in Hlookup as [_ <-].
    done.
  - intros b e id r ι Hin. set_solver.
Qed.

Lemma allocator_owners_wf_snoc O allocations id Ω b e r ι :
  allocator_owners_wf O allocations ->
  O !! id = Some Ω ->
  allocator_owners_wf (<[id := Ω ∪ {[ι]}]> O) (allocations ++ [(b, e, (id, r), ι)]).
Proof.
  intros [Hexact Hdom] HΩ. split.
  - intros id' Ω' Hlookup.
    rewrite /allocator_owner_ids list.filter_app /allocator_entry_ids fmap_app list_to_set_app_L.
    rewrite -/(allocator_entry_ids _) -/(allocator_owner_ids allocations id').
    rewrite lookup_insert_Some in Hlookup.
    destruct Hlookup as [ [<- <-]|[Hne Hlookup] ].
    + rewrite filter_cons_True //= (Hexact _ _ HΩ). set_solver.
    + rewrite filter_cons_False /=; last done.
      rewrite (Hexact _ _ Hlookup). set_solver.
  - intros b' e' id' r' ι' Hin. rewrite dom_insert_L elem_of_union elem_of_singleton.
    apply elem_of_app in Hin as [Hin|Hin].
    + right. by eapply Hdom.
    + left. apply list_elem_of_singleton in Hin. by simplify_eq.
Qed.

(** From a header entry to membership: the owner set of the recorded owner
    contains the entry's identifier. *)

Lemma allocator_owners_wf_lookup O allocations b e id r ι Ω :
  allocator_owners_wf O allocations ->
  (b, e, (id, r), ι) ∈ allocations ->
  O !! id = Some Ω ->
  ι ∈ Ω.
Proof.
  intros [Hexact _] Hin HΩ.
  rewrite (Hexact _ _ HΩ) /allocator_owner_ids /allocator_entry_ids elem_of_list_to_set.
  apply list_elem_of_fmap. exists (b, e, (id, r), ι). split; first done.
  by apply list_elem_of_filter.
Qed.

(** The converse, from membership to the owner recorded in the header entry
    of an identifier: with distinct identifiers, the entry carrying [ι] is
    the one counted in the owner set. *)

Lemma allocator_owners_wf_member O allocations b e o r ι id Ω :
  allocator_owners_wf O allocations ->
  NoDup (allocator_entry_ids allocations) ->
  (b, e, (o, r), ι) ∈ allocations ->
  O !! id = Some Ω ->
  ι ∈ Ω ->
  o = id.
Proof.
  intros [Hexact _] Hnodup Hin HΩ Hmem.
  rewrite (Hexact _ _ HΩ) /allocator_owner_ids /allocator_entry_ids elem_of_list_to_set in Hmem.
  apply list_elem_of_fmap in Hmem as ( [ [ [b' e'] [o' r'] ] ι'] & Heq & Hin').
  simpl in Heq. subst ι'.
  apply list_elem_of_filter in Hin' as [Ho Hin']. simpl in Ho. subst o'.
  apply list_elem_of_lookup in Hin as [i Hi].
  apply list_elem_of_lookup in Hin' as [j Hj].
  assert (i = j) as <-.
  { eapply NoDup_lookup; [exact Hnodup| |].
    - rewrite /allocator_entry_ids list_lookup_fmap Hi //.
    - rewrite /allocator_entry_ids list_lookup_fmap Hj //. }
  rewrite Hi in Hj. by simplify_eq.
Qed.

(** Every owner set is contained in any superset of the entry identifiers,
    for instance the issued set. *)

Lemma allocator_owners_wf_subset O allocations id Ω (issued : gset AId) :
  allocator_owners_wf O allocations ->
  list_to_set (allocator_entry_ids allocations) ⊆ issued ->
  O !! id = Some Ω ->
  Ω ⊆ issued.
Proof.
  intros [Hexact _] Hissued HΩ. rewrite (Hexact _ _ HΩ).
  etrans; last exact Hissued.
  rewrite /allocator_owner_ids /allocator_entry_ids.
  intros ι. rewrite !elem_of_list_to_set !list_elem_of_fmap.
  intros (x & -> & Hx). exists x. split; first done.
  by apply list_elem_of_filter in Hx as [_ Hx].
Qed.

Section AllocatorService.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {FA : FreeAuth Σ} {allocator_ownerg : allocatorOwnerG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** The authoritative owner map, an exact view of the header list. *)

  Definition allocator_service_owners
    (allocations : list allocator_header_entry) : iProp Σ :=
    (∃ O : gmap Z (gset AId),
     allocator_owners O ∗
     ⌜allocator_owners_wf O allocations⌝)%I.

  (** The read-only memory of the service, its imports and its code, is
      persistent: it is not in the invariant. *)
  Definition allocator_service_static : iProp Σ :=
    ([[allocator_pcc_b, allocator_code_b]] ↦ₐ□ [[lword_of_word <$> allocator_imports]] ∗
     codefrag_pers allocator_code_b allocator_code)%I.

  #[global] Instance allocator_service_static_persistent :
    Persistent allocator_service_static.
  Proof. apply _. Qed.

  (** The bump slot holds the identifier-less heap root, whose cursor is the
      first unused address; [next = heap_e] represents an exhausted heap. *)

  Definition allocator_service_data (next : Addr) : iProp Σ :=
    (∃ (allocations : list allocator_header_entry) (live issued : gset AId)
       (Cs : gmap Addr (AddrClaim * AllocStatus * bool)),
     "%Hnext" ∷ ⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗ (* Bump bounds. *)
     "Hslot" ∷ allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗ (* Bump slot. *)
     "Hheaders" ∷ allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Physical header chain. *)
     "%Hwf" ∷ ⌜allocator_entries_wf allocations⌝ ∗ (* Reserved word 0, distinct identifiers. *)
     "%Hcwf" ∷ ⌜allocator_cells_wf next allocations live issued Cs⌝ ∗ (* Cursor and claim clauses. *)
     "Htoks" ∷ allocator_entries_res live allocations ∗ (* Identifiers and status tokens. *)
     "Howners" ∷ allocator_service_owners allocations ∗ (* Owner map. *)
     "Hcells" ∷ allocator_cells Cs)%I. (* Claims, shadow entries and memory of the heap cells. *)

  Definition allocator_service_inv : iProp Σ :=
    ∃ next : Addr, allocator_service_data next.

  Definition allocator_service_ctx : iProp Σ :=
    na_inv cerise_nais Nallocator_service allocator_service_inv.

End AllocatorService.

Section AllocatorServiceInitialization.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Like KVS initialization, service initialization consumes only imports,
      code, and data. The enclosing system retains the export table to allocate
      the switcher's ordinary PCC, CGP, and entry invariants separately. *)

  Definition allocator_service_initial_resources : iProp Σ :=
    ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
     codefrag allocator_code_b allocator_code ∗
     [[allocator_cgp_b, allocator_cgp_e]] ↦ₐ [[lword_of_word <$> allocator_data]])%I.

End AllocatorServiceInitialization.
