From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocator Require Export allocator allocator_owners.
From griotte Require Import memory_region region_keys.

(** Resources used by the allocator service. Its heap cells, their shadow
    entries and address claims, its header chain and its pieces of the status
    tokens are all in its non-atomic service invariant. *)

Section AllocatorRanges.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {MP : MachineParameters}.

  Definition allocator_range_memory (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, a ↦ₐ -.

End AllocatorRanges.

Definition allocator_positive_size (w : Word) : Prop :=
  ∃ n : Z, w = WInt n ∧ (0 < n)%Z.

(** The first two free blocks check only the tag and the allocated prefix.
    Exact allocation identity is checked locally, from the shadow entries
    around the base and the header below it. *)

Definition allocator_free_in_prefix {MP : MachineParameters}
  (next : Addr) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a.

(** Ghost header entries contain the payload base, the header values and the
    allocation identifier: [(base, end, (owner, reserved), ι)]. The physical
    header stores no identifier. The stored end is also the next header address. Checked
    addition excludes address wraparound when recovering the base. *)

Definition allocator_header_entry : Type := (Addr * Addr * (Z * Z) * AId)%type.

Definition allocator_has_bounds (allocations : list allocator_header_entry)
  (b e : Addr) : Prop :=
  ∃ (reserved : Z * Z) (ι : AId), (b, e, reserved, ι) ∈ allocations.

(** The allocation [(b, e)] exists and its header records the owner [o]. *)

Definition allocator_owned_bounds (allocations : list allocator_header_entry)
  (o : Z) (b e : Addr) : Prop :=
  ∃ (r : Z) (ι : AId), (b, e, (o, r), ι) ∈ allocations.

(** The identifiers of the ghost header entries. *)
Definition allocator_entry_ids (allocations : list allocator_header_entry) : list AId :=
  (λ '(_, _, _, ι), ι) <$> allocations.

(** The invariant of the ghost header entries: header word 1 is the owner
    identifier (constrained by [allocator_owners_wf]), the last reserved word
    is 0 (malloc writes 0, free never reads it), and the identifiers are
    pairwise distinct (each is fresh when malloc issues it). *)
Definition allocator_entries_wf (allocations : list allocator_header_entry) : Prop :=
  Forall (λ '(_, _, reserved, _), reserved.2 = 0%Z) allocations ∧
  NoDup (allocator_entry_ids allocations).

(** The header words of the entries: the three words below each payload base.
    They are exactly the painted cells of the heap (D11). *)
Definition allocator_is_header (allocations : list allocator_header_entry)
    (a : Addr) : Prop :=
  ∃ (b e : Addr) reserved ι, (b, e, reserved, ι) ∈ allocations ∧
    (b - allocator_header_words <= a < b)%Z.

Definition allocator_header_bounds (h stop b e : Addr) : Prop :=
  (h + allocator_header_words)%a = Some b ∧ (b < e /\ e <= stop)%a.

Fixpoint allocator_chain (h stop : Addr)
  (allocations : list allocator_header_entry) : Prop :=
  match allocations with
  | [] => h = stop
  | (b, e, _, _) :: rest =>
      allocator_header_bounds h stop b e ∧ allocator_chain e stop rest
  end.

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
    included (D4), and every recorded owner has an entry. *)

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
    for instance the issued set (D31's owner clause). *)

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

Section AllocatorHeaders.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  (** Own the header words with the values named by the logical entry.
      [reserved] holds the owner identifier and the reserved word; malloc
      initializes them to the caller's owner and zero. *)

  Definition allocator_header (h b e : Addr) (reserved : Z * Z) : iProp Σ :=
    (⌜(h + allocator_header_words)%a = Some b⌝ ∗
     h ↦ₐ WInt e ∗
     ((h ^+ 1)%a ↦ₐ WInt reserved.1 ∗
      (h ^+ 2)%a ↦ₐ WInt reserved.2))%I.

  (** A list segment ending at [stop], following the recursive [isList]
      convention in Cerise's [examples/keylist.v]. The empty segment owns no
      memory and equates its endpoints. Unfolding a nonempty segment exposes
      one protected header and its tail, leaving payload ownership outside.
      No later is needed: recursion decreases the finite logical list.

      The link is the first header word: [h ↦ₐ WInt e]. The recursive call
      [allocator_headers e stop rest] starts the next node at that very [e].
      Thus [e] serves as both this payload's exclusive end and the next
      header's address. The owner and reserved words are carried as node data.
      The empty case [h = stop] terminates the chain at the bump pointer.

      For example, with two payloads of lengths four and three:
        header at 100: [106; r1], payload [102, 106)
        header at 106: [111; r2], payload [108, 111)
        stop at 111: no header is read here.
      The physical links are 100 -> 106 -> 111, and the logical list is
      [(102, 106, r1, ι1); (108, 111, r2, ι2)]. Unfolding owns the header at 100,
      then the header at 106, then the pure endpoint equality [111 = 111].

      [free] reads one header, three words below a payload base, through
      [allocator_headers_acc]. Malloc appends a singleton segment at the
      old bump pointer. *)

  Fixpoint allocator_headers (h stop : Addr)
    (allocations : list allocator_header_entry) : iProp Σ :=
    match allocations with
    | [] => ⌜h = stop⌝%I
    | (b, e, reserved, _) :: rest =>
        (⌜(b < e /\ e <= stop)%a⌝ ∗
         allocator_header h b e reserved ∗
         allocator_headers e stop rest)%I
    end.

  Global Instance allocator_headers_timeless h stop allocations :
    Timeless (allocator_headers h stop allocations).
  Proof.
    revert h. induction allocations as [| [ [ [b e] reserved] ι] rest IH];
      intros h; simpl; apply _.
  Qed.

End AllocatorHeaders.

(** The service invariant can remain open across an entire allocator call. *)

Definition Nallocator_service : namespace := nroot .@ "allocator_service".

(** The namespace of the invariants on the allocator's export table entries. *)
Definition allocator_exp_tblN : namespace := nroot .@ "allocator_exports".

(** The core [FreeAuth] instance (D35): the allocator keeps the whole client
    half, and the client holds nothing. It is passed explicitly, never found by
    instance resolution, so that a layer can swap it. *)
Lemma free_auth_core_split {Σ : gFunctors} `{!allocRegistryG Σ} (ι : AId) :
  (ι ↦st{1/2} ALive ∗ emp ⊣⊢ ι ↦st{1/2} ALive)%I.
Proof. by rewrite right_id. Qed.

Definition free_auth_core {Σ : gFunctors} `{!allocRegistryG Σ} : FreeAuth Σ := {|
  free_auth_kept ι := (ι ↦st{1/2} ALive)%I;
  free_auth_held ι := emp%I;
  free_auth_kept_timeless ι := _;
  free_auth_held_timeless ι := _;
  free_auth_split := free_auth_core_split;
|}.

(** The allocator's piece of the status token of [ι] (D17, D35). While [ι] is
    live ([ι ∈ live]), one share and the kept part of the client half; from
    [AQuar] on, the whole token. *)
Section AllocatorTokens.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}.

  Definition allocator_tok (live : gset AId) (ι : AId) (b e : Addr) : iProp Σ :=
    if decide (ι ∈ live)
    then (ι ↦st{share (finz.dist b e)} ALive ∗ free_auth_kept ι)%I
    else (∃ s, ι ↦st{1} s ∗ ι ⊒ AQuar)%I.

  (** One identifier and one token per ghost header entry. *)
  Definition allocator_entries_res (live : gset AId)
      (allocations : list allocator_header_entry) : iProp Σ :=
    [∗ list] entry ∈ allocations,
      let '(b, e, _, ι) := entry in alloc_obj ι b e ∗ allocator_tok live ι b e.

  Global Instance allocator_tok_timeless live ι b e : Timeless (allocator_tok live ι b e).
  Proof. rewrite /allocator_tok. case_decide; apply _. Qed.

  Global Instance allocator_entries_res_timeless live allocations :
    Timeless (allocator_entries_res live allocations).
  Proof.
    apply big_sepL_timeless. intros k [ [ [b e] reserved] ι] _. apply _.
  Qed.

End AllocatorTokens.

(** The per-cell state of the service invariant (§4.8): the address claim,
    the shadow entry and the memory, as far as the allocator holds it. The
    flag [hdr] marks a header word, whose memory is in the header chain; its
    shadow entry is painted, by a pure clause of [allocator_cells_wf]. A
    claimed cell belongs to a live allocation: it is unpainted and its memory
    is with the client. Heap roots and unclaimed non-header cells (the unused
    suffix and revoked payloads) are unpainted, with their memory here. *)
Section AllocatorCells.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  Definition cell_res (a : Addr) (c : AddrClaim) (s : AllocStatus) (hdr : bool) : iProp Σ :=
    addr_alloc a c ∗ a ↦ₛ s ∗
    match c with
    | HeapRoot => ⌜s = ShadowLive⌝ ∗ a ↦ₐ -
    | Unclaimed => if hdr then emp else ⌜s = ShadowLive⌝ ∗ a ↦ₐ -
    | Claimed _ => ⌜s = ShadowLive⌝
    end%I.

  Definition allocator_cells (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) : iProp Σ :=
    [∗ map] a ↦ x ∈ Cs, cell_res a x.1.1 x.1.2 x.2.

  Global Instance cell_res_timeless a c s hdr : Timeless (cell_res a c s hdr).
  Proof. rewrite /cell_res. destruct c; [destruct hdr| |]; apply _. Qed.

  Global Instance allocator_cells_timeless Cs : Timeless (allocator_cells Cs).
  Proof. apply _. Qed.

End AllocatorCells.

(** The pure clauses of the service invariant: every heap address has a
    cell, the heap root, the header words (exactly the painted cells), the cursor
    clause (every cell above the bump cursor is unclaimed, unpainted and not a
    header), the claim/header clause in both directions (the cells of a live
    entry are claimed by its identifier, and every claimed cell lies in the
    range of the live entry carrying its identifier), and the issued set
    (D31), which contains every identifier of the header list. *)
Record allocator_cells_wf {MP : MachineParameters} (next : Addr)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool)) : Prop := {
  acw_dom a : (heap_b <= a < heap_e)%a -> is_Some (Cs !! a);
  acw_root : Cs !! heap_b = Some (HeapRoot, ShadowLive, false);
  acw_cursor a : (next <= a < heap_e)%a -> Cs !! a = Some (Unclaimed, ShadowLive, false);
  acw_live b e reserved ι a :
    (b, e, reserved, ι) ∈ allocations -> ι ∈ live -> (b <= a < e)%a ->
    Cs !! a = Some (Claimed ι, ShadowLive, false);
  acw_claimed a ι s hdr :
    Cs !! a = Some (Claimed ι, s, hdr) ->
    ∃ b e reserved, (b, e, reserved, ι) ∈ allocations ∧ ι ∈ live ∧ (b <= a < e)%a;
  acw_header a c s hdr :
    Cs !! a = Some (c, s, hdr) -> (hdr = true <-> allocator_is_header allocations a);
  acw_painted a c s hdr :
    Cs !! a = Some (c, s, hdr) -> (s = ShadowQuarantined <-> hdr = true);
  acw_live_ids : live ⊆ list_to_set (allocator_entry_ids allocations);
  acw_issued : list_to_set (allocator_entry_ids allocations) ⊆ issued;
}.

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

  Definition allocator_service_static : iProp Σ :=
    ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
     codefrag allocator_code_b allocator_code)%I.

  (** The bump slot holds the identifier-less heap root, whose cursor is the
      first unused address; [next = heap_e] represents an exhausted heap. *)

  Definition allocator_service_data (next : Addr) : iProp Σ :=
    (∃ (allocations : list allocator_header_entry) (live issued : gset AId)
       (Cs : gmap Addr (AddrClaim * AllocStatus * bool)),
     ⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗ (* Bump bounds. *)
     allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗ (* Bump slot. *)
     allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Physical header chain. *)
     ⌜allocator_entries_wf allocations⌝ ∗ (* Reserved word 0, distinct identifiers. *)
     ⌜allocator_cells_wf next allocations live issued Cs⌝ ∗ (* Cursor and claim clauses. *)
     allocator_entries_res live allocations ∗ (* Identifiers and status tokens. *)
     allocator_service_owners allocations ∗ (* Owner map. *)
     allocator_cells Cs)%I. (* Claims, shadow entries and memory of the heap cells. *)

  Definition allocator_service_inv : iProp Σ :=
    allocator_service_static ∗ ∃ next : Addr, allocator_service_data next.

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
    (allocator_service_static ∗
     [[allocator_cgp_b, allocator_cgp_e]] ↦ₐ [[lword_of_word <$> allocator_data]])%I.

End AllocatorServiceInitialization.
