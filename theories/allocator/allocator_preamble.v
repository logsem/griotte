From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocator Require Export allocator.
From griotte Require Import memory_region region_keys.

(** Resources used by the allocator service. The shared
    allocation states, token families, and heap invariant come
    from [allocator_resources]; there is only one definition of [AllocState]. *)

Section AllocatorRanges.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  Definition free_addrs (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, free_addr_token a.

  Definition allocator_range_memory (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, a ↦ₐ -.

  Definition allocator_zeroed (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, a ↦ₐ WInt 0.

  Definition allocator_reclaimed (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, reclaim_token a.

End AllocatorRanges.

Definition allocator_positive_size (w : Word) : Prop :=
  ∃ n : Z, w = WInt n ∧ (0 < n)%Z.

(** The first two free blocks check only the tag and the allocated prefix.
    Exact allocation identity is checked by traversing the header list. *)

Definition allocator_free_in_prefix {MP : MachineParameters}
  (next : Addr) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a.

(** Ghost header entries contain the payload base, both header values and the
    allocation identifier: [(base, end, reserved, ι)]. The physical header stores
    no identifier. The stored end is also the next header address. Checked
    addition excludes address wraparound when recovering the base. *)

Definition allocator_header_entry : Type := (Addr * Addr * (Z * Z) * AId)%type.

Definition allocator_has_bounds (allocations : list allocator_header_entry)
  (b e : Addr) : Prop :=
  ∃ (reserved : Z * Z) (ι : AId), (b, e, reserved, ι) ∈ allocations.

(** The identifiers of the ghost header entries. *)
Definition allocator_entry_ids (allocations : list allocator_header_entry) : list AId :=
  (λ '(_, _, _, ι), ι) <$> allocations.

(** The core invariant of the ghost header entries: the reserved words are 0
    (malloc writes 0 to both, free never reads them), and the identifiers are
    pairwise distinct (each is fresh when malloc issues it). *)
Definition allocator_entries_wf (allocations : list allocator_header_entry) : Prop :=
  Forall (λ '(_, _, reserved, _), reserved = (0%Z, 0%Z)) allocations ∧
  NoDup (allocator_entry_ids allocations).

(** The receipts' authority, keyed by identifier. *)
Definition allocator_history_map (allocations : list allocator_header_entry) :
  gmap AId (Addr * Addr * (Z * Z)) :=
  list_to_map ((λ '(b, e, reserved, ι), (ι, (b, e, reserved))) <$> allocations).

Definition allocator_header_bounds (h stop b e : Addr) : Prop :=
  (h + allocator_header_words)%a = Some b ∧ (b < e /\ e <= stop)%a.

Fixpoint allocator_chain (h stop : Addr)
  (allocations : list allocator_header_entry) : Prop :=
  match allocations with
  | [] => h = stop
  | (b, e, _, _) :: rest =>
      allocator_header_bounds h stop b e ∧ allocator_chain e stop rest
  end.

(** Whole-allocation bounds validity. Successful free additionally requires a
    live shadow observation; this historical predicate also holds after free. *)

Definition allocator_free_valid {MP : MachineParameters}
  (next : Addr) (allocations : list allocator_header_entry) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧
    (heap_b < b /\ b < e /\ e <= next)%a ∧ allocator_has_bounds allocations b e.

(** Immutable header receipts use service-specific ghost state. Each base maps
    to both the original end and the reserved integer. The current allocator
    preserves both fields after initialization. Receipts record metadata, not
    liveness or authority to access the payload. *)

Section AllocatorHeaders.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  (** Own both header words with the values named by the logical entry.
      [reserved] is an explicit integer parameter; malloc initializes it to zero. *)

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
      header's address. The reserved second word is carried as node data.
      The empty case [h = stop] terminates the chain at the bump pointer.

      For example, with two payloads of lengths four and three:
        header at 100: [106; r1], payload [102, 106)
        header at 106: [111; r2], payload [108, 111)
        stop at 111: no header is read here.
      The physical links are 100 -> 106 -> 111, and the logical list is
      [(102, 106, r1, ι1); (108, 111, r2, ι2)]. Unfolding owns the header at 100,
      then the header at 106, then the pure endpoint equality [111 = 111].

      Traversal frames a visited prefix and recurses on the remaining suffix.
      Malloc appends a singleton segment at the old bump pointer. *)

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

Section AllocatorHistory.
  Context {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}.

  Definition allocator_history (allocations : list allocator_header_entry) : iProp Σ :=
    @ghost_map_auth Σ AId (Addr * Addr * (Z * Z)) _ _ allocator_history_inG
      allocator_history_gname 1 (allocator_history_map allocations).

End AllocatorHistory.

(** The service invariant can remain open across an entire allocator call.
    Its namespace is a sibling of [Nallocator], so atomic shadow access to the
    shared heap invariant remains available while service resources are held. *)

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
    live, one share and the kept part of the client half; from [AQuar] on, the
    whole token. *)
Section AllocatorTokens.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}.

  Definition allocator_tok (ι : AId) (b e : Addr) : iProp Σ :=
    ((ι ↦st{share (finz.dist b e)} ALive ∗ free_auth_kept ι) ∨
     (∃ s, ι ↦st{1} s ∗ ι ⊒ AQuar))%I.

  (** One identifier and one token per ghost header entry. *)
  Definition allocator_entries_res (allocations : list allocator_header_entry) : iProp Σ :=
    [∗ list] entry ∈ allocations,
      let '(b, e, _, ι) := entry in alloc_obj ι b e ∗ allocator_tok ι b e.

  Global Instance allocator_tok_timeless ι b e : Timeless (allocator_tok ι b e).
  Proof. apply _. Qed.

  Global Instance allocator_entries_res_timeless allocations :
    Timeless (allocator_entries_res allocations).
  Proof.
    apply big_sepL_timeless. intros k [ [ [b e] reserved] ι] _. apply _.
  Qed.

End AllocatorTokens.

Section AllocatorService.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {FA : FreeAuth Σ} {MP : MachineParameters} {layout : allocatorLayout}.

  Definition allocator_service_static : iProp Σ :=
    ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[allocator_imports]] ∗
     codefrag allocator_code_b allocator_code)%I.

  (** The reserved first address is never allocated or quarantined. Keeping its
      free-address token proves that the heap capability's base has a clear bit.
      The other tokens identify the unused suffix; the shared invariant owns
      its memory. [next = heap_e] represents an exhausted heap. *)

  Definition allocator_service_data (next : Addr) : iProp Σ :=
    (∃ allocations : list allocator_header_entry,
     ⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗ (* Bump bounds. *)
     allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗ (* Bump slot. *)
     free_addr_token heap_b ∗ (* Root stays unquarantined. *)
     free_addrs next heap_e ∗ (* Unused suffix. *)
     allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Physical header chain. *)
     allocator_history allocations ∗ (* Matching ghost map. *)
     ⌜allocator_entries_wf allocations⌝ ∗ (* Reserved words 0, distinct identifiers. *)
     allocator_entries_res allocations)%I. (* Identifiers and status tokens. *)

  (** After malloc's prepare block, the new header has been written and the
      whole chunk has been taken from the free suffix. The bump slot and
      published history still describe the old prefix. Payload memory is held
      separately for zeroing; publishing appends the header and issues a receipt.
      This predicate is held while the service invariant is open. *)

  Definition allocator_service_pending (next b e : Addr) : iProp Σ :=
    (∃ allocations : list allocator_header_entry,
     ⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗ (* Old bump bounds. *)
     ⌜allocator_header_bounds next heap_e b e⌝ ∗ (* New chunk bounds. *)
     allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗ (* Old bump slot. *)
     free_addr_token heap_b ∗ (* Root stays unquarantined. *)
     free_addrs e heap_e ∗ (* Remaining unused suffix. *)
     allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Published header chain. *)
     allocator_history allocations ∗ (* Published ghost map. *)
     ⌜allocator_entries_wf allocations⌝ ∗ (* Published entries' invariant. *)
     allocator_entries_res allocations ∗ (* Published identifiers and tokens. *)
     allocator_header next b e (0%Z, 0%Z))%I. (* New, unpublished header. *)

  Definition allocator_service_inv : iProp Σ :=
    allocator_service_static ∗ ∃ next : Addr, allocator_service_data next.

  Definition allocator_service_ctx : iProp Σ :=
    na_inv cerise_nais Nallocator_service allocator_service_inv.

End AllocatorService.

Section AllocatorServiceInitialization.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocator_preg : allocator_preG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  (** Like KVS initialization, service initialization consumes only imports,
      code, and data. The enclosing system retains the export table to allocate
      the switcher's ordinary PCC, CGP, and entry invariants separately. *)

  Definition allocator_service_initial_resources : iProp Σ :=
    (allocator_service_static ∗
     [[allocator_cgp_b, allocator_cgp_e]] ↦ₐ [[allocator_data]])%I.

End AllocatorServiceInitialization.
