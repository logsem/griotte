From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocator Require Export allocator.
From griotte Require Import memory_region.

(** Resources used by the allocator service. The shared
    allocation states, token families, and heap invariant come
    from [allocator_resources]; there is only one definition of [AllocState]. *)

Section AllocatorRanges.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  Definition free_cells (b e : Addr) : iProp Σ :=
    [∗ list] a ∈ finz.seq_between b e, free_cell_token a.

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

(** Logical entries contain the payload base and both header values:
    [(base, (end, reserved))]. The stored end is also the next header address.
    Checked addition excludes address wraparound when recovering the base. *)

Definition allocator_header_entry : Type := (Addr * (Addr * Z))%type.

Definition allocator_has_bounds (allocations : list allocator_header_entry)
  (b e : Addr) : Prop :=
  ∃ reserved : Z, (b, (e, reserved)) ∈ allocations.

Definition allocator_header_bounds (h stop b e : Addr) : Prop :=
  (h + allocator_header_words)%a = Some b ∧ (b < e /\ e <= stop)%a.

Fixpoint allocator_chain (h stop : Addr)
  (allocations : list allocator_header_entry) : Prop :=
  match allocations with
  | [] => h = stop
  | (b, (e, reserved)) :: rest =>
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

Class allocatorHistoryG Σ := {
  allocator_history_inG :: ghost_mapG Σ Addr (Addr * Z);
  allocator_history_gname : gname;
}.

Definition allocator_historyΣ : gFunctors := ghost_mapΣ Addr (Addr * Z).

Section AllocatorHeaders.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  (** Own both header words with the values named by the logical entry.
      [reserved] is an explicit integer parameter; malloc initializes it to zero. *)

  Definition allocator_header (h b e : Addr) (reserved : Z) : iProp Σ :=
    (⌜(h + allocator_header_words)%a = Some b⌝ ∗
     h ↦ₐ WInt e ∗
     (h ^+ 1)%a ↦ₐ WInt reserved)%I.

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
      [(102, (106, r1)); (108, (111, r2))]. Unfolding owns the header at 100,
      then the header at 106, then the pure endpoint equality [111 = 111].

      Traversal frames a visited prefix and recurses on the remaining suffix.
      Malloc appends a singleton segment at the old bump pointer. *)

  Fixpoint allocator_headers (h stop : Addr)
    (allocations : list allocator_header_entry) : iProp Σ :=
    match allocations with
    | [] => ⌜h = stop⌝%I
    | (b, (e, reserved)) :: rest =>
        (⌜(b < e /\ e <= stop)%a⌝ ∗
         allocator_header h b e reserved ∗
         allocator_headers e stop rest)%I
    end.

  Global Instance allocator_headers_timeless h stop allocations :
    Timeless (allocator_headers h stop allocations).
  Proof.
    revert h. induction allocations as [| (b & e & reserved) rest IH];
      intros h; simpl; apply _.
  Qed.

End AllocatorHeaders.

Section AllocatorHistory.
  Context {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}.

  Definition allocator_history (allocations : list allocator_header_entry) : iProp Σ :=
    ghost_map_auth allocator_history_gname 1 (list_to_map allocations).

  Definition allocator_allocation (b e : Addr) (reserved : Z) : iProp Σ :=
    ghost_map_elem allocator_history_gname b DfracDiscarded (e, reserved).

End AllocatorHistory.

(** The service invariant can remain open across an entire allocator call.
    Its namespace is a sibling of [Nallocator], so atomic shadow access to the
    shared heap invariant remains available while service resources are held. *)

Definition Nallocator_service : namespace := nroot .@ "allocator_service".

Section AllocatorService.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters} {layout : allocatorLayout}.

  Definition allocator_service_static : iProp Σ :=
    ([[allocator_pcc_b, allocator_code_b]] ↦ₐ [[allocator_imports]] ∗
     codefrag allocator_code_b allocator_code)%I.

  Context {allocator_historyg : allocatorHistoryG Σ}.

  (** The reserved first cell is never allocated or quarantined. Keeping its
      free-cell token proves that the heap capability's base has a clear bit.
      The other tokens identify the unused suffix; the shared invariant owns
      its memory. [next = heap_e] represents an exhausted heap. *)

  Definition allocator_service_data (next : Addr) : iProp Σ :=
    (∃ allocations : list allocator_header_entry,
     ⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗ (* Bump bounds. *)
     allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗ (* Bump slot. *)
     free_cell_token heap_b ∗ (* Root stays unquarantined. *)
     free_cells next heap_e ∗ (* Unused suffix. *)
     allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Physical header chain. *)
     allocator_history allocations)%I. (* Matching ghost map. *)

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
     free_cell_token heap_b ∗ (* Root stays unquarantined. *)
     free_cells e heap_e ∗ (* Remaining unused suffix. *)
     allocator_headers (heap_b ^+ 1)%a next allocations ∗ (* Published header chain. *)
     allocator_history allocations ∗ (* Published ghost map. *)
     allocator_header next b e 0)%I. (* New, unpublished header. *)

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
