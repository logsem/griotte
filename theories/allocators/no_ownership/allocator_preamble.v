From iris.algebra Require Import gset.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocators.common Require Export allocator_common_preamble.
From griotte.allocators.no_ownership Require Export allocator.
From griotte Require Import memory_region region_keys.

(** The resources of the allocator service that are specific to this
    allocator. The shared ones are in [allocator_common_preamble]. *)

(** The core invariant of the ghost header entries: the reserved words are 0
    (malloc writes 0 to both, free never reads them), and the identifiers are
    pairwise distinct (each is fresh when malloc issues it). *)
Definition allocator_entries_wf (allocations : list allocator_header_entry) : Prop :=
  Forall (λ '(_, _, reserved, _), reserved = (0%Z, 0%Z)) allocations ∧
  NoDup (allocator_entry_ids allocations).

(** Whole-allocation bounds validity: the bounds of a ghost header entry. It
    also holds after free, since headers are never removed. *)

Definition allocator_free_valid {MP : MachineParameters}
  (next : Addr) (allocations : list allocator_header_entry) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧
    (heap_b < b /\ b < e /\ e <= next)%a ∧ allocator_has_bounds allocations b e.

Section AllocatorService.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {FA : FreeAuth Σ} {MP : MachineParameters} {layout : allocatorLayout}.

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
     ⌜allocator_entries_wf allocations⌝ ∗ (* Reserved words 0, distinct identifiers. *)
     ⌜allocator_cells_wf next allocations live issued Cs⌝ ∗ (* Cursor and claim clauses. *)
     allocator_entries_res live allocations ∗ (* Identifiers and status tokens. *)
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
