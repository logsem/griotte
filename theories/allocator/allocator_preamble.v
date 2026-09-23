From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte.allocator Require Export allocator.
From griotte Require Import memory_region.

(** Resources used by the allocator service. The shared
    allocation states, token families, heap invariant, and load accessors come
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

Definition allocator_free_valid {MP : MachineParameters}
  (next : Addr) (w : Word) : Prop :=
  ∃ (p : Perm) (g : Locality) (b e a : Addr),
    w = WCap true p g b e a ∧ (heap_b < b /\ b < e /\ e <= next)%a.

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

  (** The reserved first cell is never allocated or quarantined. Keeping its
      free-cell token proves that the heap capability's base has a clear bit.
      The other tokens identify the unused suffix; the shared invariant owns
      its memory. [next = heap_e] represents an exhausted heap. *)
  Definition allocator_service_data (next : Addr) : iProp Σ :=
    (⌜(heap_b < next /\ next <= heap_e)%a⌝ ∗
     allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
     free_cell_token heap_b ∗ free_cells next heap_e)%I.

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
