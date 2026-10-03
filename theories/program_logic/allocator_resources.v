From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Import proofmode.
From griotte Require Export cerise_instance machine_parameters machine_base alloc_registry.
From griotte Require Import region_keys.

(** Case studies start with zeroed free memory and a live shadow entry for
    every heap address. Program memory is kept disjoint from this region. *)
Definition initial_heap_memory `{HeapRegion} : Mem :=
  gset_to_gmap (WInt 0) heap_addresses.

Definition initial_heap_shadow `{HeapRegion} : ShadowTbl :=
  (fun _ => ShadowLive) <$> initial_heap_memory.

(** Allocation receipts, keyed by allocation identifier: [ι ↦ (b, e, reserved)].
    They are temporary: worlds keep them until the observation rule replaces
    them as the link between an identifier and the allocator's header. *)
Class allocatorHistoryG Σ := {
  allocator_history_inG :: ghost_mapG Σ AId (Addr * Addr * (Z * Z));
  allocator_history_gname : gname;
}.

Definition allocator_historyΣ : gFunctors := ghost_mapΣ AId (Addr * Addr * (Z * Z)).

Definition allocator_allocation {Σ : gFunctors} {allocator_historyg : allocatorHistoryG Σ}
    (ι : AId) (b e : Addr) (reserved : Z * Z) : iProp Σ :=
  @ghost_map_elem Σ AId (Addr * Addr * (Z * Z)) _ _ allocator_history_inG
    allocator_history_gname ι DfracDiscarded (b, e, reserved).

Class allocator_preG Σ := {
  allocator_history_preG :: ghost_mapG Σ AId (Addr * Addr * (Z * Z));
}.

Class allocatorG Σ := {
  allocator_preG_inG :: allocator_preG Σ;
  allocator_historyG_instance :: allocatorHistoryG Σ;
}.

Definition allocator_history_empty {Σ : gFunctors} {allocatorg : allocatorG Σ} : iProp Σ :=
  @ghost_map_auth Σ AId (Addr * Addr * (Z * Z)) _ _
    (@allocator_history_inG Σ (@allocator_historyG_instance Σ allocatorg))
    (@allocator_history_gname Σ (@allocator_historyG_instance Σ allocatorg))
    1 (∅ : gmap AId (Addr * Addr * (Z * Z))).

Definition allocator_preΣ : gFunctors := #[allocator_historyΣ].

#[global] Instance subG_allocator_preΣ {Σ} :
  subG allocator_preΣ Σ -> allocator_preG Σ.
Proof. solve_inG. Qed.

(** The allocator's shared invariant is empty (D28, D43): its cells, shadow
    entries and freed memory are in the allocator's service invariant, and the
    registry and the address claims in the state interpretation. [Nallocator]
    and [allocator_ctx] remain as placeholders until their pass-through users
    outside the allocator drop them. *)
Definition Nallocator : namespace := nroot .@ "allocator".

Section Allocator.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {MP : MachineParameters}.

  Definition allocator_ctx : iProp Σ := True.

  #[global] Instance allocator_ctx_persistent : Persistent allocator_ctx.
  Proof. apply _. Qed.

  #[global] Instance allocator_ctx_timeless : Timeless allocator_ctx.
  Proof. apply _. Qed.
End Allocator.

Section Initialization.
  Context {Σ : gFunctors} `{!allocator_preG Σ}.

  (** Allocates the allocator's ghost state: an empty receipt history. *)
  Lemma allocator_init :
    ⊢ |==> ∃ ag : allocatorG Σ, @allocator_history_empty Σ ag.
  Proof.
    iMod (ghost_map_alloc_empty (K := AId) (V := (Addr * Addr * (Z * Z))%type))
      as (γhistory) "Hhistory".
    pose (hg := {| allocator_history_inG := allocator_history_preG;
                   allocator_history_gname := γhistory |}).
    iModIntro. iExists {| allocator_preG_inG := _; allocator_historyG_instance := hg |}.
    iExact "Hhistory".
  Qed.
End Initialization.
