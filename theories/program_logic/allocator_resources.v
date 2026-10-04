From iris.proofmode Require Import proofmode.
From griotte Require Export cerise_instance machine_parameters machine_base alloc_registry.
From griotte Require Import region_keys.

(** Case studies start with zeroed free memory and a live shadow entry for
    every heap address. Program memory is kept disjoint from this region. *)
Definition initial_heap_memory `{HeapRegion} : Mem :=
  gset_to_gmap (WInt 0) heap_addresses.

Definition initial_heap_shadow `{HeapRegion} : ShadowTbl :=
  (fun _ => ShadowLive) <$> initial_heap_memory.
