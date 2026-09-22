From griotte Require Import addresses.

(** Entries are keyed by heap addresses. Direct accesses through a capability
    into the shadow region use [shadow_to_heap] to obtain this key. Loading a
    heap capability consults its base directly. *)
Definition ShadowTbl := gmap Addr bool.
