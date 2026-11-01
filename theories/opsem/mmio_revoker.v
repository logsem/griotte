From griotte Require Import machine_base.

(** The revoker is a memory-mapped device at a single address, outside the
    heap and the shadow region. A store to it sweeps memory; a load from it
    reads as zero. *)
Class RevokerRegion := {
    revoker_addr : Addr;
  }.

Definition is_revoker_address `{RevokerRegion} (a : Addr) : bool :=
  bool_decide (a = revoker_addr).

Lemma is_revoker_address_spec `{RevokerRegion} a :
  is_revoker_address a = true <-> a = revoker_addr.
Proof. rewrite /is_revoker_address. apply bool_decide_eq_true. Qed.
