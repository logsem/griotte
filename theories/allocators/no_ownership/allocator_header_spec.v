From iris.proofmode Require Import proofmode.
From griotte.allocators.no_ownership Require Import allocator_preamble.
From griotte.allocators.common Require Export allocator_common_header_spec.
From griotte Require Import proofmode region_keys.

(** The facts on the header chain and the cells shared by the allocators are
    in [allocator_common_header_spec]. *)

Lemma allocator_entries_wf_snoc allocations b e ι :
  ι ∉ allocator_entry_ids allocations ->
  allocator_entries_wf allocations ->
  allocator_entries_wf (allocations ++ [(b, e, (0%Z, 0%Z), ι)]).
Proof.
  intros Hι [Hzero Hnodup]. split.
  - apply Forall_app. split; first done. by repeat constructor.
  - rewrite allocator_entry_ids_app. apply list.NoDup_app. split; first done.
    split.
    + intros ι' Hin Hin'. cbn in Hin'. apply list_elem_of_singleton in Hin'. by subst.
    + cbn. apply NoDup_singleton.
Qed.

