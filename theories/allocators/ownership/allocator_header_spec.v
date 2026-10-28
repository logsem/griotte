From iris.proofmode Require Import proofmode.
From griotte.allocators.ownership Require Import allocator_preamble.
From griotte.allocators.common Require Export allocator_common_header_spec.
From griotte Require Import proofmode region_keys.

(** The facts on the header chain and the cells shared by the allocators are
    in [allocator_common_header_spec]. *)

Lemma allocator_entries_wf_snoc allocations b e o ι :
  ι ∉ allocator_entry_ids allocations ->
  allocator_entries_wf allocations ->
  allocator_entries_wf (allocations ++ [(b, e, (o, 0%Z), ι)]).
Proof.
  intros Hι [Hzero Hnodup]. split.
  - apply Forall_app. split; first done. by repeat constructor.
  - rewrite allocator_entry_ids_app. apply list.NoDup_app. split; first done.
    split.
    + intros ι' Hin Hin'. cbn in Hin'. apply list_elem_of_singleton in Hin'. by subst.
    + cbn. apply NoDup_singleton.
Qed.

Section AllocatorHeaderContracts.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}.

  (** The first two header words of an entry: its recorded end and owner. *)
  Lemma allocator_headers_acc :
    ∀ h stop allocations (b e : Addr) o r ι,
      (b, e, (o, r), ι) ∈ allocations ->
      allocator_headers h stop allocations ⊢
      (b ^+ (- allocator_header_words)) ↦ₐ WInt e ∗
      ((b ^+ (- allocator_header_words)) ^+ 1) ↦ₐ WInt o ∗
      ((b ^+ (- allocator_header_words)) ↦ₐ WInt e -∗
       ((b ^+ (- allocator_header_words)) ^+ 1) ↦ₐ WInt o -∗
       allocator_headers h stop allocations).
  Proof.
    intros h stop allocations. revert h.
    induction allocations as [| [ [ [b0 e0] r0] ι0] rest IH];
      intros h b e o r ι Hin; simpl.
    - set_solver.
    - rewrite elem_of_cons in Hin. destruct Hin as [Heq|Hin].
      + injection Heq as <- <- <- <-.
        iIntros "(%Hbounds & (%Hbase & Hend & Howner & Hreserved) & Htail)".
        assert (b ^+ (- allocator_header_words) = h) as ->
          by (unfold allocator_header_words in *; solve_addr).
        iFrame "Hend Howner". iIntros "Hend Howner". iFrame. done.
      + iIntros "(%Hbounds & Hhead & Htail)".
        iDestruct (IH with "Htail") as "(Hend & Howner & Hclose)"; first exact Hin.
        iFrame "Hend Howner". iIntros "Hend Howner". iFrame. iSplit; first done.
        iApply ("Hclose" with "Hend Howner").
  Qed.

End AllocatorHeaderContracts.
