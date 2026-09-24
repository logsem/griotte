From iris.proofmode Require Import proofmode.
From griotte Require Export heap_std allocator_resources.

(** Outside the physical heap, ordinary region resources are unchanged.
    An unrecorded heap address cannot be an active shared cell. *)
Definition heap_cell_status `{HeapRegion} (W_heap : Heap) (a : Addr) : option AllocObjectStatus :=
  if is_heap_address a then
    alloc_object_status ∘ snd <$> heap_lookup_addr W_heap a
  else Some AllocObjectLive.

Definition heap_cell_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  heap_cell_status W_heap a = Some AllocObjectLive.

Section heap_region.
  Context {Σ : gFunctors} {allocatorg : allocatorG Σ} `{HeapRegion}.

  Definition heap_cell_resource (W_heap : Heap) (a : Addr) (P : iProp Σ) : iProp Σ :=
    (if is_heap_address a then
       match heap_lookup_addr W_heap a with
       | None => False
       | Some (_, o) =>
           match alloc_object_status o with
           | AllocObjectLive => P
           | AllocObjectQuarantined => reclaim_token a
           end
       end
     else P)%I.

  Lemma heap_cell_resource_status W_heap a P :
    heap_cell_resource W_heap a P =
    (match heap_cell_status W_heap a with
     | Some AllocObjectLive => P
     | Some AllocObjectQuarantined => reclaim_token a
     | None => False
     end)%I.
  Proof.
    rewrite /heap_cell_resource /heap_cell_status.
    destruct (is_heap_address a); last done.
    destruct (heap_lookup_addr W_heap a) as [[base obj]|]; done.
  Qed.

  Global Instance heap_cell_resource_ne W_heap a : NonExpansive (heap_cell_resource W_heap a).
  Proof. intros n P Q HPQ. rewrite !heap_cell_resource_status.
    destruct (heap_cell_status W_heap a) as [[]|]; done. Qed.

  Lemma heap_cell_resource_live W_heap a P :
    heap_cell_live W_heap a -> heap_cell_resource W_heap a P = P.
  Proof. intros Ha. by rewrite heap_cell_resource_status Ha. Qed.

  Lemma heap_cell_resource_live_elim W_heap a P :
    heap_cell_live W_heap a -> heap_cell_resource W_heap a P -∗ P.
  Proof. intros Ha. rewrite (heap_cell_resource_live _ _ _ Ha). iIntros "$". Qed.

  Lemma heap_cell_resource_live_intro W_heap a P :
    heap_cell_live W_heap a -> P -∗ heap_cell_resource W_heap a P.
  Proof. intros Ha. rewrite (heap_cell_resource_live _ _ _ Ha). iIntros "$". Qed.

  Lemma heap_cell_resource_quarantined W_heap a P :
    heap_cell_status W_heap a = Some AllocObjectQuarantined ->
    heap_cell_resource W_heap a P = reclaim_token a.
  Proof. intros Ha. by rewrite heap_cell_resource_status Ha. Qed.

  Lemma heap_cell_resource_mono W_heap a P Q :
    (P -∗ Q) -∗ heap_cell_resource W_heap a P -∗ heap_cell_resource W_heap a Q.
  Proof.
    rewrite !heap_cell_resource_status. destruct (heap_cell_status W_heap a) as [[]|];
      iIntros "HPQ HP"; try done. by iApply "HPQ".
  Qed.
End heap_region.

Lemma heap_cell_live_nonheap `{HeapRegion} W_heap a :
  is_heap_address a = false -> heap_cell_live W_heap a.
Proof. intros Ha. by rewrite /heap_cell_live /heap_cell_status Ha. Qed.

Lemma heap_cell_live_lookup `{HeapRegion} W_heap a b o :
  heap_lookup_addr W_heap a = Some (b,o) ->
  alloc_object_status o = AllocObjectLive -> heap_cell_live W_heap a.
Proof.
  intros Ha Ho. rewrite /heap_cell_live /heap_cell_status.
  destruct (is_heap_address a); last done. by rewrite Ha /= Ho.
Qed.

(** The explicit cases used by list interfaces allow non-heap and live-heap
    addresses to occur together. *)
Definition heap_cell_nonheap_or_live `{HeapRegion} (W_heap : Heap) (a : Addr) : Prop :=
  is_heap_address a = false ∨
  (is_heap_address a = true ∧ ∃ base obj,
    heap_lookup_addr W_heap a = Some (base,obj) ∧
    alloc_object_status obj = AllocObjectLive).

Lemma heap_cell_live_cases `{HeapRegion} W_heap a :
  heap_cell_live W_heap a ↔ heap_cell_nonheap_or_live W_heap a.
Proof.
  rewrite /heap_cell_live /heap_cell_status /heap_cell_nonheap_or_live.
  destruct (is_heap_address a) eqn:Hheap; last naive_solver.
  destruct (heap_lookup_addr W_heap a) as [[base obj]|] eqn:Hlookup;
    last naive_solver.
  cbn. destruct (alloc_object_status obj) eqn:Hstatus.
  - split; last done. intros _. right. split; first done. exists base,obj. done.
  - split; first discriminate. intros [Hfalse|[_ (base' & obj' & Heq & Hlive)]].
    + discriminate.
    + simplify_eq. congruence.
Qed.

Lemma heap_cells_live_cases `{HeapRegion} W_heap l :
  Forall (heap_cell_live W_heap) l ↔ Forall (heap_cell_nonheap_or_live W_heap) l.
Proof. rewrite !Forall_forall. setoid_rewrite heap_cell_live_cases. done. Qed.

(** At an untrusted execution boundary, the resources for every cell in each
    recorded allocation establish whole-block agreement with the physical
    allocator. This assertion is not imposed while trusted code is painting. *)
From griotte Require Import heap_allocator.

Section heap_region_agreement.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    `{MP : MachineParameters}.

  Definition heap_payload_resources (W_heap : Heap) : iProp Σ :=
    [∗ map] base ↦ obj ∈ W_heap,
      [∗ list] a ∈ finz.seq_between base (alloc_object_end obj),
        heap_cell_resource W_heap a (a ↦ₐ -).

  Lemma heap_cell_resource_allocator_agree W_heap a s :
    is_heap_address a = true ->
    heap_cell_resource W_heap a (a ↦ₐ -) -∗ allocator_entry a s -∗
    ⌜∃ status, heap_cell_status W_heap a = Some status ∧
       s = alloc_object_cell_state status⌝.
  Proof.
    intros Hheap. rewrite heap_cell_resource_status.
    destruct (heap_cell_status W_heap a) as [status|] eqn:Hstatus;
      last by iIntros "[]".
    destruct status.
    - iIntros "[%w Hw] Hentry".
      iDestruct (allocator_entry_memory_live with "Hentry Hw") as %->.
      iPureIntro. exists AllocObjectLive. done.
    - iIntros "Htoken Hentry".
      iDestruct (allocator_entry_token_quarantined with "Hentry Htoken") as %->.
      iPureIntro. exists AllocObjectQuarantined. done.
  Qed.

  Lemma heap_payload_resources_allocator_agree W_heap allocations alloc_map :
    heap_wf W_heap ->
    alloc_object_end <$> W_heap = fst <$> list_to_map allocations ->
    (∀ base obj a, W_heap !! base = Some obj -> alloc_object_contains base obj a ->
       is_heap_address a = true) ->
    dom alloc_map = heap_addresses ->
    heap_payload_resources W_heap -∗
    ([∗ map] a ↦ s ∈ alloc_map, allocator_entry a s) -∗
    ⌜heap_std_allocator_agree W_heap allocations alloc_map⌝.
  Proof.
    iIntros (Hwf Hbounds Hheap Hdom) "Hcells Halloc".
    iAssert (∀ base obj a, ⌜W_heap !! base = Some obj⌝ →
      ⌜alloc_object_contains base obj a⌝ →
      ⌜alloc_map !! a = Some (alloc_object_cell_state (alloc_object_status obj))⌝)%I
      as %Hagree.
    { iIntros (base obj a Hobj Ha).
      have Haddr := Hheap base obj a Hobj Ha.
      have Hlookup := heap_lookup_addr_complete W_heap a base obj Hwf Hobj Ha.
      iDestruct (big_sepM_lookup with "Hcells") as "Hobj"; first exact Hobj.
      iDestruct (big_sepL_elem_of with "Hobj") as "Hcell".
      { by apply elem_of_finz_seq_between. }
      assert (is_Some (alloc_map !! a)) as [s Hs].
      { apply elem_of_dom. rewrite Hdom elem_of_heap_addresses. done. }
      iDestruct (big_sepM_lookup with "Halloc") as "Hentry"; first exact Hs.
      iDestruct (heap_cell_resource_allocator_agree with "Hcell Hentry")
        as %(status & Hstatus & ->); first exact Haddr.
      rewrite /heap_cell_status Haddr Hlookup /= in Hstatus.
      iPureIntro. congruence. }
    iPureIntro. split; first exact Hwf. split; assumption.
  Qed.
End heap_region_agreement.
