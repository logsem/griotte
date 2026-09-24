From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec.

(** Trusted calls use [allocator_malloc_valid_correct] at size one and
    [allocator_free_valid_correct] with the singleton containing [&p]. Their
    continuations retain an original-bounds receipt and return physical
    ownership / reclaim tokens, respectively.
    Compose them with [switcher_cc_specification_known_to_known_function];
    neither trusted call requires the private pointer to satisfy [interp].

    The separate unknown-caller entry contracts below follow the service
    boundary in the KVS case study. They must cover arbitrary safe arguments,
    allocation failure, invalid frees, narrowed ranges and repeated free.
    The current physical free proof requires memory ownership, so it cannot
    simply be applied to a capability retained by an unknown compartment. *)

Section Heap_Temporal_Safety_Allocator.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}.

  (** A kernel-checked description of the present blocker. A tagged RW
      capability to even one heap cell cannot satisfy today's [interp]. *)
  Lemma hts_heap_buffer_not_interp W C b :
    (heap_b <= b /\ b < b ^+ 1 /\ b ^+ 1 <= heap_e)%a ->
    interp W C (hts_buffer b) -∗ False.
  Proof.
    iIntros (Hbounds) "Hbuffer".
    iDestruct (interp_cap_disjoint with "Hbuffer") as %[_ Hheap]; first done.
    iPureIntro. apply (Hheap b); apply elem_of_finz_seq_between; solve_addr.
  Qed.

  (** BLOCKED: allocation must extend the heap world and make the zeroed
      result safe to return to an arbitrary caller. The successful branch
      contradicts [hts_heap_buffer_not_interp] with the current relation. *)
  Lemma hts_malloc_entry_spec W C :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_malloc_nargs W C.
  Proof.
  Abort.

  (** BLOCKED: free from an unknown caller needs the shared heap protocol to
      recover live cells or handle already quarantined cells, then reestablish
      the world while invalidating retained aliases. Do not assume exclusive
      points-to ownership merely because the argument is safe to share. *)
  Lemma hts_free_entry_spec W C :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
  Abort.

End Heap_Temporal_Safety_Allocator.
