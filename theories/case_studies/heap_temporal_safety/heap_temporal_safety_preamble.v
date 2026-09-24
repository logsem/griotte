From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region switcher assert heap_temporal_safety.
From griotte.allocator Require Export allocator_preamble.

Definition htsN : namespace := nroot .@ "heap_temporal_safety".
Definition hts_assertN : namespace := htsN .@ "assert".
Definition hts_switcherN : namespace := htsN .@ "switcher".

Section Heap_Temporal_Safety_Resources.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} {allocatorg : allocatorG Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP : MachineParameters}.

  Definition hts_buffer (b : Addr) : Word :=
    WCap true RW Global b (b ^+ 1)%a b.

  Definition hts_private_data (p : Addr) (saved : Word) : iProp Σ :=
    p ↦ₐ WInt 0 ∗ (p ^+ 1)%a ↦ₐ saved.

  (** The receipt records original bounds and the reserved header integer,
      but grants no payload access.
      These predicates still require exclusive physical resources. In
      particular, [hts_live_buffer] is not a persistent safe-to-share
      interpretation and cannot survive an
      arbitrary call without a future heap-world protocol. *)
  Definition hts_live_buffer (b : Addr) (reserved : Z) (w : Word) : iProp Σ :=
    ⌜(heap_b < b /\ b < b ^+ 1 /\ b ^+ 1 <= heap_e)%a⌝ ∗
    allocator_allocation b (b ^+ 1)%a reserved ∗ b ↦ₐ w.

  Definition hts_quarantined_buffer (b : Addr) (reserved : Z) : iProp Σ :=
    allocator_allocation b (b ^+ 1)%a reserved ∗ reclaim_token b.

  Lemma hts_private_data_initial p e :
    (p + 2)%a = Some e ->
    [[p, e]] ↦ₐ [[hts_main_data]] ⊣⊢ hts_private_data p (WInt 0).
  Proof.
    intros Hsize.
    rewrite /hts_main_data /hts_private_data.
    rewrite (region_pointsto_cons p (p ^+ 1)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (p ^+ 1)%a e e); [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    simpl. by rewrite right_id.
  Qed.

  Lemma hts_live_buffer_bounds b reserved w :
    hts_live_buffer b reserved w -∗ ⌜is_heap_address b = true⌝.
  Proof.
    iIntros "[%Hbounds _]". iPureIntro.
    apply withinBounds_true_iff. solve_addr.
  Qed.

  Lemma hts_quarantined_buffer_exclusive b reserved :
    hts_quarantined_buffer b reserved -∗ hts_quarantined_buffer b reserved -∗ False.
  Proof. iIntros "[_ H1] [_ H2]"; iApply (reclaim_token_exclusive with "[$] [$]"). Qed.

End Heap_Temporal_Safety_Resources.

Section Heap_Temporal_Safety_Imports.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}
    `{!switcherLayout} `{!assertLayout} `{!allocatorLayout}.

  Lemma hts_main_imports_length adv_f : length (hts_main_imports adv_f) = 5.
  Proof. reflexivity. Qed.

  Lemma hts_main_imports_pointsto b e adv_f :
    (b + 5)%a = Some e ->
    [[b, e]] ↦ₐ [[hts_main_imports adv_f]] ⊣⊢
      b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call
      ∗ (b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert
      ∗ (b ^+ 2)%a ↦ₐ WSealed ot_switcher adv_f
      ∗ (b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global)
      ∗ (b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global)
      ∗ region_pointsto (b ^+ 5)%a e [].
  Proof.
    intros Hsize. rewrite /hts_main_imports.
    rewrite (region_pointsto_cons b (b ^+ 1)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 1)%a (b ^+ 2)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 2)%a (b ^+ 3)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 3)%a (b ^+ 4)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 4)%a (b ^+ 5)%a e); [|solve_addr|solve_addr].
    done.
  Qed.
End Heap_Temporal_Safety_Imports.
