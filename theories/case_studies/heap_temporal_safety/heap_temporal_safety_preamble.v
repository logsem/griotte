From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region switcher assert heap_temporal_safety region_keys.
From griotte.allocator Require Export allocator_preamble.

Definition htsN : namespace := nroot .@ "heap_temporal_safety".
Definition hts_assertN : namespace := htsN .@ "assert".
Definition hts_switcherN : namespace := htsN .@ "switcher".

Section Heap_Temporal_Safety_Resources.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Definition hts_buffer (b : Addr) : Word :=
    WCap true RW Global b (b ^+ 1)%a b.

  Lemma hts_private_data_initial p e :
    (p + 1)%a = Some e ->
    [[p, e]] ↦ₐ [[lword_of_word <$> hts_main_data]] ⊣⊢ p ↦ₐ WInt 0.
  Proof.
    intros Hsize.
    rewrite /hts_main_data.
    rewrite (region_pointsto_cons p e e); [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    simpl. by rewrite right_id.
  Qed.

End Heap_Temporal_Safety_Resources.

Section Heap_Temporal_Safety_Imports.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}
    `{!switcherLayout} `{!assertLayout} `{!allocatorLayout}.

  Lemma hts_main_imports_length owner_a adv_f :
    length (hts_main_imports owner_a adv_f) = 6.
  Proof. reflexivity. Qed.

  Lemma hts_main_imports_pointsto b e owner_a adv_f :
    (b + 6)%a = Some e ->
    [[b, e]] ↦ₐ [[lword_of_word <$> hts_main_imports owner_a adv_f]] ⊣⊢
      b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call
      ∗ (b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert
      ∗ (b ^+ 2)%a ↦ₐ WSealed ot_switcher adv_f
      ∗ (b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global)
      ∗ (b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global)
      ∗ (b ^+ 5)%a ↦ₐ allocator_capability Global owner_a
      ∗ region_pointsto (b ^+ 6)%a e [].
  Proof.
    intros Hsize. rewrite /hts_main_imports.
    rewrite (region_pointsto_cons b (b ^+ 1)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 1)%a (b ^+ 2)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 2)%a (b ^+ 3)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 3)%a (b ^+ 4)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 4)%a (b ^+ 5)%a e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (b ^+ 5)%a (b ^+ 6)%a e); [|solve_addr|solve_addr].
    done.
  Qed.
End Heap_Temporal_Safety_Imports.
