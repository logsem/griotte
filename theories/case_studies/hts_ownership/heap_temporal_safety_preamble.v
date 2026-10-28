From iris.proofmode Require Import proofmode.
From griotte Require Import logrel memory_region switcher assert region_keys.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety.
From griotte.allocators.ownership Require Export allocator_preamble.

Section Heap_Temporal_Safety_Resources.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Definition hts_buffer (b : Addr) : Word :=
    Cap RW Global b (b ^+ 1) b.

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

  Lemma hts_main_imports_pointsto_pers b e owner_a adv_f :
    (b + 6)%a = Some e ->
    [[b, e]] ↦ₐ□ [[lword_of_word <$> hts_main_imports owner_a adv_f]] ⊣⊢
      b ↦ₐ□ switcher_entry_call
      ∗ (b ^+ 1) ↦ₐ□ assert_entry
      ∗ (b ^+ 2) ↦ₐ□ WSealed ot_switcher adv_f
      ∗ (b ^+ 3) ↦ₐ□ WSealed ot_switcher (allocator_malloc Global)
      ∗ (b ^+ 4) ↦ₐ□ WSealed ot_switcher (allocator_free Global)
      ∗ (b ^+ 5) ↦ₐ□ allocator_capability Global owner_a
      ∗ region_pointsto_pers (b ^+ 6) e [].
  Proof.
    intros Hsize. rewrite /hts_main_imports.
    rewrite (region_pointsto_pers_cons b (b ^+ 1) e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_pers_cons (b ^+ 1) (b ^+ 2) e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_pers_cons (b ^+ 2) (b ^+ 3) e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_pers_cons (b ^+ 3) (b ^+ 4) e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_pers_cons (b ^+ 4) (b ^+ 5) e); [|solve_addr|solve_addr].
    rewrite (region_pointsto_pers_cons (b ^+ 5) (b ^+ 6) e); [|solve_addr|solve_addr].
    done.
  Qed.
End Heap_Temporal_Safety_Imports.
