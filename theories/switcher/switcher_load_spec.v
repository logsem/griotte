From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load map_simpl register_tactics.
From griotte Require Export call_stack.

Section Switcher_Load.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  Definition stack_load_result (raw actual : Word) : Prop :=
    actual = raw ∨ (is_heap_cap raw = true ∧ actual = clear_tag raw).

  Lemma stack_load_result_nonheap raw actual :
    is_heap_cap raw = false -> stack_load_result raw actual -> actual = raw.
  Proof. intros Hheap [-> | [Hheap' ->]]; congruence. Qed.

  Lemma switcher_load_stack E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd b e a raw :
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw }}}
      Instr Executable @ E
    {{{ retv, RET retv; ⌜retv = FailedV⌝ ∨
        ∃ actual, ⌜retv = NextIV⌝ ∗ ⌜stack_load_result raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw }}}.
  Proof.
    iIntros (Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha) Hφ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "Hφ". iRight. iExists raw. iFrame.
      iPureIntro. split; first done. by left. }
    iDestruct (map_of_regs_3 with "HPC Hsrc Hdst") as "[Hmap (%Hpc_src & %Hpc_dst & %Hsrc_dst)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Ha") as "[Hmem %Hpc_a]".
    iApply (wp_load E pc_p pc_g pc_b pc_e pc_a dst src wi with "[$Hmap $Hmem]");
      eauto; simplify_map_eq; eauto.
    { by rewrite !dom_insert; set_solver+. }
    { exists true, RWL, Local, b, e, a. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - case_decide; last done. exists raw. by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 (Hsrc0 & _).
      simpl_map_regs by eauto. simplify_map_eq. done. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 loadv actual Hallow Hlookup Hactual Hinc|].
    2: { iApply "Hφ". by iLeft. }
    destruct Hallow as (Hsrc0 & _). simpl_map_regs by eauto. simplify_map_eq.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    rewrite (insert_insert_ne _ dst PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hsrc & Hdst)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Ha]"; auto.
    iApply "Hφ". iRight. iExists actual. iFrame.
    iPureIntro. split; first done.
    destruct Hactual as [-> | ->]; [by left|right; done].
  Qed.

  (** Precise restoration when the caller supplies the current shadow entries. *)
  Lemma switcher_load_stack_shadow E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd b e a raw ws shadow :
    raw ∈ ws ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        saved_shadow ws shadow }}}
      Instr Executable @ E
    {{{ RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ restore_word shadow raw ∗
        src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        saved_shadow ws shadow }}}.
  Proof.
    iIntros (Hraw Hshadow Hinstr Hvpc Hbounds Hpc' Hdst Hsrc φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hshadow) Hφ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { rewrite restore_word_nonheap //.
      iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "Hφ". iFrame. }
    destruct raw as [|[t p g b' e' a'|]| |]; try discriminate.
    iDestruct (saved_shadow_lookup _ _ _ b' with "Hshadow")
      as (bit Hbit) "[Hs Hclose]"; first exact Hraw.
    { by rewrite /heap_cap_base /is_heap_cap in Hheap |- *; rewrite Hheap. }
    rewrite /restore_word /heap_cap_base /is_heap_cap in Hheap |- *.
    rewrite Hheap Hbit /=.
    destruct bit.
    - iApply (wp_load_success_heap_revoked with "[$HPC $Hi $Hdst $Hsrc $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hs)".
      iDestruct ("Hclose" with "Hs") as "Hshadow".
      iApply "Hφ". iFrame.
    - iApply (wp_load_success_heap with "[$HPC $Hi $Hdst $Hsrc $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hs)".
      iDestruct ("Hclose" with "Hs") as "Hshadow".
      iApply "Hφ". iFrame.
  Qed.
End Switcher_Load.
