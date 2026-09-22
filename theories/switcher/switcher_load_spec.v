From iris.proofmode Require Import proofmode.
From griotte Require Import rules_Load map_simpl register_tactics.
From griotte Require Import rules_Allocator.
From griotte Require Export call_stack.

Section Switcher_Load.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

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
        ∃ actual, ⌜retv = NextIV⌝ ∗ ⌜load_heap raw actual⌝ ∗
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

End Switcher_Load.

Section Switcher_Restore.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{!allocatorG Σ} `{MP : MachineParameters}.

  (** Restore one saved register, borrowing its shadow entry from the allocator
      for this instruction only. Success exposes [load_heap], so subsequent
      loads need not observe the same shadow bit, even for an aliased base. *)
  Lemma switcher_load_stack_restore E pc_p pc_g pc_b pc_e pc_a pc_a'
    dst src wi wd b e a raw :
    ↑Nallocator ⊆ E ->
    is_shadow_address a = false ->
    decodeInstrW wi = Load dst src 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    dst ≠ cnull -> src ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RWL Local b e a ∗ a ↦ₐ raw ∗
        allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV; ⌜load_heap raw actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RWL Local b e a ∗
        a ↦ₐ raw }}}.
  Proof.
    iIntros (HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & #Halloc) HΦ".
    destruct (is_heap_cap raw) eqn:Hheap; cycle 1.
    { iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply ("HΦ" $! raw). iFrame. iPureIntro. by left. }
    destruct raw as [|[t p g base e' a'|]| |]; try discriminate.
    cbn in Hheap.
    iDestruct (allocator_ctx_shadow_access_with base with "Halloc") as "#Haccess".
    { by apply elem_of_heap_addresses. }
    iApply (wp_load_heap_access with "[$Haccess $HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
    iNext. iIntros (bit) "(_ & _ & HPC & Hdst & Hi & Hsrc & Ha)".
    iApply ("HΦ" $! (if bit then clear_tag (WCap t p g base e' a') else WCap t p g base e' a')).
    destruct bit; iFrame; iPureIntro; [right|left]; done.
  Qed.
End Switcher_Restore.
