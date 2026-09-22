From iris.proofmode Require Import proofmode.
From griotte Require Export allocator.
From griotte Require Import rules_Load rules_Store.

(** Heap loads borrow the shadow entry only for the atomic instruction.
    The caller's evidence is returned after closing the allocator invariant;
    it can therefore be reused when several saved capabilities share a base. *)
Section AllocatorRules.
  Context {Σ : gFunctors} `{!ceriseG Σ} `{!allocatorG Σ} `{MP : MachineParameters}.
  Lemma wp_load_heap_access E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a (t' : bool) p' g' b' e' a' pc_a' dq dq' (saved_heap_allocated_resources : iProp Σ) (P : bool -> Prop) :
    ↑Nallocator ⊆ E ->
    is_shadow_address a = false ->
    is_heap_address b' = true ->
    decodeInstrW w = Load r1 r2 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    readAllowed p = true ∧ withinBounds b e a = true ->
    (pc_a + 1)%a = Some pc_a' ->
    r1 ≠ cnull -> r2 ≠ cnull ->
    {{{ allocator_shadow_access_with b' saved_heap_allocated_resources P ∗ saved_heap_allocated_resources ∗
    ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    ▷ pc_a ↦ₐ{dq} w ∗ ▷ r1 ↦ᵣ w' ∗
    ▷ r2 ↦ᵣ WCap true p g b e a ∗
    ▷ a ↦ₐ{dq'} WCap t' p' g' b' e' a' }}}
    Instr Executable @ E
    {{{ bit, RET NextIV; ⌜P bit⌝ ∗ saved_heap_allocated_resources ∗
    PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    r1 ↦ᵣ (if bit then clear_tag (load_word p (WCap t' p' g' b' e' a'))
            else load_word p (WCap t' p' g' b' e' a')) ∗
    pc_a ↦ₐ{dq} w ∗ r2 ↦ᵣ WCap true p g b e a ∗
    a ↦ₐ{dq'} WCap t' p' g' b' e' a' }}}.
  Proof.
    iIntros (HE Hshadow Hheap Hinstr Hvpc Hread Hpc Hr1 Hr2 Φ)
    "(#Haccess & HR & HPC & Hi & Hr1 & Hr2 & Ha) HΦ".
    iApply (wp_atomic _ _ (E ∖ ↑Nallocator)).
    iMod ("Haccess" $! E HE with "HR") as (bit HP) "[Hs Hclose]".
    iModIntro. destruct bit.
    - iApply (wp_load_success_heap_revoked with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hr1 & Hi & Hr2 & Ha & Hs)".
      iMod ("Hclose" with "[$Hs]") as "HR".
      iModIntro. iApply ("HΦ" $! true). iFrame. done.
    - iApply (wp_load_success_heap with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hr1 & Hi & Hr2 & Ha & Hs)".
      iMod ("Hclose" with "[$Hs]") as "HR".
      iModIntro. iApply ("HΦ" $! false). iFrame. done.
  Qed.

  (** Quarantining a live cell performs the physical shadow store before
       transferring its memory to the allocator. Only then does the client
       receive the reclaim token; opening the invariant alone cannot mint it. *)
  Lemma wp_store_quarantine E pc_p pc_g pc_b pc_e pc_a pc_a' w dst p g b e a heap_a v :
    ↑Nallocator ⊆ E ->
    shadow_to_heap a = Some heap_a ->
    decodeInstrW w = Store dst (inl 1%Z) 0 ->
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    (pc_a + 1)%a = Some pc_a' ->
    writeAllowed p = true ->
    withinBounds b e a = true ->
    dst ≠ cnull ->
    {{{ allocator_ctx ∗ heap_a ↦ₐ v ∗
    ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    ▷ pc_a ↦ₐ w ∗ ▷ dst ↦ᵣ WCap true p g b e a }}}
    Instr Executable @ E
    {{{ RET NextIV;
    PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
    pc_a ↦ₐ w ∗ dst ↦ᵣ WCap true p g b e a ∗ reclaim_token heap_a }}}.
  Proof.
    iIntros (HE Htranslate Hinstr Hvpc Hpc Hwrite Hbounds Hdst Φ)
    "(#Halloc & Ha & HPC & Hi & Hdst) HΦ".
    destruct (shadow_to_heap_bounds a heap_a Htranslate) as [Hshadow Hheap].
    iApply (wp_atomic _ _ (E ∖ ↑Nallocator)).
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup heap_a with "Hbody") as (s) "[Hentry Hput]".
    { by apply elem_of_heap_addresses. }
    iDestruct (allocator_entry_memory_live with "Hentry Ha") as %->.
    iDestruct "Hentry" as "[Hs Htoken]".
    iModIntro.
    iApply (wp_store_success_shadow_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ true false
      with "[$HPC $Hi $Hdst $Hs]"); eauto.
    iNext. iIntros "(HPC & Hi & Hdst & Hs)".
    iMod ("Hclose" with "[Ha Hs Hput]").
    { iNext. iApply ("Hput" $! Quarantined). iFrame. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.
End AllocatorRules.
