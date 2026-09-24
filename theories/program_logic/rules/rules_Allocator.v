From iris.proofmode Require Import proofmode.
From griotte.program_logic Require Export allocator_resources.
From griotte Require Import rules_Load rules_Store.

Section AllocatorRules.
  Context {Σ : gFunctors} `{!ceriseG Σ} `{!allocatorG Σ} `{MP : MachineParameters}.

  (** A heap load consults the allocator invariant for this instruction only.
      The observed shadow status determines whether the loaded tag is cleared. *)
  Lemma wp_load_heap_inv E r1 r2 pc_p pc_g pc_b pc_e pc_a w w'
    p g b e a raw base pc_a' dq dq' :
    ↑Nallocator ⊆ E →
    is_shadow_address a = false →
    heap_cap_base raw = Some base →
    decodeInstrW w = Load r1 r2 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    readAllowed p = true ∧ withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    r1 ≠ cnull →
    r2 ≠ cnull →
    {{{ allocator_ctx
        ∗ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ r1 ↦ᵣ w'
        ∗ ▷ r2 ↦ᵣ WCap true p g b e a
        ∗ ▷ a ↦ₐ{dq'} raw }}}
      Instr Executable @ E
    {{{ (status : AllocStatus), RET NextIV;
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a'
        ∗ r1 ↦ᵣ (match status with
                  | ShadowLive => load_word p raw
                  | ShadowQuarantined => clear_tag (load_word p raw)
                  end)
        ∗ pc_a ↦ₐ{dq} w
        ∗ r2 ↦ᵣ WCap true p g b e a
        ∗ a ↦ₐ{dq'} raw }}}.
  Proof.
    iIntros (HE Hshadow Hheap Hinstr Hvpc Hread Hpc Hr1 Hr2 Φ)
      "(#Halloc & HPC & Hi & Hr1 & Hr2 & Ha) HΦ".
    (* Load r1 r2: open the shadow entry for the loaded capability's base. *)
    iInv Nallocator as ">Hbody" "Hclose".
    iDestruct (allocator_inv_lookup base with "Hbody") as (s) "[[Hs Hres] Hput]".
    { apply elem_of_heap_addresses.
      unfold heap_cap_base in Hheap.
      destruct (memory_cap_base raw) as [b'|]; last discriminate.
      destruct (is_heap_address b') eqn:Hb'; inversion Hheap; subst; done. }
    destruct (shadow_status s) eqn:Hstatus.
    - iApply (wp_load_success_heap_word with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hr1 & Hi & Hr2 & Ha & Hs)".
      iMod ("Hclose" with "[Hs Hres Hput]").
      { iNext. iApply ("Hput" $! s). iFrame "Hres". by rewrite /allocator_entry Hstatus. }
      iModIntro. iApply ("HΦ" $! ShadowLive). iFrame.
    - iApply (wp_load_success_heap_word_revoked with "[$HPC $Hi $Hr1 $Hr2 $Ha $Hs]"); eauto.
      iNext. iIntros "(HPC & Hr1 & Hi & Hr2 & Ha & Hs)".
      iMod ("Hclose" with "[Hs Hres Hput]").
      { iNext. iApply ("Hput" $! s). iFrame "Hres". by rewrite /allocator_entry Hstatus. }
      iModIntro. iApply ("HΦ" $! ShadowQuarantined). iFrame.
  Qed.

  (** Quarantining a live cell performs the physical shadow store before
       transferring its memory to the allocator. Only then does the client
       receive the reclaim token; opening the invariant alone cannot mint it. *)
  Lemma wp_store_quarantine E pc_p pc_g pc_b pc_e pc_a pc_a' w dst p g b e a heap_a v :
    ↑Nallocator ⊆ E ->
    shadow_to_heap a = Some heap_a ->
    decodeInstrW w = Store dst (inl (encodeAllocStatus ShadowQuarantined)) 0 ->
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
    iDestruct "Hentry" as "[Hs [Htoken Hfree]]".
    iModIntro.
    iApply (wp_store_success_shadow_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ ShadowQuarantined ShadowLive
      with "[$HPC $Hi $Hdst $Hs]"); eauto.
    iNext. iIntros "(HPC & Hi & Hdst & Hs)".
    iMod ("Hclose" with "[Ha Hs Hput Hfree]").
    { iNext. iApply ("Hput" $! Quarantined). iFrame. }
    iModIntro. iApply "HΦ". iFrame.
  Qed.
End AllocatorRules.
