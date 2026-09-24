From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte.allocator Require Import allocator_preamble.

(** Loop specifications. Fetch and return use the existing instruction/macro rules.
    Every loop requires a nonempty range because it stores before testing.
    Registers not mentioned in the contracts can be framed. *)
Section AllocatorMacros.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {allocatorg : allocatorG Σ}
    {MP : MachineParameters}
  .

  (** The existing fetch macro proof specialized to an arbitrary WP mask, so
      allocator calls can keep the non-atomic service invariant open. *)
  Lemma allocator_fetch_spec
    (n : Z) (rdst rscratch1 rscratch2 : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry wdst w1 w2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := fetch_instrs n rdst rscratch1 rscratch2 in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_cap wentry = false ->
    rdst ≠ cnull ->
    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->

    ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rdst ↦ᵣ wdst
    ∗ ▷ rscratch1 ↦ᵣ w1
    ∗ ▷ rscratch2 ↦ᵣ w2
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (pc_b ^+ n)%a ↦ₐ wentry
    ∗ ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end
         ∗ rdst ↦ᵣ load_word pc_p wentry
         ∗ rscratch1 ↦ᵣ WInt 0
         ∗ rscratch2 ↦ᵣ WInt 0
         ∗ codefrag pc_a code
         ∗ (pc_b ^+ n)%a ↦ₐ wentry
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end Hvpc Hcont Hpc_n Hdisjoint Hnonheap Hrdst Hr1 Hr2;
      subst code pc_end.
    iIntros "(>HPC & >Hrdst & >Hscratch1 & >Hscratch2 & >Hcode & >Hentry & Hφ)".
    codefrag_facts "Hcode".
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + n)%a = Some (pc_b ^+ n)%a) as Hpc_bn by solve_addr.
    assert (is_shadow_address (pc_b ^+ n)%a = false) as Hshadow.
    { eapply disjoint_from_shadow_not_in; eauto. }
    iGo "Hcode".
    iApply "Hφ"; iFrame.
  Qed.

  Lemma allocator_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wnull : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := encodeInstrsW [Jalr cnull cra] in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ cra ↦ᵣ wret
    ∗ ▷ cnull ↦ᵣ wnull
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (PC ↦ᵣ updatePcPerm wret
         ∗ cra ↦ᵣ wret
         ∗ cnull ↦ᵣ WInt 0
         ∗ codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hpc Hdisjoint; subst code.
    iIntros "(>HPC & >Hcra & >Hcnull & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Jalr cnull cra. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_zero_spec
    (rptr rend rtmp : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (p : Perm) (g : Locality) (b e : Addr) (wtmp : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_zero_instrs rptr rend rtmp in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    writeAllowed p = true ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    NoDup [PC; cnull; rptr; rend; rtmp] ->

    ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rptr ↦ᵣ WCap true p g b e b
    ∗ ▷ rend ↦ᵣ WInt (finz.to_z e)
    ∗ ▷ rtmp ↦ᵣ wtmp
    ∗ ▷ codefrag pc_a code
    ∗ ▷ allocator_range_memory b e
    ∗ ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end
         ∗ rptr ↦ᵣ WCap true p g b e e
         ∗ rend ↦ᵣ WInt (finz.to_z e)
         ∗ rtmp ↦ᵣ WInt 0
         ∗ codefrag pc_a code
         ∗ ([∗ list] a ∈ finz.seq_between b e, a ↦ₐ WInt 0)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow Hwrite Hheap Hregs)
      "(>HPC & >Hptr & >Hend & >Htmp & >Hcode & >Hmem & Hφ)".
    assert (Hrptr : rptr ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrend : rend ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrtmp : rtmp ≠ cnull) by (repeat rewrite NoDup_cons in Hregs; set_solver).

    (* Keep the capability's base fixed while the loop cursor advances. *)
    pose (cap_b := b).
    assert (Hcap_b : (heap_b <= cap_b)%a) by (unfold cap_b; solve_addr).
    assert (Hba : (cap_b <= b)%a) by (unfold cap_b; solve_addr).
    assert (Hbase : b = cap_b) by done.
    iEval (rewrite {1}Hbase) in "Hptr".
    iEval (rewrite {1}Hbase) in "Hφ".
    clear Hbase; clearbody cap_b.
    iLöb as "IH" forall (b wtmp Hheap Hba).
    codefrag_facts "Hcode".
    iEval (rewrite /allocator_range_memory
      (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons) in "Hmem".
    iDestruct "Hmem" as "[[%w Ha] Hmem]".

    (* Store rptr 0 writes zero to the current heap cell. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_success_z with "[$HPC $Hi $Hptr $Ha]"); try solve_pure.
    { eapply disjoint_from_shadow_not_in; first exact heap_shadow_disjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }
    iIntros "!> (HPC & Hi & Hptr & Ha)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").

    (* Lea rptr 1 advances the heap cursor. *)
    iInstr "Hcode".
    (* GetA rtmp rptr reads the advanced cursor. *)
    iInstr "Hcode".
    (* Sub rtmp rend rtmp computes the remaining length. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - rewrite Hlast Z.sub_diag.
      (* Jnz .allocator_zero rtmp falls through after the last cell. *)
      iInstr "Hcode".
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
        Hlast finz_seq_between_empty; last solve_addr.
      rewrite big_sepL_cons big_sepL_nil. iFrame.
    - (* Jnz .allocator_zero rtmp repeats the loop. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Htmp]"); try solve_pure.
      { intros Hzero; inversion Hzero; solve_addr. }
      { instantiate (1 := pc_a). solve_addr. }
      iIntros "!> (HPC & Hi & Htmp)".
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      iApply ("IH" $! (b ^+ 1)%a with
        "[] [] HPC Hptr Hend Htmp Hcode Hmem [Ha Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hend & Htmp & Hcode & Hzero)".
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
      iFrame.
  Qed.

  (** Clear painting preserves the exact words supplied by the caller.
      Quarantine painting gives up those words and returns one reclaim token
      per cell. In either case, memory ownership witnesses that the entire
      input range is live; repeated runtime frees are outside this contract.

      The translation and length premises identify the shadow interval, including
      the one-past-end pointer reached by the final LEA but never dereferenced.
      The service layout supplies them when composing the allocator operations. *)
  Lemma allocator_paint_spec
    (status : AllocStatus) (rptr rcount : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (b e sb se : Addr) (ws : list Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_paint_instrs rptr rcount status in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    ↑Nallocator ⊆ E ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a ->
    (finz.to_z se - finz.to_z sb = finz.to_z e - finz.to_z b)%Z ->
    (∀ a, (b <= a /\ a < e)%a ->
       heap_to_shadow a = Some (sb ^+ (finz.to_z a - finz.to_z b))%a) ->
    NoDup [PC; cnull; rptr; rcount] ->

    allocator_ctx
    ∗ ▷ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a
    ∗ ▷ rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb
    ∗ ▷ rcount ↦ᵣ WInt (finz.to_z e - finz.to_z b)
    ∗ ▷ codefrag pc_a code
    ∗ ▷ ([[b, e]] ↦ₐ [[ws]])
    ∗ ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end
         ∗ rptr ↦ᵣ WCap true RW Global shadow_b shadow_e se
         ∗ rcount ↦ᵣ WInt 0
         ∗ codefrag pc_a code
         ∗ (match status with
            | ShadowQuarantined => [∗ list] a ∈ finz.seq_between b e, reclaim_token a
            | ShadowLive => [[b, e]] ↦ₐ [[ws]]
            end)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow HE Hheap Hshadow Hlen Htranslate Hregs)
      "(#Halloc & >HPC & >Hptr & >Hcount & >Hcode & >Hmem & Hφ)".
    assert (Hrptr : rptr ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrcount : rcount ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    iLöb as "IH" forall (b sb ws Hheap Hshadow Hlen Htranslate).
    assert (Hcode_eq : allocator_paint_instrs rptr rcount status =
      encodeInstrsW [Store rptr (inl (encodeAllocStatus status)) 0;
                    Lea rptr (inl 1%Z);
                    Sub rcount (inr rcount) (inl 1%Z);
                    Jnz (inl (-3)%Z) rcount]) by (destruct status; reflexivity).
    rewrite Hcode_eq in Hpc |- *.
    codefrag_facts "Hcode".
    iDestruct (big_sepL2_length with "Hmem") as %Hws.
    rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) in Hws.
    clear Hcode_eq.
    destruct ws as [|w ws]; first discriminate Hws.
    assert (Hbnext : (b + 1)%a = Some (b ^+ 1)%a) by solve_addr.
    assert (Hbnext_e : (b ^+ 1 <= e)%a) by solve_addr.
    iEval (rewrite (region_pointsto_cons b (b ^+ 1)%a e w ws Hbnext Hbnext_e))
      in "Hmem".
    iDestruct "Hmem" as "[Ha Hmem]".
    assert (Hmap : heap_to_shadow b = Some sb).
    { specialize (Htranslate b).
      replace (sb ^+ (b - b))%a with sb in Htranslate by solve_addr.
      apply Htranslate; solve_addr. }

    (* Store rptr status writes the shadow entry, opening the shared invariant. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iAssert (WP Instr Executable @ E {{ v,
      ⌜v = NextIV⌝ ∗
      PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a ∗
      pc_a ↦ₐ encodeInstrW (Store rptr (inl (encodeAllocStatus status)) 0) ∗
      rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
      (match status with ShadowQuarantined => reclaim_token b | ShadowLive => b ↦ₐ w end) }})%I
      with "[HPC Hi Hptr Ha]" as "Hstore".
    { iApply (wp_atomic _ _ (E ∖ ↑Nallocator)).
      iInv Nallocator as ">Hbody" "Hclose".
      iDestruct (allocator_inv_lookup b with "Hbody") as (s) "[Hentry Hput]".
      { apply elem_of_heap_addresses, withinBounds_true_iff; solve_addr. }
      iDestruct (allocator_entry_memory_live with "Hentry Ha") as %->.
      iDestruct "Hentry" as "[Hs [Hreclaim Hfree]]".
      iModIntro.
      iApply (wp_store_success_shadow_z _ _ _ _ _ _ _ _ _ _ _ _ _ _ status ShadowLive
        with "[$HPC $Hi $Hptr $Hs]"); try solve_pure.
      { unfold is_shadow_address. apply withinBounds_true_iff; solve_addr. }
      { by apply heap_shadow_inverse. }
      { apply withinBounds_true_iff; solve_addr. }
      iIntros "!> (HPC & Hi & Hptr & Hs)".
      destruct status.
      - iMod ("Hclose" with "[Hs Hput Hfree Hreclaim]").
        { iNext. iApply ("Hput" $! Live). iFrame. }
        iModIntro; iFrame; done.
      - iMod ("Hclose" with "[Ha Hs Hput Hfree]").
        { iNext. iApply ("Hput" $! Quarantined). iFrame. }
        iModIntro; iFrame; done.
    }
    iApply (wp_wand with "Hstore").
    iIntros (v) "(-> & HPC & Hi & Hptr & Ha)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").

    (* Lea rptr 1 advances the shadow cursor. *)
    iInstr "Hcode".
    (* Sub rcount rcount 1 consumes one word of the count. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - replace (e - b - 1)%Z with 0%Z by solve_addr.
      (* Jnz .allocator_paint rcount falls through after the last cell. *)
      iInstr "Hcode".
      assert (Hslast : (sb ^+ 1)%a = se) by solve_addr.
      rewrite Hslast.
      iApply "Hφ"; iFrame.
      destruct status.
      + rewrite (region_pointsto_cons b (b ^+ 1)%a e w ws Hbnext Hbnext_e).
        iFrame.
      + rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
          Hlast finz_seq_between_empty; last solve_addr.
        rewrite big_sepL_cons big_sepL_nil. iFrame.
    - (* Jnz .allocator_paint rcount repeats the loop. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hcount]"); try solve_pure.
      { intros Hzero; inversion Hzero; solve_addr. }
      { instantiate (1 := pc_a). solve_addr. }
      iIntros "!> (HPC & Hi & Hcount)".
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      replace (e - b - 1)%Z with (e - (b ^+ 1)%a)%Z by solve_addr.
      iApply ("IH" $! (b ^+ 1)%a (sb ^+ 1)%a ws with
        "[] [] [] [] HPC Hptr Hcount Hcode Hmem [Ha Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro. intros a Ha_bounds.
        rewrite (Htranslate a); last solve_addr.
        f_equal. clear -Hheap Hshadow Hlen Hbnext Ha_bounds. solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hcount & Hcode & Hpainted)".
      iApply "Hφ"; iFrame.
      destruct status.
      + rewrite (region_pointsto_cons b (b ^+ 1)%a e w ws Hbnext Hbnext_e).
        iFrame.
      + rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
        iFrame.
  Qed.
  (** Translate a heap interval to its shadow interval. The instruction list
      is shared by malloc block 4 and free block 3. *)
  Lemma allocator_translate_spec
    (E : coPset)
    (pc_b pc_e pc_a next b e : Addr) (w3 wa2 : Word)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 4 in
    let sb := (shadow_b ^+ (b - heap_b))%a in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->

    ▷ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ▷ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
    ∗ ▷ ct1 ↦ᵣ WInt b
    ∗ ▷ ct2 ↦ᵣ WInt e
    ∗ ▷ ct3 ↦ᵣ w3
    ∗ ▷ ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b
    ∗ ▷ ca2 ↦ᵣ wa2
    ∗ ▷ codefrag pc_a code
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length code)%a
         ∗ ct0 ↦ᵣ WCap true RW Global heap_b heap_e next
         ∗ ct1 ↦ᵣ WInt b
         ∗ ct2 ↦ᵣ WInt e
         ∗ ct3 ↦ᵣ WInt (b - heap_b)
         ∗ ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb
         ∗ ca2 ↦ᵣ WInt (e - b)
         ∗ codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code sb Hpc Hdisjoint Hheap; subst code sb.
    iIntros "(>HPC & >Hct0 & >Hct1 & >Hct2 & >Hct3 & >Hctp & >Hca2 & >Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    pose proof heap_shadow_same_size as Hsize.
    assert (Hsb : (shadow_b <= (shadow_b ^+ (b - heap_b))%a /\
                   (shadow_b ^+ (b - heap_b))%a < shadow_e)%a) by solve_addr.
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
  Qed.
End AllocatorMacros.
