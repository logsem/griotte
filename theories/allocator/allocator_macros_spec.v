From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region fetch.
From griotte.allocator Require Import allocator_preamble.

(** Loop specifications. Fetch and return use the existing instruction/macro rules.
    Every loop requires a nonempty range because it stores before testing.
    Registers not mentioned in the contracts can be framed. *)

(** A tagged, nonempty capability based in the heap has authority. *)
Lemma heap_authority_base_heap_cap `{MP : MachineParameters} p g b e a :
  (heap_b <= b)%a -> (b < e)%a -> (b < heap_e)%a ->
  heap_authority_base (WCap true p g b e a) = Some b.
Proof.
  intros Hb Hbe He.
  rewrite /heap_authority_base decide_True // /heap_cap_base /=.
  assert (is_heap_address b = true) as -> by (apply withinBounds_true_iff; solve_addr).
  done.
Qed.

Lemma has_authority_heap_cap `{MP : MachineParameters} p g b e a :
  (heap_b <= b)%a -> (b < e)%a -> (b < heap_e)%a ->
  has_authority (WCap true p g b e a).
Proof.
  intros Hb Hbe He. split; first done. exists b.
  by apply heap_authority_base_heap_cap.
Qed.

Section AllocatorMacros.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {MP : MachineParameters}
  .

  (** The existing fetch macro proof specialized to an arbitrary WP mask, so
      allocator calls can keep the non-atomic service invariant open. *)

  Lemma allocator_fetch_spec
    (n : Z) (rdst rscratch1 rscratch2 : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (wentry wdst w1 w2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := fetch_instrs n rdst rscratch1 rscratch2 in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    withinBounds pc_b pc_e (pc_b ^+ n)%a = true ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_cap wentry.(lw) = false ->
    rdst ≠ cnull ->
    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->

    PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rdst ↦ᵣ wdst ∗
    rscratch1 ↦ᵣ w1 ∗
    rscratch2 ↦ᵣ w2 ∗
    (pc_b ^+ n)%a ↦ₐ wentry ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rdst ↦ᵣ lload_word pc_p wentry ∗
         rscratch1 ↦ᵣ WInt 0 ∗
         rscratch2 ↦ᵣ WInt 0 ∗
         (pc_b ^+ n)%a ↦ₐ wentry ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end Hvpc Hcont Hpc_n Hdisjoint Hnonheap Hrdst Hr1 Hr2;
      subst code pc_end.
    iIntros "(HPC & Hrdst & Hscratch1 & Hscratch2 & Hentry & Hcode & Hφ)".
    codefrag_facts "Hcode".
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + n)%a = Some (pc_b ^+ n)%a) as Hpc_bn by solve_addr.
    assert (is_shadow_address (pc_b ^+ n)%a = false) as Hshadow.
    { eapply disjoint_from_shadow_not_in; eauto. }
    iGo "Hcode".
    iApply "Hφ"; iFrame.
  Qed.

  Lemma allocator_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wnull : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := encodeInstrsW [Jalr cnull cra] in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cra ↦ᵣ wret ∗
    cnull ↦ᵣ wnull ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ lupdatePcPerm wret ∗
         cra ↦ᵣ wret ∗
         cnull ↦ᵣ WInt 0 ∗
         codefrag pc_a code ∗
         £ 1
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hpc Hdisjoint; subst code.
    iIntros "(HPC & Hcra & Hcnull & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Jalr cnull cra. *)
    iInstr "Hcode" with "Hlc".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_zero_spec
    (rptr rend rtmp : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (p : Perm) (g : Locality) (b e : Addr) (π : option AId) (wtmp : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_zero_instrs rptr rend rtmp in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    writeAllowed p = true ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    NoDup [PC; cnull; rptr; rend; rtmp] ->

    PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rptr ↦ᵣ WCap true p g b e b @@? π ∗
    rend ↦ᵣ WInt (finz.to_z e) ∗
    rtmp ↦ᵣ wtmp ∗
    allocator_range_memory b e ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rptr ↦ᵣ WCap true p g b e e @@? π ∗
         rend ↦ᵣ WInt (finz.to_z e) ∗
         rtmp ↦ᵣ WInt 0 ∗
         ([∗ list] a ∈ finz.seq_between b e, a ↦ₐ WInt 0) ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow Hwrite Hheap Hregs)
      "(HPC & Hptr & Hend & Htmp & Hmem & Hcode & Hφ)".
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

    (* Store rptr 0. *)
    iInstr_success "Hcode".
    { eapply disjoint_from_shadow_not_in; first exact heap_shadow_disjoint.
      apply withinBounds_true_iff; solve_addr. }
    { apply withinBounds_true_iff; solve_addr. }

    (* Lea rptr 1 advances the heap cursor. *)
    iInstr "Hcode".
    (* GetA rtmp rptr reads the advanced cursor. *)
    iInstr "Hcode".
    (* Sub rtmp rend rtmp computes the remaining length. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - rewrite Hlast Z.sub_diag.
      (* Jnz .allocator_zero rtmp falls through after the last address. *)
      iInstr "Hcode".
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
        Hlast finz_seq_between_empty; last solve_addr.
      rewrite big_sepL_cons big_sepL_nil. iFrame.
    - (* Jnz .allocator_zero rtmp repeats the loop. *) iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Htmp]"); try solve_pure.
      { intros Hzero; inversion Hzero; solve_addr. }
      { instantiate (1 := pc_a). solve_addr. }
      iIntros "!> (HPC & Hi & Htmp)".
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      iApply ("IH" $! (b ^+ 1)%a with
        "[] [] HPC Hptr Hend Htmp Hmem Hcode [Ha Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hend & Htmp & Hzero & Hcode)".
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
      iFrame.
  Qed.

  (** The shadow stores of the paint loop are justified either because they
      store the entry's current value, or by a shared resource [R] together
      with a per-cell resource [P a] (§4.5). *)
  Definition allocator_paint_ok (R : iProp Σ) (P : Addr → iProp Σ) (b e : Addr) : Prop :=
    ∀ a Rs Cs, (b <= a < e)%a →
      reg_auth Rs -∗ addr_alloc_auth Cs -∗ R ∗ P a -∗ ⌜shadow_perm_ok Rs Cs a⌝.

  (** The paint loop stores [s_new] into the shadow entries of a nonempty
      range, touching no memory. The shared resource [R] and the per-cell
      resources [P a] are returned unchanged. Its three instances: the
      same-value store of [malloc] ([↦ₛ L], any claim), the paint of [free]
      ([↦ₛ L], [Claimed ι], with [R := ι ↦st{1} APainting]), and its unpaint
      ([↦ₛ Q], [Unclaimed]).

      The translation and length premises identify the shadow interval, including
      the one-past-end pointer reached by the final LEA but never dereferenced.
      The service layout supplies them when composing the allocator operations. *)

  Lemma allocator_paint_spec
    (s_old s_new : AllocStatus) (rptr rcount : RegName) (E : coPset)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (b e sb se : Addr) (R : iProp Σ) (P : Addr → iProp Σ)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_paint_instrs rptr rcount s_new in
    let pc_end := (pc_a ^+ length code)%a in
    executeAllowed pc_p = true ->
    SubBounds pc_b pc_e pc_a pc_end ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->
    (shadow_b <= sb /\ sb < se /\ se <= shadow_e)%a ->
    (finz.to_z se - finz.to_z sb = finz.to_z e - finz.to_z b)%Z ->
    (∀ a, (b <= a /\ a < e)%a ->
       heap_to_shadow a = Some (sb ^+ (finz.to_z a - finz.to_z b))%a) ->
    NoDup [PC; cnull; rptr; rcount] ->
    s_old = s_new ∨ allocator_paint_ok R P b e ->

    PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
    rcount ↦ᵣ WInt (finz.to_z e - finz.to_z b) ∗
    R ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ s_old ∗ P a) ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_end ∗
         rptr ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
         rcount ↦ᵣ WInt 0 ∗
         R ∗
         ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ s_new ∗ P a) ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code pc_end; subst code pc_end.
    iIntros (Hexec Hpc Hpc_shadow Hheap Hshadow Hlen Htranslate Hregs Hok)
      "(HPC & Hptr & Hcount & HR & Hcells & Hcode & Hφ)".
    assert (Hrptr : rptr ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    assert (Hrcount : rcount ≠ cnull) by
      (clear -Hregs; repeat rewrite NoDup_cons in Hregs; set_solver).
    iLöb as "IH" forall (b sb Hheap Hshadow Hlen Htranslate Hok).
    assert (Hcode_eq : allocator_paint_instrs rptr rcount s_new =
      encodeInstrsW [Store rptr (inl (encodeAllocStatus s_new)) 0;
                    Lea rptr (inl 1%Z);
                    Sub rcount (inr rcount) (inl 1%Z);
                    Jnz (inl (-3)%Z) rcount]) by (destruct s_new; reflexivity).
    rewrite Hcode_eq in Hpc |- *.
    codefrag_facts "Hcode".
    clear Hcode_eq.
    assert (Hbnext : (b + 1)%a = Some (b ^+ 1)%a) by solve_addr.
    assert (Hbnext_e : (b ^+ 1 <= e)%a) by solve_addr.
    iEval (rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons)
      in "Hcells".
    iDestruct "Hcells" as "[[Hs HP] Hcells]".
    assert (Hmap : heap_to_shadow b = Some sb).
    { specialize (Htranslate b).
      replace (sb ^+ (b - b))%a with sb in Htranslate by solve_addr.
      apply Htranslate; solve_addr. }
    unfold lword_of_word.

    (* Store rptr (encodeAllocStatus s_new). *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iAssert (WP Instr Executable @ E {{ v,
      ⌜v = NextIV⌝ ∗
      PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a ∗
      pc_a ↦ₐ encodeInstrW (Store rptr (inl (encodeAllocStatus s_new)) 0) ∗
      rptr ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
      b ↦ₛ s_new ∗ R ∗ P b }})%I
      with "[HPC Hi Hptr Hs HR HP]" as "Hstore".
    { destruct Hok as [<- | Hok].
      - iApply (wp_store_success_shadow_z_same with "[$HPC $Hi $Hptr $Hs]"); try solve_pure.
        { unfold is_shadow_address. apply withinBounds_true_iff; solve_addr. }
        { by apply heap_shadow_inverse. }
        { apply withinBounds_true_iff; solve_addr. }
        iIntros "!> (HPC & Hi & Hptr & Hs)". iFrame. done.
      - iApply (wp_store_success_shadow_z_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s_new s_old b
          (R ∗ P b) with "[$HPC $Hi $Hptr $Hs $HR $HP]"); try solve_pure.
        { intros Rs Cs. iIntros "HRs HCs HRP".
          iApply (Hok b with "HRs HCs HRP"). solve_addr. }
        { unfold is_shadow_address. apply withinBounds_true_iff; solve_addr. }
        { by apply heap_shadow_inverse. }
        { apply withinBounds_true_iff; solve_addr. }
        iIntros "!> (HPC & Hi & Hptr & Hs & HR & HP)". iFrame. done. }
    iApply (wp_wand with "Hstore").
    iIntros (v) "(-> & HPC & Hi & Hptr & Hs & HR & HP)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").

    (* Lea rptr 1 advances the shadow cursor. *)
    iInstr "Hcode".
    (* Sub rcount rcount 1 consumes one word of the count. *)
    iInstr "Hcode".
    destruct (decide ((b ^+ 1)%a = e)) as [Hlast | Hmore].
    - replace (e - b - 1)%Z with 0%Z by solve_addr.
      (* Jnz .allocator_paint rcount falls through after the last address. *)
      iInstr "Hcode".
      assert (Hslast : (sb ^+ 1)%a = se) by solve_addr.
      rewrite Hslast.
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap)))
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
      iApply ("IH" $! (b ^+ 1)%a (sb ^+ 1)%a with
        "[] [] [] [] [] HPC Hptr Hcount HR Hcells Hcode [Hs HP Hφ]").
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro; solve_addr. }
      { iPureIntro. intros a Ha_bounds.
        rewrite (Htranslate a); last solve_addr.
        f_equal. clear -Hheap Hshadow Hlen Hbnext Ha_bounds. solve_addr. }
      { iPureIntro. destruct Hok as [-> | Hok]; [by left|right].
        intros a Rs Cs Ha. apply Hok. solve_addr. }
      iNext. iIntros "(HPC & Hptr & Hcount & HR & Hpainted & Hcode)".
      iApply "Hφ"; iFrame.
      rewrite (finz_seq_between_cons b e (proj1 (proj2 Hheap))) big_sepL_cons.
      iFrame.
  Qed.

  (** Translate the header of a new allocation to its shadow interval, and
      load the count of header words (malloc body block 4). *)

  Lemma allocator_translate_spec
    (E : coPset)
    (pc_b pc_e pc_a next h b : Addr) (w3 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_body_instrs_n 4 in
    let sh := (shadow_b ^+ (h - heap_b))%a in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b <= h /\ h < heap_e)%a ->
    (h + allocator_header_words)%a = Some b ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct3 ↦ᵣ w3 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length code)%a ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         ct3 ↦ᵣ WInt (h - heap_b) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sh ∗
         ca2 ↦ᵣ WInt allocator_header_words ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code sh Hpc Hdisjoint Hheap Hb; subst code sh.
    unfold allocator_header_words in *.
    iIntros "(HPC & Hct0 & Hct1 & Hct3 & Hctp & Hca2 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    pose proof heap_shadow_same_size as Hsize.
    assert (Hsh : (shadow_b <= (shadow_b ^+ (h - heap_b))%a /\
                   (shadow_b ^+ (h - heap_b))%a < shadow_e)%a) by solve_addr.
    replace (b - heap_b - 3)%Z with (h - heap_b)%Z by solve_addr.
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Mov ca2 allocator_header_words. *)
    iInstr "Hcode".
    iApply "Hφ". iFrame.
  Qed.

End AllocatorMacros.

Section AllocatorOwnerMacro.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}
  .

  Definition allocator_unsealing_key : Word :=
    WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype.

  (** The allocator's three imports, as separate words. *)
  Lemma allocator_imports_split :
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ⊣⊢
    (allocator_pcc_b ^+ allocator_shadow_import_off)%a ↦ₐ
      WCap true RW Global shadow_b shadow_e shadow_b ∗
    (allocator_pcc_b ^+ 1)%a ↦ₐ
      WSealRange true (false, true) Global AllocOtype (AllocOtype ^+ 1)%ot AllocOtype ∗
    (allocator_pcc_b ^+ allocator_revoker_import_off)%a ↦ₐ allocator_revoker_cap.
  Proof.
    pose proof allocator_size_imports as Hsize.
    rewrite allocator_imports_length in Hsize.
    rewrite /allocator_imports !fmap_cons fmap_nil.
    rewrite (region_pointsto_cons allocator_pcc_b (allocator_pcc_b ^+ 1)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 1)%a (allocator_pcc_b ^+ 2)%a);
      [|solve_addr|solve_addr].
    rewrite (region_pointsto_cons (allocator_pcc_b ^+ 2)%a allocator_code_b);
      [|solve_addr|solve_addr].
    rewrite /region_pointsto finz_seq_between_empty; last solve_addr.
    rewrite /allocator_shadow_import_off /allocator_revoker_import_off.
    assert ((allocator_pcc_b ^+ 0)%a = allocator_pcc_b) as -> by solve_addr.
    iSplit; [iIntros "($ & $ & $ & _)" | iIntros "($ & $ & $)"]; done.
  Qed.

  (** Load the owner identifier of an allocator capability. The physical owner
      word is only read. Block 0 of both allocator entries is this macro. *)

  Lemma allocator_owner_spec
    (E : coPset) (pc_b pc_e pc_a : Addr)
    (g : Locality) (a : Addr) (o : Z) (wtp w3 w4 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_owner_instrs ctp ca0 ct3 ct4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off)%a = true ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
    a ↦ₐ WInt o ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length code)%a ∗
         ctp ↦ᵣ WInt o ∗
         ct3 ↦ᵣ WInt 0 ∗
         ct4 ↦ᵣ WInt 0 ∗
         ca0 ↦ᵣ allocator_capability g a ∗
         (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
         a ↦ₐ WInt o ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code; subst code.
    iIntros (Hpc Hdisjoint Hkey Hshadow_a Ha)
      "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Ha & Hcode & Hφ)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + allocator_unsealing_key_import_off)%a =
      Some (pc_b ^+ allocator_unsealing_key_import_off)%a) as Hpc_bn
      by (apply withinBounds_true_iff in Hkey; solve_addr).
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off)%a = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key /allocator_capability /allocator_capability_scap.
    (* Mov ctp PC. *)
    iInstr "Hcode".
    (* GetB ct3 ctp. *)
    iInstr "Hcode".
    (* GetA ct4 ctp. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct4. *)
    iInstr "Hcode".
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Lea ctp allocator_unsealing_key_import_off. *)
    iInstr "Hcode".
    (* Load ctp ctp. *)
    iInstr "Hcode".
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    (* Mov ct3 0. *)
    iInstr "Hcode".
    (* Mov ct4 0. *)
    iInstr "Hcode".
    (* UnSeal ctp ctp ca0. *)
    iInstr "Hcode".
    (* Load ctp ctp. *)
    iInstr "Hcode".
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    iApply "Hφ". iFrame.
  Qed.

  (** A malformed allocator capability traps: either [unseal] fails, or it
      clears the tag of the result and the following [load] fails. *)

  Lemma allocator_owner_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wsealed wtp w3 w4 : LWord)
    (P : iProp Σ) :

    let code := allocator_owner_instrs ctp ca0 ct3 ct4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    withinBounds pc_b pc_e (pc_b ^+ allocator_unsealing_key_import_off)%a = true ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ wsealed ∗
    (pc_b ^+ allocator_unsealing_key_import_off)%a ↦ₐ allocator_unsealing_key ∗
    codefrag pc_a code
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros code; subst code.
    iIntros (Hpc Hdisjoint Hkey Hwsealed)
      "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Hcode)".
    codefrag_facts "Hcode".
    pose proof allocator_otype_size as Hotype.
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea by solve_addr.
    assert ((pc_b + allocator_unsealing_key_import_off)%a =
      Some (pc_b ^+ allocator_unsealing_key_import_off)%a) as Hpc_bn
      by (apply withinBounds_true_iff in Hkey; solve_addr).
    assert (is_shadow_address (pc_b ^+ allocator_unsealing_key_import_off)%a = false)
      as Hshadow_key by (eapply disjoint_from_shadow_not_in; eauto).
    rewrite /allocator_unsealing_key.
    (* Mov ctp PC. *)
    iInstr "Hcode".
    (* GetB ct3 ctp. *)
    iInstr "Hcode".
    (* GetA ct4 ctp. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 ct4. *)
    iInstr "Hcode".
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    (* Lea ctp allocator_unsealing_key_import_off. *)
    iInstr "Hcode".
    (* Load ctp ctp. *)
    iInstr "Hcode".
    iEval (rewrite /lload_word /lift_word /=) in "Hctp".
    (* Mov ct3 0. *)
    iInstr "Hcode".
    (* Mov ct4 0. *)
    iInstr "Hcode".
    (* UnSeal ctp ctp ca0. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (map_of_regs_3 with "HPC Hctp Hca0") as "[Hmap %Hne]".
    destruct Hne as (HPCctp & HPCca0 & Hctpca0).
    iApply (wp_UnSeal _ RX Global pc_b pc_e (pc_a ^+ 9)%a None _ ctp ctp ca0
      with "[$Hi $Hmap]").
    { by rewrite decode_encode_instrW_inv. }
    { solve_pure. }
    { by rewrite lookup_insert_eq. }
    { rewrite /regs_of !dom_insert_L. set_solver+. }
    iNext. iIntros (regs' retv) "(%Hspec & Hi & Hmap)".
    inversion Hspec as
      [ p g b e a πs o sb π Hsrc1 Hsrc2 Htag Hperm Hwb HincrPC
      | t p g b e a πs o sb π Hsrc1 Hsrc2 Hfalse HincrPC
      | Hfail ]; subst.
    - (* A well-formed allocator capability: excluded. *)
      exfalso. simplify_map_eq.
      apply withinBounds_le_addr in Hwb.
      destruct Hwsealed as [Hne|Hne]; [apply Z.eqb_neq in Hne; solve_addr|congruence].
    - (* The unsealed word is untagged, and the load traps. *)
      simplify_map_eq.
      apply incrementPC_Some_inv in HincrPC as (?&?&?&?&?&?&a10&?&HPC'&Ha10&->).
      simplify_map_eq.
      iEval (rewrite (insert_insert_ne _ ctp PC) // !insert_insert_eq) in "Hmap".
      iEval (rewrite !insert_insert_eq) in "Hmap".
      iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hctp & Hca0)"; [done..|].
      assert (a10 = (pc_a ^+ 10)%a) as -> by solve_addr.
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      (* Load ctp ctp. *)
      iInstr "Hcode".
      wp_end; iIntros "%Hcontr"; done.
    - wp_pure; wp_end; iIntros "%Hcontr"; done.
  Qed.

  (** The owner block at an allocator entry point [pc_a], followed by the
      rest of the entry, with a malformed allocator capability: it traps. *)

  Lemma allocator_owner_entry_invalid_spec
    (E : coPset) (pc_a : Addr) (rest : list Word) (wsealed wtp w3 w4 : LWord)
    (P : iProp Σ) :

    let owner := allocator_owner_instrs ctp ca0 ct3 ct4 in
    SubBounds allocator_pcc_b allocator_pcc_e pc_a (pc_a ^+ length (owner ++ rest))%a ->
    (is_sealed_with_o wsealed.(lw) AllocOtype = false \/ get_tag wsealed.(lw) = false) ->

    PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ wsealed ∗
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
    codefrag pc_a (owner ++ rest)
    ⊢ WP Seq (Instr Executable) @ E {{ v, ⌜v = HaltedV⌝ → P }}.
  Proof.
    intros owner; subst owner.
    iIntros (Hpc Hwsealed) "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Himports & Hcode)".
    pose proof allocator_size_imports as Himports_size.
    rewrite allocator_imports_length in Himports_size.
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    iEval (rewrite allocator_imports_split) in "Himports".
    iDestruct "Himports" as "(_ & Hkey & _)".
    iDestruct (codefrag_block0_acc with "Hcode") as "[Hown _]".
    iApply (allocator_owner_invalid_spec with "[$HPC $Hctp $Hct3 $Hct4 $Hca0 $Hown Hkey]");
      try done.
    { rewrite length_app in Hpc. solve_addr. }
    { apply withinBounds_true_iff. unfold allocator_unsealing_key_import_off.
      rewrite length_app in Hpc. solve_addr. }
  Qed.

  (** The owner block at an allocator entry point [pc_a], followed by the
      rest of the entry: the unsealing key is taken from the imports, and the
      rest of the code is given back at the end of the owner block. *)

  Lemma allocator_owner_entry_spec
    (E : coPset) (pc_a : Addr) (rest : list Word)
    (g : Locality) (a : Addr) (o : Z) (wtp w3 w4 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let owner := allocator_owner_instrs ctp ca0 ct3 ct4 in
    let pc_body := (pc_a ^+ length owner)%a in
    SubBounds allocator_pcc_b allocator_pcc_e pc_a (pc_a ^+ length (owner ++ rest))%a ->
    is_shadow_address a = false ->
    (a < a ^+ 1)%a ->

    PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e pc_a ∗
    ctp ↦ᵣ wtp ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca0 ↦ᵣ allocator_capability g a ∗
    [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
    a ↦ₐ WInt o ∗
    codefrag pc_a (owner ++ rest) ∗
    ▷ (PC ↦ᵣ WCap true RX Global allocator_pcc_b allocator_pcc_e pc_body ∗
         ctp ↦ᵣ WInt o ∗
         ct3 ↦ᵣ WInt 0 ∗
         ct4 ↦ᵣ WInt 0 ∗
         ca0 ↦ᵣ allocator_capability g a ∗
         [[allocator_pcc_b, allocator_code_b]] ↦ₐ [[lword_of_word <$> allocator_imports]] ∗
         a ↦ₐ WInt o ∗
         codefrag pc_body rest ∗
         (codefrag pc_body rest -∗ codefrag pc_a (owner ++ rest))
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros owner pc_body; subst owner pc_body.
    iIntros (Hpc Hshadow_a Ha)
      "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Himports & Howner & Hcode & Hφ)".
    pose proof allocator_size_imports as Himports_size.
    rewrite allocator_imports_length in Himports_size.
    assert (Hdisjoint : disjoint_from_shadow allocator_pcc_b allocator_pcc_e).
    { pose proof allocator_regions_disjoint as Hregions.
      unfold disjoint_from_shadow.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      set_solver. }
    iEval (rewrite allocator_imports_split) in "Himports".
    iDestruct "Himports" as "(Hshadow_import & Hkey & Hrevoker_import)".
    iDestruct (codefrag_block0_acc with "Hcode") as "[Hown Hcode_close]".
    iApply (allocator_owner_spec with "[- $HPC $Hctp $Hct3 $Hct4 $Hca0 $Howner $Hown]");
      try done.
    { rewrite length_app in Hpc. solve_addr. }
    { apply withinBounds_true_iff. unfold allocator_unsealing_key_import_off.
      rewrite length_app in Hpc. solve_addr. }
    rewrite /allocator_unsealing_key_import_off /allocator_unsealing_key. iFrame "Hkey".
    iNext. iIntros "(HPC & Hctp & Hct3 & Hct4 & Hca0 & Hkey & Howner & Hown)".
    iDestruct ("Hcode_close" with "Hown") as "Hcode".
    iDestruct (codefrag_block_acc 1 pc_a (allocator_owner_instrs ctp ca0 ct3 ct4 ++ rest)
      (allocator_owner_instrs ctp ca0 ct3 ct4) rest [] with "Hcode") as (ai) "(%Hai & Hrest & Hrest_close)".
    { rewrite /NthSubBlock app_nil_r //. }
    assert (ai = (pc_a ^+ length (allocator_owner_instrs ctp ca0 ct3 ct4))%a) as ->
      by solve_addr.
    iApply "Hφ". iFrame.
    iApply allocator_imports_split. iFrame.
  Qed.

End AllocatorOwnerMacro.
