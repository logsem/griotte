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

  (** Translate a heap interval to its shadow interval. The instruction list
      is shared by malloc block 4 and free block 3. *)

  Lemma allocator_translate_spec
    (E : coPset)
    (pc_b pc_e pc_a next b e : Addr) (w3 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_malloc_instrs_n 4 in
    let sb := (shadow_b ^+ (b - heap_b))%a in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length code)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b <= b /\ b < e /\ e <= heap_e)%a ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    ca2 ↦ᵣ wa2 ∗
    codefrag pc_a code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length code)%a ∗
         ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt e ∗
         ct3 ↦ᵣ WInt (b - heap_b) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         codefrag pc_a code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.

  Proof.
    intros code sb Hpc Hdisjoint Hheap; subst code sb.
    iIntros "(HPC & Hct0 & Hct1 & Hct2 & Hct3 & Hctp & Hca2 & Hcode & Hφ)".
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
