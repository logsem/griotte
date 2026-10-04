From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode memory_region region_keys.
From griotte.allocator Require Import allocator_preamble
  allocator_macros_spec allocator_header_spec.

(** The block specifications of [free]: one lemma per block of the assembled
    code, the revoker store, and the shadow-store permissions of the paint
    and the unpaint. The top-level specifications are in
    [allocator_free_spec]. *)

(** Address of an assembled block relative to the entry point. *)

Definition allocator_free_block_addr {MP : MachineParameters}
  (pc_a : Addr) (n : nat) : Addr :=
  (pc_a ^+ length (concat (take n assembled_allocator_free_body)))%a.

Global Instance allocator_free_in_prefix_dec {MP : MachineParameters} next w :
  Decision (allocator_free_in_prefix next w).
Proof.
  unfold allocator_free_in_prefix.
  destruct w as [z|sb|tag p g b e a|ot sb].
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - destruct sb as [tag p g b e a|tag p g b e a].
    + destruct tag.
      * destruct (decide (heap_b < b /\ b < e /\ e <= next)%a) as [Hbounds|Hbounds].
        { left. exists p, g, b, e, a. auto. }
        right. intros (p' & g' & b' & e' & a' & Heq & Hrange).
        inversion Heq; subst. contradiction.
      * right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
    + right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
  - right. intros (? & ? & ? & ? & ? & Heq & _). discriminate.
Defined.

Section AllocatorFreeBlocks.
  Context {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {FA : FreeAuth Σ}
    {MP : MachineParameters}
    {layout : allocatorLayout}.

  (** The revoker store: the sweep kills [ι], whose payload is quarantined.
      It reads the whole register file, which must hold no word with authority
      over [ι]. The shadow cursor is then rewound to the payload base for the
      unpaint. *)

  Lemma allocator_free_revoke_spec
    (E : coPset) (pc_b pc_e pc_a b e sb se : Addr) (ι : AId) (regs : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 7 in
    let code := allocator_free_body_instrs_n 7 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (se + (b - e))%a = Some sb ->
    dom regs = all_registers_s ∖ {[PC; ct1; ct2; ct3; ct4; ctp; ca2]} ->
    (∀ x lv, x ≠ cnull -> regs !! x = Some lv ->
       has_authority lv.(lw) -> lv.(lprov) ≠ Some ι) ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ allocator_revoker_cap ∗
    ct4 ↦ᵣ WInt 0 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
    ca2 ↦ᵣ WInt 0 ∗
    ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
    revoke_pre ι ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 8) ∗
         ct1 ↦ᵣ WInt b ∗
         ct2 ↦ᵣ WInt e ∗
         ct3 ↦ᵣ allocator_revoker_cap ∗
         ct4 ↦ᵣ WInt (b - e) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
         revoke_post ι ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hlayout Hcont Hpc Hdisjoint Hsb Hdom Hclean; subst start code.
    iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hpre & Hcode & Hφ)".
    codefrag_facts "Hcode".
    pose proof (@allocator_revoker_size MP layout Hlayout) as Hrev.
    assert (Hnone : ∀ r, r ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName) ->
      regs !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }
    (* Store ct3 0. *)
    unfold lword_of_word.
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    (* Assemble the whole register file. *)
    iDestruct (big_sepM_insert with "[$Hregs $Hca2]") as "Hregs";
      first (apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hctp]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct4]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct3]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct2]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct1]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $HPC]") as "Hregs";
      first (simplify_map_eq; apply Hnone; set_solver).
    iApply (wp_store_revoker _ RX Global pc_b pc_e (allocator_free_block_addr pc_a 7) None
              (allocator_free_block_addr pc_a 7 ^+ 1)%a _ _ ct3 (inl 0%Z) 0 RW Global
              revoker_addr (revoker_addr ^+ 1)%a revoker_addr {[ι]}
      with "[$Hi $Hregs Hpre]").
    { cbn. apply decode_encode_instrW_inv. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { by simplify_map_eq. }
    { intros x.
      destruct (decide (x ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName))) as [Hx|Hx].
      { rewrite !elem_of_union !elem_of_singleton in Hx.
        destruct_or! Hx; subst x; by simplify_map_eq. }
      rewrite !lookup_insert_ne; [|set_solver..].
      apply elem_of_dom. rewrite Hdom. apply elem_of_difference.
      split; [apply all_registers_s_correct|done]. }
    { split_and!; [by simplify_map_eq | by rewrite finz_add_0 | done |].
      apply withinBounds_true_iff. solve_addr. }
    { unfold allocator_free_block_addr in *. solve_addr. }
    { intros x lv ι' bv Hx Hlookup Htag Hbase Hprov.
      rewrite not_elem_of_singleton. intros ->.
      destruct (decide (x ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName))) as [Hin|Hin].
      { rewrite !elem_of_union !elem_of_singleton in Hin.
        destruct_or! Hin; subst x; simplify_map_eq; done. }
      do 7 (rewrite lookup_insert_ne in Hlookup; last set_solver).
      by apply (Hclean x lv Hx Hlookup); [split; [|exists bv]|]. }
    { by rewrite big_sepS_singleton. }
    iNext. iIntros "(Hi & Hregs & Hpost)".
    rewrite big_sepS_singleton insert_insert_eq.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Take the registers back. *)
    iDestruct (big_sepM_insert with "Hregs") as "[HPC Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct1 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct2 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct3 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct4 Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hctp Hregs]";
      first (simplify_map_eq; apply Hnone; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca2 Hregs]";
      first (apply Hnone; set_solver).
    assert (Hstep : (pc_a ^+ 68)%a = (allocator_free_block_addr pc_a 7 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite -Hstep Hstep) in "HPC".
    (* Sub ct4 ct1 ct2. *)
    iInstr "Hcode".
    (* Lea ctp ct4. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    assert (Hnext : (allocator_free_block_addr pc_a 7 ^+ 4)%a =
      allocator_free_block_addr pc_a 8)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hnext) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  (** The shadow-store permissions of the paint and of the unpaint. *)

  Lemma allocator_free_paint_ok ι b e :
    allocator_paint_ok (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι)) b e.
  Proof.
    intros a Rs Cs _. iIntros "HR HC [Htok Hc]".
    iDestruct (reg_lookup_own with "HR Htok") as %(b1 & e1 & γ & HRι).
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. right. by exists ι, (b1, e1, γ, APainting).
  Qed.

  Lemma allocator_free_unpaint_ok b e :
    allocator_paint_ok emp (λ a, addr_alloc a Unclaimed) b e.
  Proof.
    intros a Rs Cs _. iIntros "_ HC [_ Hc]".
    iDestruct (addr_alloc_lookup with "HC Hc") as %HCa.
    iPureIntro. by left.
  Qed.

  (** The local header check (D11). It reads the shadow entries of the word
      below the requested base, which must be painted (the last header word),
      and of the base, which must be unpainted; then the end recorded in the
      header three words below the base, which must match the requested end,
      and the owner recorded in the next header word, which must match the
      owner [o] of the allocator capability, in [ca0]. The header is read only
      when both shadow checks pass. On success the shadow cursor is at the
      base and the count of addresses to paint is in [ca2]. *)

  Lemma allocator_free_check_spec
    (E : coPset) (pc_b pc_e pc_a next b e eh sb : Addr) (o oh : Z) (s1 s2 : AllocStatus)
    (w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 3 in
    let code := allocator_free_body_instrs_n 3 in
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    (s1 = ShadowQuarantined -> s2 = ShadowLive ->
      (heap_b + allocator_header_words < b)%Z) ->
    (shadow_b + (b - heap_b))%a = Some sb ->
    heap_to_shadow (b ^+ (-1))%a = Some (sb ^+ (-1))%a ->
    heap_to_shadow b = Some sb ->

    (b ^+ (-1))%a ↦ₛ s1 ∗
    b ↦ₛ s2 ∗
    (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
     then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
          ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
     else emp) ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ WInt o ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    codefrag start code ∗
    ▷ ((b ^+ (-1))%a ↦ₛ s1 ∗
       b ↦ₛ s2 ∗
       (if decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)
        then (b ^+ (- allocator_header_words))%a ↦ₐ WInt eh ∗
             ((b ^+ (- allocator_header_words)) ^+ 1)%a ↦ₐ WInt oh
        else emp) ∗
       ca0 ↦ᵣ WInt o ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ct4 ↦ᵣ - ∗
       codefrag start code ∗
       ((⌜s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 4) ∗
         ct3 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb)
        ∨
        (⌜¬ (s1 = ShadowQuarantined ∧ s2 = ShadowLive ∧ eh = e ∧ oh = o)⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10) ∗
         ct3 ↦ᵣ - ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ -))
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hdisjoint Hbounds Hheader Hsb Htr1 Htr2; subst start code.
    iIntros "(Hs1 & Hs2 & Hhdr & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hctp & Hcode & Hφ)".
    codefrag_facts "Hcode".
    assert (Henc : ∀ s s', s ≠ s' → encodeAllocStatus s ≠ encodeAllocStatus s').
    { intros s s' Hne Heq. apply Hne.
      rewrite -(decode_encode_alloc_status_inv s) -(decode_encode_alloc_status_inv s') Heq //. }
    assert (Hinvalid : (allocator_free_block_addr pc_a 3 ^+ 47)%a = allocator_free_block_addr pc_a 10)
      by (unfold allocator_free_block_addr; solve_addr).
    pose proof heap_shadow_same_size as Hss.
    assert (Hsb1 : (shadow_b <= (sb ^+ -1)%a /\ (sb ^+ -1)%a < shadow_e)%a) by solve_addr.
    assert (Hsbr : (shadow_b <= sb /\ sb < shadow_e)%a) by solve_addr.
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 30)%a = (allocator_free_block_addr pc_a 3 ^+ 1)%a)
      by (unfold allocator_free_block_addr; solve_addr).
    iEval (rewrite Hstep) in "HPC".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    replace (b - heap_b - 1)%Z with ((sb ^+ -1)%a - shadow_b)%Z by solve_addr.
    (* Lea ctp ct3. *)
    iInstr "Hcode".
    unfold lword_of_word.
    (* Load ct3 ctp: the shadow entry of the word below the base. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hs1]"); try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    { apply heap_shadow_inverse. exact Htr1. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr1)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hs1)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowQuarantined). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowQuarantined)
      with (encodeAllocStatus ShadowQuarantined).
    destruct (decide (s1 = ShadowQuarantined)) as [->|Hs1q]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s1 - encodeAllocStatus ShadowQuarantined) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs1q). lia. }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      rewrite Hinvalid.
      iApply "Hφ". iFrame. iRight. iSplit.
      { iPureIntro. intros (? & _). done. }
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. iSplitL "Hca2"; [by iExists _|].
      by iExists _. }
    rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Lea ctp 1. *)
    iInstr "Hcode".
    replace ((sb ^+ -1) ^+ 1)%a with sb by solve_addr.
    (* Load ct3 ctp: the shadow entry of the base. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_from_shadow _ ct3 ctp with "[$HPC $Hi $Hct3 $Hctp $Hs2]"); try solve_pure.
    { exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    { apply heap_shadow_inverse. exact Htr2. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { split; first done. exact (proj2 (heap_to_shadow_bounds _ _ Htr2)). }
    iIntros "!> (HPC & Hct3 & Hi & Hctp & Hs2)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    (* Sub ct3 ct3 (encodeAllocStatus ShadowLive). *)
    iInstr "Hcode".
    change (match MP with {| encodeAllocStatus := f |} => f end ShadowLive)
      with (encodeAllocStatus ShadowLive).
    destruct (decide (s2 = ShadowLive)) as [->|Hs2l]; last first.
    { assert (Hneq : WInt (encodeAllocStatus s2 - encodeAllocStatus ShadowLive) ≠ WInt 0).
      { intros [=]. apply (Henc _ _ Hs2l). lia. }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      rewrite Hinvalid.
      iApply "Hφ". iFrame. iRight. iSplit.
      { iPureIntro. intros (_ & ? & _). done. }
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _. }
    rewrite Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    specialize (Hheader eq_refl eq_refl).
    iDestruct "Hhdr" as "[Hhdr Hown]".
    (* Mov ct4 ct0. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Sub ct3 ct1 ct3. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 allocator_header_words. *)
    iInstr "Hcode".
    unfold allocator_header_words in *.
    change (Z.opp 3) with (-3)%Z in *.
    replace (b - next - 3)%Z with ((b ^+ -3)%a - next)%Z by solve_addr.
    (* Lea ct4 ct3. *)
    iInstr "Hcode".
    (* Load ca2 ct4: the recorded end. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_notinstr _ ca2 ct4 with "[$HPC $Hi $Hca2 $Hct4 $Hhdr]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in heap_b heap_e (b ^+ -3)%a);
        first exact heap_shadow_disjoint.
      apply withinBounds_true_iff. solve_addr. }
    { reflexivity. }
    { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
    { split; first done. apply withinBounds_true_iff. solve_addr. }
    iIntros "!> (HPC & Hca2 & Hi & Hct4 & Hhdr)".
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hca2".
    (* Sub ct3 ca2 ct2. *)
    iInstr "Hcode".
    destruct (decide (eh = e)) as [->|Hne].
    - rewrite Z.sub_diag.
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      (* Load ct3 ct4 1: the recorded owner. *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_success_notinstr_imm _ ct3 ct4 with "[$HPC $Hi $Hct3 $Hct4 $Hown]");
        try solve_pure.
      { eapply (disjoint_from_shadow_not_in heap_b heap_e ((b ^+ -3) ^+ 1)%a);
          first exact heap_shadow_disjoint.
        apply withinBounds_true_iff. solve_addr. }
      { reflexivity. }
      { constructor; [unfold allocator_free_block_addr; solve_addr|done]. }
      { split; first done. apply withinBounds_true_iff. solve_addr. }
      { solve_addr. }
      iIntros "!> (HPC & Hct3 & Hi & Hct4 & Hown)".
      wp_pure.
      iSpecialize ("Hcode" with "Hi").
      iEval (rewrite /lload_word /lift_word /=) in "Hct3".
      (* Sub ct3 ct3 ca0. *)
      iInstr "Hcode".
      destruct (decide (oh = o)) as [->|Hneo].
      + rewrite Z.sub_diag.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        (* Sub ca2 ct2 ct1. *)
        iInstr "Hcode".
        assert (Hfound : (allocator_free_block_addr pc_a 3 ^+ 23)%a = allocator_free_block_addr pc_a 4)
          by (unfold allocator_free_block_addr; solve_addr).
        iEval (rewrite Hfound) in "HPC".
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame. iLeft. iFrame. done.
      + assert (Hneq : WInt (oh - o) ≠ WInt 0) by (intros [=]; apply Hneo; lia).
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        rewrite Hinvalid.
        iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
        iFrame. iRight. iSplit; first (iPureIntro; intros (_ & _ & _ & ?); done).
        iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
    - assert (Hneq : WInt (eh - e) ≠ WInt 0) by (intros [=]; apply Hne; solve_addr).
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      rewrite Hinvalid.
      iApply "Hφ". case_decide as Hd; [|exfalso; naive_solver].
      iFrame. iRight. iSplit; first (iPureIntro; intros (_ & _ & ? & _); done).
      iFrame "HPC". iSplitL "Hct3"; [by iExists _|]. by iExists _.
  Qed.

  Lemma allocator_free_success_block_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wreq wstatus : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 5 in
    let code := allocator_free_body_instrs_n 5 in
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->

    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wstatus ∗
    codefrag start code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e
           (allocator_free_block_addr pc_a 6) ∗
         ca0 ↦ᵣ WInt ALLOC_OK ∗
         ca1 ↦ᵣ WInt 0 ∗
         codefrag start code
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code Hcont Hpc Hshadow; subst start code.
    iIntros "(HPC & Hca0 & Hca1 & Hcode & Hφ)".
    codefrag_facts "Hcode".
    (* Mov ca0 ALLOC_OK. *)
    iInstr "Hcode".
    assert (Hstep : (pc_a ^+ 57)%a =
      ((allocator_free_block_addr pc_a 5) ^+ 1)%a).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hstep) in "HPC".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    assert (Hnext : (allocator_free_block_addr pc_a 5 ^+ 2)%a =
      allocator_free_block_addr pc_a 6).
    { unfold allocator_free_block_addr. solve_addr. }
    iEval (rewrite Hnext) in "HPC".
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_free_prepare_valid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (o : Z)
    (wreq wa0 w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_body_instrs_n 0 ++ allocator_free_body_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    allocator_free_in_prefix next wreq.(lw) ->

    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ WInt o ∗
         ca1 ↦ᵣ wreq ∗
         ctp ↦ᵣ WInt o ∗
         codefrag pc_a code ∗
         (∃ (p : Perm) (g : Locality) (b e a : Addr),
             ⌜wreq.(lw) = WCap true p g b e a
               ∧ (heap_b < b /\ b < e /\ e <= next)%a⌝ ∗
             PC ↦ᵣ WCap true RX Global pc_b pc_e
                 (allocator_free_block_addr pc_a 2) ∗
             ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
             ct1 ↦ᵣ WInt b ∗
             ct2 ↦ᵣ WInt e ∗
             ct3 ↦ᵣ WInt 0)
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout Hcont Hpc Hdisjoint Hcgp_pc (p & g & b & e & a & Hreq & Hbounds);
      subst code.
    destruct wreq as [wreq π]; cbn in Hreq; subst wreq.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.
    codefrag_facts "Hcode".
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    rewrite (encodeWordType_correct_cap true p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* GetTag ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 1. *)
    iInstr "Hcode".
    rewrite /Z.b2z Z.sub_diag.
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    (* Reload the heap root: it is identifier-less and has authority, so it
       loads exactly. *)
    unfold lword_of_word.
    (* Load ct0 cgp. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
    { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
      { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
        unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
        cbn [union_list] in Hregions. set_solver. }
      { apply withinBounds_true_iff. solve_addr. } }
    { done. }
    { intros _. left. pose proof heap_valid. apply has_authority_heap_cap; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between.
      unfold allocator_free_body_instrs in Hpc. solve_addr. }
    iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iEval (rewrite /lload_word /lift_word /=) in "Hct0".
    iEval (cbn [load_word]) in "Hct0".
    (* GetB ct1 ca1. *)
    iInstr "Hcode".
    (* GetE ct2 ca1. *)
    iInstr "Hcode".
    (* GetB ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct1. *)
    iInstr "Hcode".
    replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_base_ok ct3. *)
    iInstr "Hcode".
    (* Lt ct3 ct1 ct2. *)
    iInstr "Hcode".
    replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
    (* Jnz .free_nonempty ct3. *)
    iInstr "Hcode".
    (* GetA ct3 ct0. *)
    iInstr "Hcode".
    (* Lt ct3 ct3 ct2. *)
    iInstr "Hcode".
    replace (next <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
    (* Jnz .free_invalid ct3. *)
    iInstr "Hcode".
    iApply "Hφ".
    iFrame "Hslot Hcgp Hca0 Hca1 Hctp Hcode".
    iExists p, g, b, e, a.
    iSplit.
    { iPureIntro. split; first done. exact Hbounds. }
    iFrame.
  Qed.

  Lemma allocator_free_prepare_invalid_spec
    (E : coPset)
    (pc_b pc_e pc_a next : Addr) (o : Z)
    (wreq wa0 w0 w1 w2 w3 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let code := allocator_free_body_instrs_n 0 ++ allocator_free_body_instrs_n 1 in
    allocatorLayoutWf ->
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    allocator_cgp_b ∉ finz.seq_between pc_b pc_e ->
    ¬ allocator_free_in_prefix next wreq.(lw) ->

    allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    ca0 ↦ᵣ wa0 ∗
    ca1 ↦ᵣ wreq ∗
    ctp ↦ᵣ WInt o ∗
    ct0 ↦ᵣ w0 ∗
    ct1 ↦ᵣ w1 ∗
    ct2 ↦ᵣ w2 ∗
    ct3 ↦ᵣ w3 ∗
    codefrag pc_a code ∗
    ▷ (allocator_cgp_b ↦ₐ WCap true RW Global heap_b heap_e next ∗
         cgp ↦ᵣ WCap true RW Global
             allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
         ca0 ↦ᵣ WInt o ∗
         ca1 ↦ᵣ wreq ∗
         ctp ↦ᵣ WInt o ∗
         codefrag pc_a code ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e
             (allocator_free_block_addr pc_a 10) ∗
         ct0 ↦ᵣ - ∗
         ct1 ↦ᵣ - ∗
         ct2 ↦ᵣ - ∗
         ct3 ↦ᵣ -
         -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros code Hlayout Hcont Hpc Hdisjoint Hcgp_pc Hrequest; subst code.
    destruct wreq as [wreq π]; cbn in Hrequest.
    iIntros "(Hslot & HPC & Hcgp & Hca0 & Hca1 & Hctp & Hct0 & Hct1 & Hct2 & Hct3 & Hcode & Hφ)".
    pose proof (@allocator_size_data MP layout Hlayout) as Hsize. cbn in Hsize.
    codefrag_facts "Hcode".
    (* Mov ca0 ctp. *)
    iInstr "Hcode".
    (* GetWType ct3 ca1. *)
    iInstr "Hcode".
    (* Sub ct3 ct3 (encodeWordType wt_cap). *)
    iInstr "Hcode".
    destruct (is_cap wreq) eqn:Hreq_cap.
    + destruct wreq; cbn in Hreq_cap; try done.
      destruct sb; cbn in Hreq_cap; try done.
      rewrite (encodeWordType_correct_cap tag p g b e a true (O LG LM) Global 0%a 0%a 0%a) /wt_cap Z.sub_diag.
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      (* GetTag ct3 ca1. *)
      iInstr "Hcode".
      (* Sub ct3 ct3 1. *)
      iInstr "Hcode".
      destruct tag.
      * rewrite /Z.b2z Z.sub_diag.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        unfold lword_of_word.
        (* Load ct0 cgp. *)
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (wp_load_success_exact with "[$HPC $Hi $Hct0 $Hcgp $Hslot]"); try solve_pure.
        { eapply (disjoint_from_shadow_not_in allocator_cgp_b allocator_cgp_e allocator_cgp_b).
          { pose proof (@allocator_regions_disjoint MP layout Hlayout) as Hregions.
            unfold disjoint_from_shadow. rewrite !disjoint_list_cons in Hregions.
            cbn [union_list] in Hregions. set_solver. }
          { apply withinBounds_true_iff. solve_addr. } }
        { done. }
        { intros _. left. pose proof heap_valid. apply has_authority_heap_cap; solve_addr. }
        { apply withinBounds_true_iff. solve_addr. }
        { intros Heq. apply Hcgp_pc. rewrite Heq elem_of_finz_seq_between.
          unfold allocator_free_body_instrs in Hpc. solve_addr. }
        iIntros "!> (HPC & Hi & Hct0 & Hcgp & Hslot)". wp_pure.
        iSpecialize ("Hcode" with "Hi").
        iEval (rewrite /lload_word /lift_word /=) in "Hct0".
        iEval (cbn [load_word]) in "Hct0".
        (* GetB ct1 ca1. *)
        iInstr "Hcode".
        (* GetE ct2 ca1. *)
        iInstr "Hcode".
        (* GetB ct3 ct0. *)
        iInstr "Hcode".
        (* Lt ct3 ct3 ct1. *)
        iInstr "Hcode".
        destruct (decide (heap_b < b)%a) as [Hbase|Hbase].
        ** replace (heap_b <? b)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
          (* Jnz .free_base_ok ct3. *)
          iInstr "Hcode".
          (* Lt ct3 ct1 ct2. *)
          iInstr "Hcode".
          destruct (decide (b < e)%a) as [Hnonempty|Hempty].
          {
            replace (b <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
            (* Jnz .free_nonempty ct3. *)
            iInstr "Hcode".
            (* GetA ct3 ct0. *)
            iInstr "Hcode".
            (* Lt ct3 ct3 ct2. *)
            iInstr "Hcode".
            destruct (decide (next < e)%a) as [Hpast|Hwithin].
            {
              replace (next <? e)%Z with true by (symmetry; apply Z.ltb_lt; solve_addr).
              (* Jnz .free_invalid ct3. *)
              iInstr "Hcode".
              iApply "Hφ". iFrame.
            }
            { exfalso. apply Hrequest.
              exists p, g, b, e, a. split; first reflexivity. solve_addr. }
          }
          replace (b <? e)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_nonempty ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame.
        ** replace (heap_b <? b)%Z with false by (symmetry; apply Z.ltb_ge; solve_addr).
          (* Jnz .free_base_ok ct3. *)
          iInstr "Hcode".
          (* Jmp .free_invalid. *)
          iInstr "Hcode".
          iApply "Hφ". iFrame.
      * cbn.
        (* Jnz .free_invalid ct3. *)
        iInstr "Hcode".
        iApply "Hφ". iFrame.
    + assert (Hnoncap : WInt (encodeWordType wreq - encodeWordType wt_cap) ≠ WInt 0).
      {
        pose proof (encodeWordType_correct wreq wt_cap) as Hencode.
        intro Hzero.
        injection Hzero as Hzero.
        assert (Heq : encodeWordType wreq = encodeWordType wt_cap) by lia.
        destruct wreq; cbn in Hreq_cap, Hencode; try discriminate.
        all: try (destruct sb; cbn in Hreq_cap, Hencode; try discriminate); contradiction.
      }
      (* Jnz .free_invalid ct3. *)
      iInstr "Hcode".
      iApply "Hφ". iFrame.
  Qed.

  Context {layout_wf : allocatorLayoutWf}.

  (** The local header check against the service invariant: with the cells
      and the header chain of the service, the check succeeds exactly when the
      requested bounds are those of a ghost header entry recorded with the
      owner [o] of the allocator capability, in [ca0]. Header words are
      exactly the painted cells, so the word below [b] is painted and [b] is
      not exactly when [b] is a payload base (D11). *)

  Lemma allocator_free_local_check_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr) (o : Z)
    (allocations : list allocator_header_entry) (live issued : gset AId)
    (Cs : gmap Addr (AddrClaim * AllocStatus * bool))
    (w3 w4 wa2 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :

    let start := allocator_free_block_addr pc_a 3 in
    let code := allocator_free_body_instrs_n 3 in
    let sb := (shadow_b ^+ (b - heap_b))%a in
    ContiguousRegion pc_a (length allocator_free_body_instrs) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length allocator_free_body_instrs)%a ->
    disjoint_from_shadow pc_b pc_e ->
    (heap_b < b /\ b < e /\ e <= next /\ next <= heap_e)%a ->
    allocator_chain (heap_b ^+ 1)%a next allocations ->
    allocator_cells_wf next allocations live issued Cs ->

    allocator_cells Cs ∗
    allocator_headers (heap_b ^+ 1)%a next allocations ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e start ∗
    ca0 ↦ᵣ WInt o ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ca2 ↦ᵣ wa2 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e shadow_b ∗
    codefrag start code ∗
    ▷ (allocator_cells Cs ∗
       allocator_headers (heap_b ^+ 1)%a next allocations ∗
       ca0 ↦ᵣ WInt o ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ct4 ↦ᵣ - ∗
       codefrag start code ∗
       ((⌜allocator_owned_bounds allocations o b e⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 4) ∗
         ct3 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ WInt (e - b) ∗
         ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb)
        ∨
        (⌜¬ allocator_owned_bounds allocations o b e⌝ ∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (allocator_free_block_addr pc_a 10) ∗
         ct3 ↦ᵣ - ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ -))
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros start code sb Hcont Hpc Hdisjoint Hbounds Hchain Hcwf; subst start code sb.
    iIntros "(Hcells & Hheaders & HPC & Hca0 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hca2 & Hctp &
      Hcode & Hφ)".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid as Hheap_valid.
    set (sb := (shadow_b ^+ (b - heap_b))%a).
    assert (Hsb : (shadow_b + (b - heap_b))%a = Some sb).
    { unfold sb. clear -Hss Hbounds Hheap_valid. solve_addr. }
    assert (Htranslation : ∀ x, (heap_b <= x /\ x < heap_e)%a ->
      heap_to_shadow x = Some (shadow_b ^+ (x - heap_b))%a).
    { intros x Hx. rewrite allocator_translation_affine.
      unfold translate_region.
      assert (Hxheap : withinBounds heap_b heap_e x = true).
      { apply withinBounds_true_iff. clear -Hx. solve_addr. }
      rewrite Hxheap. clear -Hx Hheap_valid Hss. solve_addr. }
    assert (Htr1 : heap_to_shadow (b ^+ -1)%a = Some (sb ^+ -1)%a).
    { rewrite Htranslation; last solve_addr. f_equal. unfold sb. solve_addr. }
    assert (Htr2 : heap_to_shadow b = Some sb).
    { rewrite Htranslation; last solve_addr. done. }
    assert (Hb1 : ((b ^+ -1) + 1)%a = Some b) by solve_addr.
    destruct (acw_dom _ _ _ _ _ Hcwf (b ^+ -1)%a) as [ [ [c1 s1] h1] Hc1]; first solve_addr.
    destruct (acw_dom _ _ _ _ _ Hcwf b) as [ [ [c2 s2] h2] Hc2]; first solve_addr.
    pose proof (acw_header _ _ _ _ _ Hcwf _ _ _ _ Hc1) as Hh1.
    pose proof (acw_header _ _ _ _ _ Hcwf _ _ _ _ Hc2) as Hh2.
    pose proof (acw_painted _ _ _ _ _ Hcwf _ _ _ _ Hc1) as Hp1.
    pose proof (acw_painted _ _ _ _ _ Hcwf _ _ _ _ Hc2) as Hp2.
    (* A ghost header entry at [b] is seen by the check. *)
    assert (Hseen : ∀ e' r ι, (b, e', r, ι) ∈ allocations ->
      s1 = ShadowQuarantined ∧ s2 = ShadowLive).
    { intros e' r ι Hin. split.
      - apply Hp1, Hh1. by eapply allocator_is_header_below.
      - destruct s2; first done. exfalso.
        pose proof (allocator_chain_member_bounds _ _ _ _ _ _ _ Hchain Hin).
        apply (allocator_chain_payload_not_header _ _ _ _ _ _ _ b Hchain Hin);
          first solve_addr.
        by apply Hh2, Hp2. }
    iDestruct (allocator_cells_shadow_pair _ (b ^+ -1)%a b with "Hcells")
      as "(Hs1 & Hs2 & Hcells_close)"; [solve_addr|exact Hc1|exact Hc2|].
    destruct (decide (s1 = ShadowQuarantined ∧ s2 = ShadowLive)) as [ [-> ->]|Hcheck].
    - (* The base follows a header word: it is the base of an entry. *)
      destruct (allocator_is_header_base allocations (b ^+ -1)%a b) as (e' & [oh r] & ι & Hin).
      { by apply Hh1, Hp1. }
      { intros Hh. by apply Hh2 in Hh; apply Hp2 in Hh. }
      { exact Hb1. }
      pose proof (allocator_chain_member_header _ _ _ _ _ _ _ Hchain Hin) as Hhb.
      iDestruct (allocator_headers_acc with "Hheaders") as "(Hend & Hown & Hheaders_close)";
        first exact Hin.
      iApply (allocator_free_check_spec _ _ _ _ next b e e' sb o oh ShadowQuarantined ShadowLive
        with "[- $Hs1 $Hs2 $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hctp $Hcode]");
        try done.
      { intros _ _. unfold allocator_header_words in *. solve_addr. }
      iSplitL "Hend Hown"; first (case_decide as Hd; [iFrame|exfalso; naive_solver]).
      iNext. iIntros "(Hs1 & Hs2 & Hhdr & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 & Hcode & Hout)".
      case_decide as Hd; last (exfalso; naive_solver).
      iDestruct "Hhdr" as "[Hend Hown]".
      iApply "Hφ". iFrame "Hca0 Hct0 Hct1 Hct2 Hct4 Hcode".
      iSplitL "Hcells_close Hs1 Hs2"; first iApply ("Hcells_close" with "Hs1 Hs2").
      iSplitL "Hheaders_close Hend Hown"; first iApply ("Hheaders_close" with "Hend Hown").
      iDestruct "Hout" as "[(%Hok & Hrest)|(%Hko & Hrest)]".
      + iLeft. iFrame. iPureIntro. destruct Hok as (_ & _ & <- & <-). by exists r, ι.
      + iRight. iFrame. iPureIntro. intros (r' & ι' & Hin').
        destruct (allocator_chain_base_unique _ _ _ _ _ _ _ _ _ _ Hchain Hin Hin')
          as (<- & Hr & _).
        injection Hr as <- _.
        by apply Hko.
    - (* The check fails before the header is read. *)
      iApply (allocator_free_check_spec _ _ _ _ next b e b sb o 0 s1 s2
        with "[- $Hs1 $Hs2 $HPC $Hca0 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hca2 $Hctp $Hcode]");
        try done.
      { intros ? ?. exfalso. naive_solver. }
      iSplitR; first (case_decide; [exfalso; naive_solver|done]).
      iNext. iIntros "(Hs1 & Hs2 & _ & Hca0 & Hct0 & Hct1 & Hct2 & Hct4 & Hcode & Hout)".
      iApply "Hφ". iFrame "Hca0 Hct0 Hct1 Hct2 Hct4 Hcode Hheaders".
      iSplitL "Hcells_close Hs1 Hs2"; first iApply ("Hcells_close" with "Hs1 Hs2").
      iDestruct "Hout" as "[(%Hok & _)|(_ & Hrest)]".
      + exfalso. naive_solver.
      + iRight. iFrame. iPureIntro. intros (r & ι & Hin). by apply Hcheck, (Hseen e (o, r) ι).
  Qed.

End AllocatorFreeBlocks.
