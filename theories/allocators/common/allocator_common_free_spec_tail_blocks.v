From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.common Require Import allocator_common_spec_states.

(** * Free, the tail

    The tail [allocator_free_tail_code] of [free] is shared by the
    allocators.

    Block 0 paints the payload [b, e) quarantined, while the status token of
    its identifier [ι] is in [APainting]. Block 1 sets the result
    [ALLOC_OK] and clears [ca1].

    Block 2 stores to the revoker, through the revoker capability in [ca3]:
    the sweep kills [ι], whose payload is quarantined. It reads the whole
    register file, which must hold no word with authority over [ι]. The
    shadow cursor is then rewound to the payload base. Block 3 unpaints the
    revoked payload, whose cells are now unclaimed.

    After a successful [free], block 4 jumps to the return, block 6. A
    rejected request continues at block 5, which sets [ALLOC_INVALID] and
    clears [ca1], and returns through block 6. *)

Section AllocatorFreeTailBlocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorCommonLayoutWf}.

  Lemma allocator_free_quarantine_spec
    (E : coPset) (pc_b pc_e pc_a b e : Addr) (ι : AId) (wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e pc_a ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (b - heap_b))%a ∗
    ca2 ↦ᵣ WInt (e - b) ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    ι ↦st{1} APainting ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a (Claimed ι)) ∗
    codefrag_pers pc_a allocator_free_tail_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 2)%a ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
       ca2 ↦ᵣ WInt 0 ∗
       ca0 ↦ᵣ WInt ALLOC_OK ∗
       ca1 ↦ᵣ WInt 0 ∗
       ι ↦st{1} APainting ∗
       ([∗ list] a ∈ finz.seq_between b e,
          a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι)) ∗
       codefrag_pers pc_a allocator_free_tail_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow) Hbounds.
    iIntros "(HPC & Hctp & Hca2 & Hca0 & Hca1 & Hpainting & Hpayload & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.

    (* Block 0: paint the payload quarantined *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_paint_spec ShadowLive ShadowQuarantined ctp ca2 E RX Global
      pc_b pc_e pc_a b e (shadow_b ^+ (b - heap_b))%a (shadow_b ^+ (e - heap_b))%a
      (ι ↦st{1} APainting) (λ a, addr_alloc a (Claimed ι))
      with "[- $HPC $Hctp $Hca2 $Hcode $Hpainting $Hpayload]");
      [done|solve_addr|done|solve_addr|solve_addr|solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_painting. }
    iNext. iIntros "(HPC & Hctp & Hca2 & Hpainting & Hpayload & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 1: the result *)
    focus_block 1 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_success Ha_success
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ALLOC_OK. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_tail_block_offset 2)%a.
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  (** Block 2: the revoker store, over the whole register file [regs].
      Right before the store, with the PC and the whole register file in
      hand, none of whose words with authority carries [ι], the painted
      payload moves the status token of [ι] to [AQuar]. *)
  Lemma allocator_free_revoke_store_spec
    (E : coPset) (pc_b pc_e pc_a b e sb se : Addr) (ι : AId) (w4 wa2 : LWord) (regs : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e pc_a ->
    (se + (b - e))%a = Some sb ->
    dom regs = all_registers_s ∖ {[ct1; ct2; ca3; ca4; ctp; ca2]} ->
    (∀ x lv, x ≠ cnull -> regs !! x = Some lv ->
       has_authority lv.(lw) -> lv.(lprov) ≠ Some ι) ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 2)%a ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ca3 ↦ᵣ allocator_revoker_cap ∗
    ca4 ↦ᵣ w4 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
    ca2 ↦ᵣ wa2 ∗
    ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
    alloc_obj ι b e ∗
    ι ↦st{1} APainting ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι)) ∗
    codefrag_pers pc_a allocator_free_tail_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 3)%a ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ca3 ↦ᵣ allocator_revoker_cap ∗
       ca4 ↦ᵣ WInt (b - e) ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
       ca2 ↦ᵣ WInt (e - b) ∗
       ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
       revoke_post ι ∗
       ι ⊒ AQuar ∗
       codefrag_pers pc_a allocator_free_tail_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow) Hsb Hdom Hclean.
    iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & #Hobj & Hpainting &
      Hpayload & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".
    pose proof allocator_common_revoker_size as Hrev.
    assert (Hnone : ∀ r, r ∈ ({[ct1; ct2; ca3; ca4; ctp; ca2]} : gset RegName) ->
      regs !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }

    (* Block 2: the revoker store, and the rewind of the shadow cursor *)
    focus_block 2 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_revoke Ha_revoke
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Sub ca4 ct1 ct2. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
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
    (* Every cell is quarantined and no register carries [ι]: the status
       token moves to [AQuar]. *)
    iDestruct (big_sepL_sep with "Hpayload") as "[Hshadows Hclaims]".
    iMod (reg_quarantine _ ι b e with "Hobj Hpainting Hshadows HPC Hregs")
      as "(Hquar & #Hq & Hshadows & HPC & Hregs)".
    { intros x.
      destruct (decide (x ∈ ({[ct1; ct2; ca3; ca4; ctp; ca2]} : gset RegName))) as [Hx|Hx].
      { rewrite !elem_of_union !elem_of_singleton in Hx.
        destruct_or! Hx; subst x; by simplify_map_eq. }
      rewrite !lookup_insert_ne; [|set_solver..].
      apply elem_of_dom. rewrite Hdom. apply elem_of_difference.
      split; [apply all_registers_s_correct|done]. }
    { intros v [-> | (x & Hxn & Hlookup)] Hauth; first done.
      destruct (decide (x ∈ ({[ct1; ct2; ca3; ca4; ctp; ca2]} : gset RegName))) as [Hin|Hin].
      { rewrite !elem_of_union !elem_of_singleton in Hin.
        destruct_or! Hin; subst x; simplify_map_eq; done. }
      do 6 (rewrite lookup_insert_ne in Hlookup; last set_solver).
      by apply (Hclean x v Hxn Hlookup). }
    iCombine "Hshadows Hclaims" as "Hpayload".
    rewrite -big_sepL_sep.
    unfold lword_of_word.
    (* Store ca3 0. *)
    iInstrApply "Hcode" (wp_store_revoker _ RX Global pc_b pc_e (a_revoke ^+ 2)%a None
              (a_revoke ^+ 3)%a _ _ ca3 (inl 0%Z) 0 RW Global
              revoker_addr (revoker_addr ^+ 1)%a revoker_addr {[ι]})
      with "[$HPC $Hregs Hquar Hpayload]"
      as "(HPC & Hregs & Hpost)".
    { rewrite /regs_of !dom_insert_L. set_solver. }
    { split_and!; [by simplify_map_eq | by rewrite finz_add_0 | done |].
      apply withinBounds_true_iff. solve_addr. }
    { intros v Hv. by simplify_map_eq. }
    { rewrite big_sepS_singleton. iExists b, e. iFrame "Hobj Hquar Hpayload". }
    rewrite big_sepS_singleton.
    (* Take the registers back. *)
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
    (* Lea ctp ca4. *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_tail_block_offset 3)%a.
    iApply "Hφ". iFrame "∗ Hq Hcode_main".
  Qed.

  Lemma allocator_free_revoke_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr) (ι : AId)
    (w4 wa2 wret wnull : LWord) (rmap : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e pc_a ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    dom rmap = all_registers_s ∖
      {[cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ca3; ca4; ctp; cnull]} ->
    (∀ r w, rmap !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None) ->
    (has_authority wret.(lw) -> wret.(lprov) = None) ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 2)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ WInt ALLOC_OK ∗
    ca1 ↦ᵣ WInt 0 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ca3 ↦ᵣ allocator_revoker_cap ∗
    ca4 ↦ᵣ w4 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
    cnull ↦ᵣ wnull ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    alloc_obj ι b e ∗
    ι ↦st{1} APainting ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι)) ∗
    codefrag_pers pc_a allocator_free_tail_code ∗
    ▷ (PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 4)%a ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_OK ∗
       ca1 ↦ᵣ WInt 0 ∗
       ca2 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ca3 ↦ᵣ allocator_revoker_cap ∗
       ca4 ↦ᵣ WInt (b - e) ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
       cnull ↦ᵣ wnull ∗
       ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
       ι ↦st{1} ADead ∗
       ι ⊒ AQuar ∗
       ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
       codefrag_pers pc_a allocator_free_tail_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds_code Hbounds Hdom Hclean Hclean_ret.
    pose proof Hbounds_code as (Hpc & Hpc_shadow).
    iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp &
      Hcnull & Hrmap & #Hobj & Hpainting & Hpayload & #Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sb := (shadow_b ^+ (b - heap_b))%a).
    set (se := (shadow_b ^+ (e - heap_b))%a).

    (* Block 2: the revoker store, with the rest of the register file *)
    assert (Hrmap_none : ∀ r, r ∈ ({[cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ca3; ca4;
                                     ctp; cnull]} : gset RegName) -> rmap !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }
    iDestruct (big_sepM_insert with "[$Hrmap $Hcnull]") as "Hregs";
      first (apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hct0]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hca1]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hca0]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hcra]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "[$Hregs $Hcgp]") as "Hregs";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iApply (allocator_free_revoke_store_spec _ _ _ _ b e sb se ι with
      "[- $HPC $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hca2 $Hregs $Hobj $Hpainting $Hpayload
          $Hcode_main]").
    { exact Hbounds_code. }
    { subst sb se. solve_addr. }
    { rewrite !dom_insert_L Hdom.
      apply set_eq. intros x. pose proof (all_registers_s_correct x).
      destruct (decide (x ∈ ({[cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ca3; ca4; ctp;
                               cnull]} : gset RegName))) as [Hx|Hx]; set_solver. }
    { intros x lv Hx Hlookup Hauth.
      destruct (decide (x = cgp)); [subst; simplify_map_eq; done|].
      destruct (decide (x = cra)); [subst; simplify_map_eq; by rewrite Hclean_ret|].
      destruct (decide (x = ca0)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ca1)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ct0)); [subst; simplify_map_eq; done|].
      rewrite !lookup_insert_ne // in Hlookup.
      by rewrite (Hclean _ _ Hlookup Hauth). }
    iNext. iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hdead & #Hq &
      _)".
    iDestruct "Hdead" as (b1 e1) "(#Hobj1 & Hdead & _ & Hcells_dead)".
    iDestruct (alloc_obj_agree with "Hobj Hobj1") as %[<- <-].
    (* Take the registers back from the register file. *)
    iDestruct (big_sepM_insert with "Hregs") as "[Hcgp Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hcra Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca0 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hca1 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hct0 Hregs]";
      first (simplify_map_eq; apply Hrmap_none; set_solver).
    iDestruct (big_sepM_insert with "Hregs") as "[Hcnull Hrmap]";
      first (apply Hrmap_none; set_solver).
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".

    (* Block 3: unpaint the revoked payload *)
    focus_block 3 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_unpaint Ha_unpaint
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_paint_spec ShadowQuarantined ShadowLive ctp ca2 E RX Global
      pc_b pc_e a_unpaint b e sb se emp (λ a, addr_alloc a Unclaimed)
      with "[- $HPC $Hctp $Hca2 $Hcode $Hcells_dead]");
      [done|solve_addr|done|solve_addr|subst sb se; solve_addr|subst sb se; solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sb. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_unclaimed. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hcells & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    change_pc_to (pc_a ^+ allocator_free_tail_block_offset 4)%a.
    iApply "Hφ". iFrame "∗ Hq Hcode_main".
  Qed.

  Lemma allocator_free_return_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e pc_a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 4)%a ∗
    cra ↦ᵣ wret ∗
    codefrag_pers pc_a allocator_free_tail_code ∗
    trap_ok E φ ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       codefrag_pers pc_a allocator_free_tail_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow).
    iIntros "(HPC & Hcra & #Hcode_main & Hfailed & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".

    (* Block 4: jump to the return *)
    focus_block 4 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_jmp Ha_jmp
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Jmp .free_return. *)
    iInstr "Hcode".
    { transitivity (Some (pc_a ^+ allocator_free_tail_block_offset 6)%a);
        offsets_compute; solve_addr. }
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 6: return *)
    focus_block 6 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_return_spec with "[- $HPC $Hcra $Hcode]"); [solve_addr|done|].
    iFrame "Hfailed".
    iNext. iIntros "(HPC & Hcra & _ & Hlc)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

  (** Blocks 5 and 6: set [ALLOC_INVALID] and return. *)
  Lemma allocator_free_tail_invalid_spec
    (E : coPset) (pc_b pc_e pc_a : Addr) (wret wreq wca1 : LWord)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_segment_bounds allocator_free_tail_code pc_b pc_e pc_a ->
    PC ↦ₚ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_tail_block_offset 5)%a ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ wreq ∗
    ca1 ↦ᵣ wca1 ∗
    codefrag_pers pc_a allocator_free_tail_code ∗
    trap_ok E φ ∗
    ▷ (PC ↦ₚ lupdatePcPerm wret ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_INVALID ∗
       ca1 ↦ᵣ WInt 0 ∗
       codefrag_pers pc_a allocator_free_tail_code ∗
       £ 1
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow).
    iIntros "(HPC & Hcra & Hca0 & Hca1 & #Hcode_main & Hfailed & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_tail_unfold_code "Hcode_main".

    (* Block 5: set ALLOC_INVALID *)
    focus_block 5 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_invalid Ha_invalid
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    (* Mov ca0 ALLOC_INVALID. *)
    iInstr "Hcode".
    (* Mov ca1 0. *)
    iInstr "Hcode".
    destruct (decide (ca0 = cnull)) as [|_]; first done.
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    (* Block 6: return *)
    focus_block 6 "Hcode_main" of allocator_free_tail_blocks at pc_a as a_ret Ha_ret
      "Hcode" "Hcont".
    iHide "Hcode_main" as hcode.
    iApply (allocator_return_spec with "[- $HPC $Hcra $Hcode]"); [solve_addr|done|].
    iFrame "Hfailed".
    iNext. iIntros "(HPC & Hcra & _ & Hlc)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    iApply "Hφ". iFrame "∗ Hcode_main".
  Qed.

End AllocatorFreeTailBlocks.
