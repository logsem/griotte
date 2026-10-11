From iris.proofmode Require Import proofmode.
From griotte Require Import rules proofmode.
From griotte.allocators.ownership Require Import allocator_free_spec_states.

(** * Free, blocks 7-9: the revocation of the payload

    Block 7 fetches the revoker capability from the imports. Block 8 stores
    to the revoker: the sweep kills [ι], whose payload is quarantined. It
    reads the whole register file, which must hold no word with authority
    over [ι]. The shadow cursor is then rewound to the payload base. Block 9
    unpaints the revoked payload, whose cells are now unclaimed. *)

Section AllocatorFreeRevokeBlocks5.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ}
    {MP : MachineParameters} {layout : allocatorLayout} {layout_wf : allocatorLayoutWf}.

  (** Block 8: the revoker store, over the whole register file [regs]. *)
  Lemma allocator_free_revoke_store_spec
    (E : coPset) (pc_b pc_e pc_a b e sb se : Addr) (ι : AId) (regs : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (se + (b - e))%a = Some sb ->
    dom regs = all_registers_s ∖ {[PC; ct1; ct2; ct3; ct4; ctp; ca2]} ->
    (∀ x lv, x ≠ cnull -> regs !! x = Some lv ->
       has_authority lv.(lw) -> lv.(lprov) ≠ Some ι) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 8)%a ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ allocator_revoker_cap ∗
    ct4 ↦ᵣ WInt 0 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e se ∗
    ca2 ↦ᵣ WInt 0 ∗
    ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
    revoke_pre ι ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 9)%a ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ct3 ↦ᵣ allocator_revoker_cap ∗
       ct4 ↦ᵣ WInt (b - e) ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e sb ∗
       ca2 ↦ᵣ WInt (e - b) ∗
       ([∗ map] r↦w ∈ regs, r ↦ᵣ w) ∗
       revoke_post ι ∗
       codefrag pc_a allocator_free_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros (Hpc & Hpc_shadow & _) Hsb Hdom Hclean.
    iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hpre & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof allocator_revoker_size as Hrev.
    assert (Hnone : ∀ r, r ∈ ({[PC; ct1; ct2; ct3; ct4; ctp; ca2]} : gset RegName) ->
      regs !! r = None).
    { intros r Hr. apply not_elem_of_dom. rewrite Hdom. set_solver. }

    (* Block 8: the revoker store, and the rewind of the shadow cursor *)
    focus_block 8 "Hcode_main" of allocator_free_blocks at pc_a as a_revoke Ha_revoke
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
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
    iApply (wp_store_revoker _ RX Global pc_b pc_e a_revoke None
              (a_revoke ^+ 1)%a _ _ ct3 (inl 0%Z) 0 RW Global
              revoker_addr (revoker_addr ^+ 1)%a revoker_addr {[ι]}
      with "[$Hi $Hregs Hpre]").
    { cbn. apply decode_encode_instrW_inv. }
    { solve_pure. }
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
    { solve_addr. }
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
    (* Sub ct4 ct1 ct2. *)
    iInstr "Hcode".
    (* Lea ctp ct4. *)
    iInstr "Hcode".
    (* Sub ca2 ct2 ct1. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_block_offset 9)%a.
    iApply "Hφ". iFrame.
  Qed.

  Lemma allocator_free_revoke_spec
    (E : coPset) (pc_b pc_e pc_a next b e : Addr) (ι : AId)
    (w3 w4 wa2 wret wnull : LWord) (rmap : LReg)
    (φ : language.val griotte_lang → iPropI Σ) :
    allocator_free_code_bounds pc_b pc_e pc_a ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    dom rmap = all_registers_s ∖
      {[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4; ctp; cnull]} ->
    (∀ r w, rmap !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None) ->
    (has_authority wret.(lw) -> wret.(lprov) = None) ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 7)%a ∗
    cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    cra ↦ᵣ wret ∗
    ca0 ↦ᵣ WInt ALLOC_OK ∗
    ca1 ↦ᵣ WInt 0 ∗
    ca2 ↦ᵣ wa2 ∗
    ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
    ct1 ↦ᵣ WInt b ∗
    ct2 ↦ᵣ WInt e ∗
    ct3 ↦ᵣ w3 ∗
    ct4 ↦ᵣ w4 ∗
    ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
    cnull ↦ᵣ wnull ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    (pc_b ^+ allocator_revoker_import_off)%a ↦ₐ allocator_revoker_cap ∗
    alloc_obj ι b e ∗
    ι ↦st{1} AQuar ∗
    ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowQuarantined ∗ addr_alloc a (Claimed ι)) ∗
    codefrag pc_a allocator_free_code ∗
    ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ allocator_free_block_offset 10)%a ∗
       cgp ↦ᵣ WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
       cra ↦ᵣ wret ∗
       ca0 ↦ᵣ WInt ALLOC_OK ∗
       ca1 ↦ᵣ WInt 0 ∗
       ca2 ↦ᵣ WInt 0 ∗
       ct0 ↦ᵣ WCap true RW Global heap_b heap_e next ∗
       ct1 ↦ᵣ WInt b ∗
       ct2 ↦ᵣ WInt e ∗
       ct3 ↦ᵣ allocator_revoker_cap ∗
       ct4 ↦ᵣ WInt (b - e) ∗
       ctp ↦ᵣ WCap true RW Global shadow_b shadow_e (shadow_b ^+ (e - heap_b))%a ∗
       cnull ↦ᵣ wnull ∗
       ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
       (pc_b ^+ allocator_revoker_import_off)%a ↦ₐ allocator_revoker_cap ∗
       ι ↦st{1} ADead ∗
       ([∗ list] a ∈ finz.seq_between b e, a ↦ₛ ShadowLive ∗ addr_alloc a Unclaimed) ∗
       codefrag pc_a allocator_free_code
       -∗ WP Seq (Instr Executable) @ E {{ φ }})
    ⊢ WP Seq (Instr Executable) @ E {{ φ }}.
  Proof.
    intros Hbounds_code Hbounds Hdom Hclean Hclean_ret.
    pose proof Hbounds_code as (Hpc & Hpc_shadow & _).
    iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp &
      Hcnull & Hrmap & Himport & #Hobj & Hquar & Hpayload & Hcode_main & Hφ)".
    codefrag_facts "Hcode_main".
    allocator_free_unfold_code "Hcode_main".
    pose proof heap_shadow_same_size as Hss.
    pose proof heap_valid.
    set (sb := (shadow_b ^+ (b - heap_b))%a).
    set (se := (shadow_b ^+ (e - heap_b))%a).

    (* Block 7: fetch the revoker capability *)
    focus_block 7 "Hcode_main" of allocator_free_blocks at pc_a as a_fetch Ha_fetch
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_fetch_spec with "[- $HPC $Hct3 $Hct4 $Hca2 $Hcode $Himport]");
      [done|solve_addr| |done|apply allocator_revoker_import_not_heap|done|done|done|].
    { apply withinBounds_true_iff. rewrite /allocator_revoker_import_off. solve_addr. }
    iNext. iIntros "(HPC & Hct3 & Hct4 & Hca2 & Himport & Hcode)".
    iEval (rewrite /lload_word /lift_word /=) in "Hct3".
    iEval (cbn [load_word]) in "Hct3".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_block_offset 8)%a.

    (* Block 8: the revoker store, with the rest of the register file *)
    assert (Hrmap_none : ∀ r, r ∈ ({[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4;
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
      "[- $HPC $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hca2 $Hregs $Hcode_main]").
    { exact Hbounds_code. }
    { subst sb se. solve_addr. }
    { rewrite !dom_insert_L Hdom.
      apply set_eq. intros x. pose proof (all_registers_s_correct x).
      destruct (decide (x ∈ ({[PC; cgp; cra; ca0; ca1; ca2; ct0; ct1; ct2; ct3; ct4; ctp;
                               cnull]} : gset RegName))) as [Hx|Hx]; set_solver. }
    { intros x lv Hx Hlookup Hauth.
      destruct (decide (x = cgp)); [subst; simplify_map_eq; done|].
      destruct (decide (x = cra)); [subst; simplify_map_eq; by rewrite Hclean_ret|].
      destruct (decide (x = ca0)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ca1)); [subst; simplify_map_eq; done|].
      destruct (decide (x = ct0)); [subst; simplify_map_eq; done|].
      rewrite !lookup_insert_ne // in Hlookup.
      by rewrite (Hclean _ _ Hlookup Hauth). }
    iSplitL "Hquar Hpayload"; first (iExists b, e; iFrame "Hobj Hquar Hpayload").
    iNext. iIntros "(HPC & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hca2 & Hregs & Hdead &
      Hcode_main)".
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
    allocator_free_unfold_code "Hcode_main".

    (* Block 9: unpaint the revoked payload *)
    focus_block 9 "Hcode_main" of allocator_free_blocks at pc_a as a_unpaint Ha_unpaint
      "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iApply (allocator_paint_spec ShadowQuarantined ShadowLive ctp ca2 E RX Global
      pc_b pc_e a_unpaint b e sb se emp (λ a, addr_alloc a Unclaimed)
      with "[- $HPC $Hctp $Hca2 $Hcode $Hcells_dead]");
      [done|solve_addr|done|solve_addr|subst sb se; solve_addr|subst sb se; solve_addr| | | |].
    { intros a Ha. rewrite allocator_heap_to_shadow; last solve_addr.
      f_equal. subst sb. solve_addr. }
    { repeat constructor; set_solver. }
    { right. apply allocator_paint_ok_unclaimed. }
    iNext. iIntros "(HPC & Hctp & Hca2 & _ & Hcells & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    change_pc_to (pc_a ^+ allocator_free_block_offset 10)%a.
    iApply "Hφ". iFrame.
  Qed.

End AllocatorFreeRevokeBlocks5.
