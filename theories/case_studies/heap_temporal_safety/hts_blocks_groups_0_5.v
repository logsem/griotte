From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region wp_rules_interp.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import region_invariants heap_ghost logrel rules.
From griotte Require Import proofmode register_tactics map_simpl.

Section Heap_Temporal_Safety_Blocks.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {C : CmptName}.

  (* Boundary after executing block 5; the next instruction is block 6. *)
  Definition hts_phase6_pre
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (C_f : Sealable) (W_init_C : WORLD) (Ws : list WORLD)
    (Cs : list CmptName) (Nassert Nswitcher : namespace) (cstk : CSTK)
    (rmap : Reg) : iProp Σ :=
    (∃ (b a_result a_store : Addr) (wcs0 wcs1 : Word)
       (rmap_ret : Reg) (l : list Addr),
      ⌜((heap_b < b)%a ∧ (b < b ^+ 1)%a ∧ (b ^+ 1 <= heap_e)%a) ∧
        ((b ^+ 1)%a - b)%Z = 1%Z⌝ ∗
      ⌜(pc_a + length (concat (take 5 (encodeInstrsW <$> assembled_hts_main))))%a
        = Some a_store⌝ ∗
      ⌜(b + 1)%a = Some (b ^+ 1)%a⌝ ∗
      ⌜dom rmap_ret = all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]}⌝ ∗
      ⌜is_heap_cap wcs0 = false⌝ ∗
      ⌜is_heap_cap wcs1 = false⌝ ∗
      ⌜disjoint_from_shadow csp_b csp_e⌝ ∗
      ⌜disjoint_from_heap csp_b csp_e⌝ ∗
      ⌜Forall (λ a, std (revoke W_init_C) !! a = Some Revoked)
        (finz.seq_between csp_b csp_e)⌝ ∗
      ⌜∀ a, (allocator_exp_tbl_b <= a < allocator_exp_tbl_e)%a →
        is_shadow_address a = false⌝ ∗
      StackRevokedResources W_init_C C (finz.seq_between csp_b csp_e) ∗
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag) ∗
      allocator_ctx ∗ allocator_service_ctx ∗
      na_inv cerise_nais Nswitcher switcher_inv ∗
      inv (export_table_PCCN hts_allocator_exp_tblN)
        (allocator_exp_tbl_b ↦ₐ WCap true RX Global
          allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
      inv (export_table_CGPN hts_allocator_exp_tblN)
        ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
          allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)) ∗
      inv (export_table_entryN hts_allocator_exp_tblN
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
        ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
          WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
      interp W_init_C C (WSealed ot_switcher C_f) ∗
      (WSealed ot_switcher C_f) ↦□ₑ 1 ∗
      interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b) ∗
      interp_continuation cstk Ws Cs ∗
      (pc_b ^+ 1)%a ↦ₐ WSentry true RX Global b_assert e_assert b_assert ∗
      (pc_b ^+ 2)%a ↦ₐ WSealed ot_switcher C_f ∗
      (pc_b ^+ 4)%a ↦ₐ WSealed ot_switcher (allocator_free Global) ∗
      [[(pc_b ^+ 5)%a,pc_a]] ↦ₐ [[ [] ]] ∗
      cgp_b ↦ₐ WInt 0 ∗
      pc_b ↦ₐ WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call ∗
      (pc_b ^+ 3)%a ↦ₐ WSealed ot_switcher (allocator_malloc Global) ∗
      world_interp (revoke W_init_C) C ∗
      RevokedResources W_init_C C l ∗
      na_own cerise_nais ⊤ ∗
      cra ↦ᵣ WSentry true RX Global pc_b pc_e a_result ∗
      cs0 ↦ᵣ wcs0 ∗ cs1 ↦ᵣ wcs1 ∗
      csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
      [[csp_b,csp_e]] ↦ₐ [[region_addrs_zeroes csp_b csp_e]] ∗
      cstack_frag cstk ∗
      allocator_allocation b (b ^+ 1)%a (0%Z, 0%Z) ∗
      ([∗ map] k↦y ∈ delete ct0 rmap_ret, k ↦ᵣ y ∗ ⌜y = WInt 0⌝) ∗
      ca1 ↦ᵣ WInt 0 ∗ ct0 ↦ᵣ WInt 1 ∗
      cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
      (cgp_b ^+ 1)%a ↦ₐ WCap true RW Global b (b ^+ 1)%a b ∗
      PC ↦ᵣ WCap true RX Global pc_b pc_e (a_store ^+ 2)%a ∗
      ca0 ↦ᵣ WCap true RW Global b (b ^+ 1)%a b ∗
      b ↦ₐ WInt 0 ∗
      codefrag pc_a hts_main_code)%I.

  Lemma hts_phase_0_5

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : Reg)

    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nassert Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := hts_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    (* Incoming saved registers are nonheap; the buffer itself is kept in
       the private data slot and explicitly reloaded after the first call. *)
    is_heap_cap (default (WInt 0) (rmap !! cra)) = false ->
    is_heap_cap (default (WInt 0) (rmap !! cs1)) = false ->
    is_heap_cap (default (WInt 0) (rmap !! cs0)) = false ->
    Nswitcher ## Nassert ->
    Nswitcher ## Nallocator_service ->
    Nassert ## Nallocator_service ->

    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->

    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    (cgp_b)%a ∉ dom (std W_init_C) ->
    (cgp_b ^+1 )%a ∉ dom (std W_init_C) ->
    heap_std W_init_C = ∅ ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      na_inv cerise_nais Nassert (assert_inv b_assert e_assert a_flag)
      ∗ allocator_ctx ∗ allocator_service_ctx ∗ na_inv cerise_nais Nswitcher switcher_inv
      ∗ inv (export_table_PCCN hts_allocator_exp_tblN)
          (allocator_exp_tbl_b ↦ₐ WCap true RX Global
            allocator_pcc_b allocator_pcc_e allocator_pcc_b)
      ∗ inv (export_table_CGPN hts_allocator_exp_tblN)
          ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
            allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      ∗ inv (export_table_entryN hts_allocator_exp_tblN
          (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a)
          ((allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ
            WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off))
      ∗ inv (export_table_entryN hts_allocator_exp_tblN
          (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
          ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
            WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off))
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ [[ imports ]]
      ∗ codefrag pc_a hts_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ hts_main_data ]]

      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ (hts_phase6_pre pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
          C_f W_init_C Ws Cs Nassert Nswitcher cstk rmap -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap Hcra_heap Hcs1_heap Hcs0_heap
      HNswitcher_assert HNswitcher_service HNassert_service Hrmap_dom
      Hrmap_init HsubBounds Hcgp_contiguous Himports_contiguous Hp_fresh
      Hsaved_fresh Hheap_empty Hframe_match)
      "(#Hassert & #Halloc & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free & Hna
       & HPC & Hcgp & Hcsp & Hrmap & Himports & Hcode & Hdata
       & Hworld & HK & Hcstk & #Hadv & #Hentry & #Hinterp_csp)".
    iIntros "Hcontinue".
    codefrag_facts "Hcode". clear H0.
    iDestruct (hts_main_imports_pointsto pc_b pc_a C_f Himports_contiguous
      with "Himports") as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himports_tail)".
    iDestruct (hts_private_data_initial cgp_b cgp_e Hcgp_contiguous
      with "Hdata") as "[Hp Hsaved]".
    iEval (rewrite /hts_main_code) in "Hcode".
    (* Block 0: initialize p and malloc size. *)
    focus_block_0 "Hcode" as "Hblock" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0 0. *)
    iInstr "Hblock".
    iExtractList "Hrmap" [ca0] as ["Hca0"].
    (* Mov ca0 1. *)
    iInstr "Hblock".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 1: fetch switcher for malloc. *)
    focus_block 1 "Hcode" as a_fetch1 Ha_fetch1 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct0;ct2] as ["Hctp";"Hct0";"Hct2"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch1
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]");
      eauto using switcher_call_sentry_not_heap.
    { rewrite /hts_switcher_offset; solve_addr. }
    replace (pc_b ^+ hts_switcher_offset)%a with pc_b
      by (rewrite /hts_switcher_offset; solve_addr).
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct2 & Hfetch & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 2: fetch malloc entry. *)
    focus_block 2 "Hcode" as a_fetch2 Ha_fetch2 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["Hct1"].
    iApply (fetch_spec hts_malloc_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch2
      (WSealed ot_switcher (allocator_malloc Global))
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]"); eauto.
    { rewrite /hts_malloc_offset; solve_addr. }
    { unfold allocator_malloc. apply sealed_cap_nonheap.
      apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries in Hsize.
      clear - Hregions Hheap Hsize.
      assert (allocator_exp_tbl_b ∈
        finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e) as Htbl
        by (apply elem_of_finz_seq_between; solve_addr).
      assert (allocator_exp_tbl_b ∈ finz.seq_between heap_b heap_e) as Hhelem
        by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    replace (pc_b ^+ hts_malloc_offset)%a with (pc_b ^+ 3)%a by reflexivity.
    iFrame "Himport_malloc".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_malloc)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 3: call malloc. *)
    focus_block 3 "Hcode" as a_call Ha_call "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [cra] as ["Hcra"].
    (* Jalr cra ctp. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs,
      ⌜std W_init_C !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_csp");
        eauto. }
    iDestruct (interp_cap_disjoint_wl with "Hinterp_csp")
      as %[Hstk_shadow Hstk_heap]; first done.
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld]")
      as (l) "(%Hl_unk & Hworld & #Hstack_revoked_W0
        & >%Hstack_revoked_W0 & >[%stk_mem Hstk] & [Hrevoked_l _])".

    destruct (decide (ca0 = cnull)) as [Hnull|Hnonnull]; first done.
    iEval (cbn) in "Hca0".
    assert (is_Some (rmap !! cs0)) as [wcs0 Hwcs0].
    { apply elem_of_dom. rewrite Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! cs1)) as [wcs1 Hwcs1].
    { apply elem_of_dom. rewrite Hrmap_dom. set_solver. }
    iExtractList "Hrmap" [ca1;ca2;ca3;ca4;ca5;cs0;cs1] as
      ["Hca1";"Hca2";"Hca3";"Hca4";"Hca5";"Hcs0";"Hcs1"].
    iInsertList "Hrmap" [ctp;ct2].
    set (rmap_arg := ({[ ca0 := WInt 1; ca1 := wca1; ca2 := wca2;
      ca3 := wca3; ca4 := wca4; ca5 := wca5; ct0 := WInt 0 ]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    set (rmap_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete cs1 (delete cs0 (delete ca5 (delete ca4 (delete ca3
         (delete ca2 (delete ca1 (delete cra (delete ct1
           (delete ct0 (delete ca0 rmap))))))))))))).
    iPoseProof (hts_malloc_known_function
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_call ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b rmap_arg cstk
      with "Hservice") as "Hmalloc_fun".
    { subst rmap_arg. reflexivity. }
    assert (is_heap_cap wcs0 = false) as Hcs0_nonheap.
    { rewrite Hwcs0 in Hcs0_heap. exact Hcs0_heap. }
    assert (is_heap_cap wcs1 = false) as Hcs1_nonheap.
    { rewrite Hwcs1 in Hcs1_heap. exact Hcs1_heap. }
    assert (forall a, (allocator_exp_tbl_b <= a < allocator_exp_tbl_e)%a ->
      is_shadow_address a = false) as Hexport_shadow.
    { intros a Ha. apply not_true_is_false; intros Hshadow.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hshadow.
      clear - Hregions Ha Hshadow.
      assert (a ∈ finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e)
        as Htbl by (apply elem_of_finz_seq_between; solve_addr).
      assert (a ∈ finz.seq_between shadow_b shadow_e)
        as Hsh by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    assert (forall a, (allocator_exp_tbl_b <= a < allocator_exp_tbl_e)%a ->
      is_heap_address a = false) as Hexport_heap.
    { intros a Ha. apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      clear - Hregions Ha Hheap.
      assert (a ∈ finz.seq_between allocator_exp_tbl_b allocator_exp_tbl_e)
        as Htbl by (apply elem_of_finz_seq_between; solve_addr).
      assert (a ∈ finz.seq_between heap_b heap_e)
        as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_call ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b stk_mem rmap_arg rmap_other cstk
      allocator_malloc_nargs ⊤ hts_allocator_exp_tblN
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_malloc_pcc_off
      with "[- $Halloc $Hswitcher $Hexport_pcc $Hexport_cgp $Hexport_malloc
         $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
         $Hstk $Hcstk $Hmalloc_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { apply Hexport_shadow. pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries /allocator_malloc_exp_tbl_off
        in Hsize |- *. solve_addr. }
    { apply Hexport_shadow. pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries in Hsize. solve_addr. }
    { apply Hexport_shadow. pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries in Hsize. solve_addr. }
    { apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      clear - Hregions Hheap Himports_size Hcode_size.
      assert (allocator_pcc_b ∈
        finz.seq_between allocator_pcc_b allocator_pcc_e)
        as Hpcc by (apply elem_of_finz_seq_between; solve_addr).
      assert (allocator_pcc_b ∈ finz.seq_between heap_b heap_e)
        as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    { apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      pose proof allocator_size_data as Hdata_size.
      clear - Hregions Hheap Hdata_size.
      assert (allocator_cgp_b ∈
        finz.seq_between allocator_cgp_b allocator_cgp_e)
        as Hcgp by (apply elem_of_finz_seq_between; solve_addr).
      assert (allocator_cgp_b ∈ finz.seq_between heap_b heap_e)
        as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    { solve_ndisj. }
    { pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries /allocator_malloc_exp_tbl_off
        in Hsize |- *. solve_addr. }
    { pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries in Hsize. solve_addr. }
    { pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries /allocator_malloc_exp_tbl_off
        in Hsize |- *. solve_addr. }
    { rewrite /allocator_malloc_nargs; lia. }
    { exists allocator_code_b.
      rewrite /allocator_malloc_pcc_off -allocator_imports_length.
      exact allocator_size_imports. }
    { subst rmap_other.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap /=.
      set_solver+. }
    { subst rmap_arg. by rewrite /is_arg_rmap /dom_arg_rmap /=. }
    iNext.
    (* The second branch is trusted-stack exhaustion: ca0 is an integer
       error and ca1 is zero. Block 4's type check must reach Halt. *)
    iIntros "[Hcall|Hcall]".
    - iDestruct "Hcall" as
      (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret rmap_ret Hdom_rmap_ret)
      "(Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
        & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & Hmalloc_post)".
    iEval (cbn) in "HPC".
    destruct Hrestored as (Hgp & Hra & Hs0 & Hs1).
    apply load_heap_nonheap in Hgp.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=.
         reflexivity. }
    apply load_heap_nonheap in Hra.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
         reflexivity. }
    apply load_heap_nonheap in Hs0; [|rewrite Hwcs0 in Hcs0_heap; exact Hcs0_heap].
    apply load_heap_nonheap in Hs1; [|rewrite Hwcs1 in Hcs1_heap; exact Hcs1_heap].
    subst rcgp rcra rcs0 rcs1.
    iEval (cbn) in "HPC".
    iEval (rewrite /hts_malloc_result) in "Hmalloc_post".
    iDestruct "Hmalloc_post" as "[%Hoom|Hok]".
    { destruct Hoom as [-> ->].
      (* Block 4: halt on malloc failure. *)
      focus_block 4 "Hcode" as a_result Ha_result "Hblock" "Hcont";
        iHide "Hcont" as hcont.
      (* Jnz 2 ca1. *)
      iInstr "Hblock".
      (* Halt. *)
      iInstr "Hblock".
      wp_end. iIntros (_). iFrame "Hna". }
    iDestruct "Hok" as (b e) "(%Hbounds & %Hret & Hallocation & Hzeroed)".
    destruct Hret as [-> ->].
    (* Block 4: validate a successful malloc result. *)
    focus_block 4 "Hcode" as a_result Ha_result "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0]"].
    iApply (hts_malloc_result_success_spec pc_b pc_e a_result b e b _
      with "[- $HPC $Hca0 $Hca1 $Hct0 $Hblock]").
    { solve_addr. }
    iNext.
    iIntros "(HPC & Hca0 & Hca1 & Hct0 & Hblock)".
    iEval (cbn) in "HPC".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    assert (e = (b ^+ 1)%a) as He by solve_addr.
    subst e.
    assert ((b + 1)%a = Some (b ^+ 1)%a) as Hsucc by solve_addr.
    iEval (rewrite /allocator_zeroed
      (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) /=) in "Hzeroed".
    iDestruct "Hzeroed" as "[Hb _]".
    (* Block 5: save and initialize buffer. *)
    focus_block 5 "Hcode" as a_store Ha_store "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Store cgp ca0 1. *)
    iInstr_lookup "Hblock" as "Hi" "Hblock".
    wp_instr.
    iApply (wp_store_success_reg_store_word_imm
      ⊤ RX Global pc_b pc_e a_store (a_store ^+ 1)%a _
      cgp ca0 (WInt 0) RW Global cgp_b cgp_e cgp_b
      (cgp_b ^+ 1)%a 1
      (WCap true RW Global b (b ^+ 1)%a b)
      with "[$HPC $Hi $Hca0 $Hcgp $Hsaved]").
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      apply withinBounds_true_iff.
      rewrite /hts_main_data in Hcgp_contiguous.
      solve_addr. }
    { rewrite decode_encode_instrW_inv. reflexivity. }
    { solve_pure. }
    { solve_addr. }
    { reflexivity. }
    { apply withinBounds_true_iff.
      rewrite /hts_main_data in Hcgp_contiguous.
      solve_addr. }
    { solve_addr. }
    { exact Hnonnull. }
    { done. }
    iNext.
    iIntros "(HPC & Hi & Hca0 & Hcgp & Hsaved)".
    iSpecialize ("Hblock" with "Hi").
    wp_pure.
    (* Store ca0 0 0. *)
    iInstr_success "Hblock".
    { apply not_true_is_false; intros Hshadow.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hshadow.
      clear - Hregions Hshadow Hbounds.
      assert (b ∈ finz.seq_between heap_b heap_e) as Hheap
        by (apply elem_of_finz_seq_between; solve_addr).
      assert (b ∈ finz.seq_between shadow_b shadow_e) as Hsh
        by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    { apply withinBounds_true_iff; solve_addr. }
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    iApply "Hcontinue".
    rewrite /hts_phase6_pre.
    iExists b, a_result, a_store, wcs0, wcs1, rmap_ret, l.
    iSplit; first (iPureIntro; exact Hbounds).
    iSplit; first (iPureIntro; change ((pc_a + length
      (concat (take 5 (encodeInstrsW <$> assembled_hts_main))))%a = Some a_store)
      in Ha_store; exact Ha_store).
    iSplit; first (iPureIntro; exact Hsucc).
    iSplit; first (iPureIntro; exact Hdom_rmap_ret).
    iSplit; first (iPureIntro; exact Hcs0_nonheap).
    iSplit; first (iPureIntro; exact Hcs1_nonheap).
    iSplit; first (iPureIntro; exact Hstk_shadow).
    iSplit; first (iPureIntro; exact Hstk_heap).
    iSplit; first (iPureIntro; exact Hstack_revoked_W0).
    iSplit; first (iPureIntro; exact Hexport_shadow).
    iFrame "∗#".
    - iDestruct "Hcall" as
        (rmap_exhaust stk_mem_exhaust rcgp rcra rcs0 rcs1 Hdom_rmap_exhaust)
        "(Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1 & Hca0 & Hca1
          & Hrmap & Hstk & Hcstk & %Hrestored & Hemp)".
      iEval (cbn) in "HPC".
      destruct Hrestored as (Hgp & Hra & Hs0 & Hs1).
      apply load_heap_nonheap in Hgp.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=.
           reflexivity. }
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      apply load_heap_nonheap in Hs0; [|rewrite Hwcs0 in Hcs0_heap; exact Hcs0_heap].
      apply load_heap_nonheap in Hs1; [|rewrite Hwcs1 in Hcs1_heap; exact Hcs1_heap].
      subst rcgp rcra rcs0 rcs1.
      iEval (cbn) in "HPC".
      (* Block 4: halt on trusted-stack exhaustion. *)
      focus_block 4 "Hcode" as a_result Ha_result "Hblock" "Hcont";
        iHide "Hcont" as hcont.
      (* Jnz 2 ca1. *)
      iInstr "Hblock".
      (* Jmp 2. *)
      iInstr "Hblock".
      iExtractList "Hrmap" [ct0] as ["[Hct0 %Hwct0]"].
      (* GetWType ct0 ca0. *)
      iInstr "Hblock".
      (* Sub ct0 ct0 (encodeWordType wt_cap). *)
      iInstr "Hblock".
      iEval (cbn) in "Hct0".
      (* Jnz 2 ct0. *)
      iInstr_success "Hblock".
      { intro Hzero. injection Hzero as Hzero.
        apply (encodeWordType_correct (WInt ENOTENOUGHTRUSTEDSTACK) wt_cap).
        unfold wt_cap in *.
        change ((encodeWordType (WInt ENOTENOUGHTRUSTEDSTACK) -
          encodeWordType (WCap true (O LG LM) Global 0%a 0%a 0%a))%Z = 0%Z)
          in Hzero.
        lia. }
      (* Halt. *)
      iInstr "Hblock".
      wp_end. iIntros (_). iFrame "Hna".
  Qed.

End Heap_Temporal_Safety_Blocks.
