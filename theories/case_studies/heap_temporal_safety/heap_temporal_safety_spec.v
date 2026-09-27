From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory world_interp_stack.
From griotte Require Import region_invariants heap_ghost logrel rules.
From griotte Require Import proofmode register_tactics map_simpl.

Section Heap_Temporal_Safety_Main.
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

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  (* TODO: move to world_ghost_theory.v. *)
  Lemma hts_world_heap_allocate_empty W b e :
    heap_std W = ∅ ->
    (b < e)%a ->
    world_interp W C
    ==∗
    world_interp (heap_std_update W (heap_allocate ∅ b e)) C.
  Proof.
    intros Hempty Hbe.
    assert (heap_fresh (∅ : Heap) b e) as Hfresh.
    { split; first apply lookup_empty. split; first done.
      intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
    pose proof (heap_allocate_wf ∅ b e heap_wf_empty Hfresh) as Hwf.
    assert (related_sts_pub_world W
      (heap_std_update W (heap_allocate ∅ b e))) as Hrelated.
    { apply related_sts_pub_world_heap_update. rewrite Hempty.
      apply heap_allocate_future. exact Hfresh. }
    rewrite world_interp_eq /world_interp_def.
    iIntros "(Hr & Hsts & Hseal)".
    iDestruct "Hsts" as "(Hstd & Hloc & Hseals & Hheap & _)".
    iEval (rewrite Hempty) in "Hheap".
    iMod (heap_std_auth_allocate _ _ b e Hfresh with "Hheap")
      as "[Hheap #Hfull]".
    iModIntro.
    iSplitL "Hr".
    { rewrite region_eq /region_def /region_map_def.
      iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdomρ & _ & Hr)".
      iExists M, Mρ. iFrame "HM".
      iSplit; first done. iSplit; first done.
      iSplit.
      { iPureIntro. intros a Ha.
        rewrite /heap_addr_status /heap_std_update /= in Ha.
        destruct (is_heap_address a); last discriminate.
        destruct (heap_lookup_addr (heap_allocate ∅ b e) a)
          as [ [base obj] | ] eqn:Hlookup; last discriminate.
        apply heap_lookup_addr_sound in Hlookup as [Hentry _].
        rewrite /heap_allocate lookup_insert_Some in Hentry.
        destruct Hentry as [ [-> <-] | [_ Hbad] ]; first discriminate.
        rewrite lookup_empty in Hbad. discriminate. }
      iApply (big_sepM_mono with "Hr").
      iIntros (a γ Hsome) "Hm".
      iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
      iExists ρ. iFrame. iSplitR; first done.
      iDestruct "Hm" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iExists γpred, p, φ. iFrame "%#".
      destruct (is_heap_address a) eqn:Ha.
      { iEval (rewrite Hempty /heap_lookup_addr map_to_list_empty /=)
          in "Hl". done. }
      destruct ρ; cbn [region_std_interp]; last done.
      - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
        iFrame "%#∗". iNext.
        destruct (isWL p); [| destruct (isDL p)].
        + iApply ("HmonoV" with "[] [] Hφ"); done.
        + iApply ("HmonoV" with "[] [] Hφ"); done.
        + iApply ("HmonoV" with "[] [] Hφ"); last done.
          iPureIntro. by apply related_sts_pub_priv_world.
      - iDestruct "Hl" as (v Hne) "(Hl & #HmonoV & Hφ)".
        iExists v. iFrame "Hl HmonoV". iSplit; first done.
        iNext. iApply ("HmonoV" with "[] [] Hφ"); last done.
        iPureIntro. by apply related_sts_pub_priv_world. }
    iSplitL "Hstd Hloc Hseals Hheap".
    { rewrite /sts_full_world /heap_std_update /=. iFrame "∗#". }
    iApply (sealing_map_monotone_pub with "Hseal"); done.
  Qed.

  (* TODO: move to world_ghost_theory.v. *)
  Lemma hts_world_empty_heap_fresh W a :
    is_heap_address a = true ->
    heap_std W = ∅ ->
    world_interp W C -∗ ⌜a ∉ dom (std W)⌝.
  Proof.
    iIntros (Ha Hempty) "Hworld".
    rewrite world_interp_eq /world_interp_def
      region_eq /region_def /region_map_def.
    iDestruct "Hworld" as
      "((%M & %Mρ & HM & %Hdom & _ & _ & Hr) & _)".
    iIntros (Hin).
    assert (is_Some (M !! a)) as [γ Hγ].
    { apply elem_of_dom. rewrite -Hdom. exact Hin. }
    iDestruct (big_sepM_lookup with "Hr") as "Hm"; first exact Hγ.
    iDestruct "Hm" as (ρ Hρ) "[Hstate Hm]".
    iDestruct "Hm" as (γpred p φ Heq Hpers) "[Hsaved Hl]".
    iEval (rewrite Ha Hempty /heap_lookup_addr map_to_list_empty /=)
      in "Hl".
    done.
  Qed.

  Lemma hts_main_spec

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

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* Block map for hts_main_asm:
       0: initialize p and malloc size.
       1: fetch switcher for malloc.
       2: fetch malloc entry.
       3: call malloc.
       4: validate malloc result.
       5: save and initialize buffer.
       6: fetch switcher for first adversary call.
       7: fetch adversary entry.
       8: call adversary with buffer.
       9: reload saved buffer.
      10: check reloaded buffer tag.
      11: store private p capability in buffer.
      12: fetch switcher for free.
      13: fetch free entry.
      14: call free.
      15: validate free result.
      16: clear adversary argument.
      17: fetch switcher for second adversary call.
      18: fetch adversary entry.
      19: call adversary with zero.
      20: prepare p assertion.
      21: fetch and call assert service.
      22: halt. *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap Hcra_heap Hcs1_heap Hcs0_heap
      HNswitcher_assert HNswitcher_service HNassert_service Hrmap_dom
      Hrmap_init HsubBounds Hcgp_contiguous Himports_contiguous Hp_fresh
      Hsaved_fresh Hheap_empty Hframe_match)
      "(#Hassert & #Halloc & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free & Hna
       & HPC & Hcgp & Hcsp & Hrmap & Himports & Hcode & Hdata
       & Hworld & HK & Hcstk & #Hadv & #Hentry & #Hinterp_csp)".
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

    (* Block 6: fetch switcher for first adversary call. *)
    focus_block 6 "Hcode" as a_fetch6 Ha_fetch6 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp;ct2] as
      ["[Hctp %Hwctp]";"[Hct2 %Hwct2]"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch6
      (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ _ with "[- $HPC $Hctp $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_switcher_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_switcher_offset)%a with pc_b
      by (rewrite /hts_switcher_offset; solve_addr).
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct2 & Hfetch & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 7: fetch adversary entry. *)
    focus_block 7 "Hcode" as a_fetch7 Ha_fetch7 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["[Hct1 %Hwct1]"].
    iApply (fetch_spec hts_adv_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch7 (WSealed ot_switcher C_f)
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_adv_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { exact Hadv_nonheap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_adv_offset)%a with (pc_b ^+ 2)%a by reflexivity.
    iFrame "Himport_adv".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_adv)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 8: call adversary with buffer. *)
    focus_block 8 "Hcode" as a_advcall Ha_advcall "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    (* Jalr cra ctp. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    assert (is_heap_address b = true) as Hb_heap.
    { apply withinBounds_true_iff. clear -Hbounds. solve_addr. }
    assert (heap_std (revoke W_init_C) = ∅) as Hheap_revoke.
    { rewrite revoke_heap. exact Hheap_empty. }
    iDestruct (hts_world_empty_heap_fresh (revoke W_init_C) b
      Hb_heap Hheap_revoke with "Hworld") as %Hb_fresh.
    iMod (hts_world_heap_allocate_empty (revoke W_init_C) b (b ^+ 1)%a
      with "Hworld") as "Hworld".
    { exact Hheap_revoke. }
    { exact (proj1 (proj2 (proj1 Hbounds))). }

    set (Wbuf := heap_std_update (revoke W_init_C)
      (heap_allocate ∅ b (b ^+ 1)%a)).
    iDestruct (init_PermRes Wbuf C b RW interp_in_memC (WInt 0)
      with "[] Hb []") as "Hbuf_perm".
    { done. }
    { iApply future_priv_mono_interp_in_mem_z. }
    { iApply interp_int. }
    iMod (world_interp_extend_perm Wbuf C b (WInt 0) RW interp_in_memC
      with "Hworld Hbuf_perm") as "(Hworld & #Hrel_b)".
    { rewrite /heap_addr_live /heap_addr_status Hb_heap /Wbuf
        /heap_std_update /=.
      assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
      { split; first apply lookup_empty. split; first solve_addr.
        intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
      pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty Hfresh_buf)
        as Hwf_buf.
      rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
        b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
      { reflexivity. }
      { rewrite /heap_allocate lookup_insert.
        case_decide; [reflexivity|congruence]. }
      { unfold alloc_object_contains; cbn.
        split; [solve_addr|exact (proj1 (proj2 (proj1 Hbounds)))]. } }
    { subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }

    set (Wshare := <s[b := Permanent]s> Wbuf).
    iAssert (interp Wshare C (hts_buffer b)) as "#Hinterp_buf".
    { iEval (rewrite /hts_buffer fixpoint_interp1_eq /=).
      iSplit.
      { rewrite (finz_seq_between_cons b); last solve_addr.
        rewrite (finz_seq_between_empty _ (b ^+ 1)%a); last solve_addr.
        iApply big_sepL_singleton.
        iExists RW, (interp_in_mem RWL). iEval (cbn).
        iSplit; first done. iSplit.
        { iPureIntro; intros WCv; tc_solve. }
        iSplit; first iFrame "Hrel_b".
        iSplit; first iApply zcond_interp_in_mem.
        iSplit; first iApply rcond_interp_in_mem.
        iSplit; first iApply wcond_interp_in_mem.
        iSplit; first iApply monoReq_interp_in_mem.
        - subst Wshare; cbn; simplify_map_eq; reflexivity.
        - by intro.
        - iPureIntro. subst Wshare; cbn; simplify_map_eq; reflexivity. }
      iPureIntro. split.
      { rewrite /disjoint_from_shadow elem_of_disjoint.
        intros a Ha Hsh.
        pose proof heap_shadow_disjoint as Hdisj.
        rewrite elem_of_disjoint in Hdisj.
        eapply Hdisj; last exact Hsh.
        apply elem_of_finz_seq_between.
        apply elem_of_finz_seq_between in Ha. solve_addr. }
      intros _. rewrite /heap_cap_live Hb_heap.
      rewrite /Wshare /Wbuf /heap_std_update /=.
      assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
      { split; first apply lookup_empty. split; first solve_addr.
        intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
      pose proof (heap_allocate_wf ∅ b (b ^+ 1)%a heap_wf_empty Hfresh_buf)
        as Hwf_buf.
      rewrite (heap_lookup_addr_complete (heap_allocate ∅ b (b ^+ 1)%a)
        b b (MkAllocObject b (b ^+ 1)%a AllocObjectLive) Hwf_buf).
      { cbn. repeat split; try reflexivity; solve_addr. }
      { rewrite /heap_allocate lookup_insert.
        case_decide; [reflexivity|congruence]. }
      { unfold alloc_object_contains; cbn.
        split; [solve_addr|exact (proj1 (proj2 (proj1 Hbounds)))]. } }

    assert (heap_fresh (∅ : Heap) b (b ^+ 1)%a) as Hfresh_buf.
    { split; first apply lookup_empty. split; first solve_addr.
      intros c o a Hc. rewrite lookup_empty in Hc. discriminate. }
    assert (related_sts_priv_world W_init_C Wshare) as Hrelated_init_share.
    { eapply related_sts_priv_pub_trans_world.
      - apply revoke_related_sts_priv_world.
      - eapply related_sts_pub_trans_world.
        + subst Wbuf. apply related_sts_pub_world_heap_update.
          rewrite revoke_heap Hheap_empty. apply heap_allocate_future.
          exact Hfresh_buf.
        + subst Wshare. apply related_sts_pub_world_fresh.
          subst Wbuf. rewrite /heap_std_update /=. exact Hb_fresh. }
    assert (heap_wf (heap_std Wshare)) as Hwf_share.
    { subst Wshare Wbuf. rewrite /heap_std_update /=.
      apply heap_allocate_wf; [apply heap_wf_empty|exact Hfresh_buf]. }
    assert (heap_authority_base (WSealed ot_switcher C_f) = None)
      as Hsealed_base.
    { destruct (heap_authority_base (WSealed ot_switcher C_f))
        as [base|] eqn:Hbase; last done.
      apply heap_authority_base_heap_cap_base in Hbase.
      rewrite /is_heap_cap Hbase in Hadv_nonheap. discriminate. }
    iAssert (interp Wshare C (WSealed ot_switcher C_f))
      as "#Hinterp_adv_share".
    { destruct (get_tag (WSealed ot_switcher C_f)) eqn:Htag;
        last by iApply interp_untagged.
      iApply (interp_monotone_sd_retained W_init_C Wshare C
        ot_switcher C_f with "Hadv");
        [exact Hwf_share|exact Hrelated_init_share|exact Htag|].
      apply filter_heap_nonheap. exact Hsealed_base. }
    iDestruct (StackRevokedResources_mono_priv W_init_C Wshare C
      stk_frame_addrs Hrelated_init_share with "Hstack_revoked_W0")
      as "Hstack_revoked_share".
    assert (b ∉ stk_frame_addrs) as Hb_not_stack.
    { rewrite /disjoint_from_heap elem_of_disjoint in Hstk_heap.
      intros Hb_stk. eapply (Hstk_heap b Hb_stk).
      apply elem_of_finz_seq_between.
      apply withinBounds_true_iff in Hb_heap. exact Hb_heap. }
    assert (revoked_addresses Wshare stk_frame_addrs)
      as Hstack_revoked_share.
    { rewrite /revoked_addresses Forall_forall. intros a Ha.
      subst Wshare Wbuf. rewrite lookup_insert_ne.
      - cbn. rewrite /revoked_addresses Forall_forall in Hstack_revoked_W0.
        apply Hstack_revoked_W0. exact Ha.
      - intros ->. exact (Hb_not_stack Ha). }

    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["Hca2";"Hca3";"Hca4";"Hca5"].
    iDestruct "Hca2" as "[Hca2 %Hca2]".
    iDestruct "Hca3" as "[Hca3 %Hca3]".
    iDestruct "Hca4" as "[Hca4 %Hca4]".
    iDestruct "Hca5" as "[Hca5 %Hca5]".
    subst wca6 wca7 wca8 wca9.
    set (adv_arg := ({[ca0 := hts_buffer b; ca1 := WInt 0;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ adv_arg,
      rarg ↦ᵣ warg ∗ if decide (rarg ∈ dom_arg_rmap 1)
        then interp Wshare C warg else True)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hadv_arg".
    { subst adv_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct2].
    set (adv_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap_ret)))))))).
    iApply (switcher_cc_specification Nswitcher Wshare C
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_advcall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b C_f
      (region_addrs_zeroes csp_b csp_e)
      adv_arg adv_other cstk Ws Cs 1
      with "[- $Halloc $Hswitcher $Hna $HPC $Hcgp $Hcra $Hcsp
        $Hct1 $Hentry $Hcs0 $Hcs1 $Hadv_arg $Hrmap $Hstk
        $Hworld $Hstack_revoked_share $Hcstk $HK $Hinterp_adv_share]").
    { exact Hstk_shadow. }
    { exact Hstk_heap. }
    { subst adv_other. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_ret /dom_arg_rmap /=. set_solver+. }
    { subst adv_arg. rewrite /is_arg_rmap /dom_arg_rmap /=. reflexivity. }
    iFrame "%".
    iNext.
    (* First unknown-call return: the switcher gives a public future Wret and
       revokes its temporaries. Keep Hp and Hsaved outside the call frame;
       the adversary may quarantine b, so Hrel_b alone cannot supply Hb. *)
    iIntros (Wret rmap_after stk_after lret rcgp rcra rcs0 rcs1)
      "(%Hlret_unk & Hrevoked_lret & %Hrevoked_lret
       & %Hrelated_share_ext_ret & Hrel_stk_ret & %Hdom_rmap_after
       & Hstack_revoked_ret & %Hstack_revoked_ret
       & Hna & %Hcsp_bounds_ret & Hworld & Hcstk
       & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
       & [%warg0 [Hca0 _]] & [%warg1 [Hca1 _]]
       & Hrmap & Hstk & HK & %Hrestored)".
    destruct Hrestored as (Hgp_ret & Hra_ret & Hs0_ret & Hs1_ret).
    apply load_heap_nonheap in Hgp_ret.
    2: { destruct Hcgp_heap as [Hcgp_nonheap _].
         rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hcgp_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hra_ret.
    2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
           Hpc_nonheap /=. reflexivity. }
    apply load_heap_nonheap in Hs0_ret; [|exact Hcs0_nonheap].
    apply load_heap_nonheap in Hs1_ret; [|exact Hcs1_nonheap].
    subst rcgp rcra rcs0 rcs1.
    iEval (cbn) in "HPC".

    (* Block 9: hts_reload_buffer_spec loads Hsaved into ca0. Challenge:
       its load_heap result can clear the tag; retain Hsaved and Hp privately. *)
    (* Block 10: use Wret's heap status and load_heap to split live from
       quarantined. Apply hts_check_quarantined_buffer_spec to the untagged
       path and hts_check_live_buffer_spec to the tagged path. *)
    (* Live-buffer transition: extract b's physical points-to from the
       revoked heap-world resources (world_interp_revoke_partition / live
       open-world lemmas), preserving the rest of world_interp for the call. *)
    (* Block 11: hts_store_private_spec writes the narrowed &p to live b.
       Challenge: it requires b ↦ₐ w, and the world interpretation must be
       reclosed around the new word before the next cross-compartment call. *)
    (* Block 12: fetch_spec hts_switcher_offset, as in block 6. Challenge:
       extract ct0, ct2, ctp from the zeroed return-register map. *)
    (* Block 13: fetch_spec hts_free_offset obtains the sealed free entry.
       Challenge: reestablish its nonheap fact and retain Hexport_free. *)
    (* Block 14: iInstr for Jalr, then the known-to-known switcher contract
       with allocator_free_valid_correct. Challenge: build the free-function
       wrapper and supply the one-word allocation receipt and b ↦ₐ word;
       keep Hp and Hsaved outside the call frame. *)
    (* Block 15: hts_free_result_success_spec for both zero words;
       hts_free_result_failure_spec halts on either nonzero word. Challenge:
       handle the switcher's stack-exhaustion result as a failure too. *)
    (* Free-world transition: use allocator_reclaimed and heap_quarantine
       to update the world from live b to quarantined b, including its
       relation/reclaim token. Keep the dangling saved alias private. *)
    (* Block 16: iInstr for Mov ca0 0. Challenge: reassemble the zeroed
       argument map so the dangling buffer is never passed again. *)
    (* Block 17: fetch_spec hts_switcher_offset, as in block 6. Challenge:
       preserve the post-free heap world and private CGP cells. *)
    (* Block 18: fetch_spec hts_adv_offset, as in block 7. Challenge:
       transport the sealed adversary interpretation to the current world. *)
    (* Block 19: iInstr for Jalr, then switcher_cc_specification with
       ca0 = WInt 0. Challenge: prove all arguments safe to share and keep
       p/Hsaved private while closing the stack and world conditions. *)
    (* Block 20: hts_assert_prep_spec reloads p and sets ct1 to zero.
       Challenge: recover Hp after the second unknown call and preserve its
       value through both world transitions. *)
    (* Block 21: assert_success_spec for the fetched assert service.
       Challenge: split its import cell and provide ct2, ct3, ct4, cra,
       cnull plus the private zero cell p ↦ₐ WInt 0. *)
    (* Block 22: iInstr for Halt, then wp_end; return Hna. Challenge:
       ensure assertion spec has restored na_own cerise_nais ⊤. *)
  Abort.
End Heap_Temporal_Safety_Main.
