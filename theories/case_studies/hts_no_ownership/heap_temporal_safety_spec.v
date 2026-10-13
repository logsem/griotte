From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import assert_spec switcher_spec_call.
From griotte.case_studies.hts_no_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.no_ownership Require Import allocator allocator_preamble.
From griotte Require Import world_interp_stack.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_no_ownership Require Import hts_spec_states hts_spec_malloc_blocks_1 hts_spec_share_blocks_2 hts_spec_free_blocks_3 hts_spec_dangling_blocks_4 hts_spec_assert_blocks_5.

Section Heap_Temporal_Safety_Main.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {FA : FreeAuth Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma hts_main_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (C_f : Sealable)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)

    (Nswitcher : namespace)

    (cstk : CSTK)
    :

    let imports := hts_main_imports C_f in

    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    Nswitcher ## Nallocator_service ->

    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->

    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    (pc_b + length imports)%a = Some pc_a ->

    LNonHeap (cgp_b)%a ∉ dom (std W_init_C) ->
    heap_std W_init_C = ∅ ->

    frame_match Ws Cs cstk W_init_C C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ allocator_service_ctx ∗ allocator_service_static
      ∗ na_inv cerise_nais Nswitcher switcher_inv ∗ switcher_static
      ∗ allocator_exp_tbl_b ↦ₐ□ WCap true RX Global
          allocator_pcc_b allocator_pcc_e allocator_pcc_b
      ∗ (allocator_exp_tbl_b ^+ 1)%a ↦ₐ□ WCap true RW Global
          allocator_cgp_b allocator_cgp_e allocator_cgp_b
      ∗ (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a ↦ₐ□
          WInt (encode_entry_point allocator_malloc_nargs allocator_malloc_pcc_off)
      ∗ (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ□
          WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)
      ∗ na_own cerise_nais ⊤

      (* initial register file *)
      ∗ PC ↦ₚ WCap true RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
      ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a hts_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> hts_main_data ]]

      ∗ world_interp W_init_C C

      ∗ interp_continuation cstk Ws Cs

      ∗ cstack_frag cstk

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ (WSealed ot_switcher C_f) ↦□ₑ 1
      ∗ interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b)

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    (* The proof follows the control flow of [hts_main_asm]; each segment
       ends at a switcher call or at [halt]:
       (a) blocks 0-3: initialization and call to malloc
           ([hts_spec_malloc], returning [hts_malloc_ret]);
       (b) blocks 4-8: malloc result check, saving the buffer, sharing it
           and first adversary call ([hts_spec_share], [hts_adv1_ret]);
       (c) blocks 9-14: reload, tag check, store of [&p] and call to free
           ([hts_spec_free], [hts_free_ret]);
       (d) blocks 15-19: free result check, quarantine and second
           adversary call ([hts_spec_dangling], [hts_adv2_ret]);
       (e) blocks 20-22: assertion and halt ([hts_spec_assert]). *)
    intros imports; subst imports.
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      HNswitcher_service Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous
      Himports_contiguous Hp_fresh Hheap_empty Hframe_match)
      "(#Hassert & #Hservice & #Hservice_static & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free & Hna
       & HPC & Hcgp & Hcsp & Hrmap & Himports & Hcode & Hdata
       & Hworld & HK & Hcstk & #Hadv & #Hentry
       & #Hinterp_csp)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_csp")
      as %[Hstk_shadow Hstk_heap]; first done.
    iDestruct (hts_main_imports_pointsto_pers pc_b pc_a C_f Himports_contiguous
      with "Himports") as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & _)".
    iDestruct (hts_private_data_initial cgp_b cgp_e Hcgp_contiguous
      with "Hdata") as "Hp".
    iAssert (hts_main_ctx C C_f W_init_C Nswitcher) as "#Hctx".
    { iFrame "#". }
    (* (a) *)
    iApply (hts_spec_malloc C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nswitcher cstk rmap
      with "[$Hctx $Hna $HPC $Hcgp $Hcsp $Hrmap $Hworld
        $Hinterp_csp $HK $Hcstk $Himport_switcher $Himport_assert
        $Himport_adv $Himport_malloc $Himport_free
        $Hcode $Hp]"); try done.
    iIntros "Hmalloc_ret".
    (* (b) *)
    iApply (hts_spec_share C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nswitcher cstk
      with "[$Hctx $Hmalloc_ret]"); try done.
    iIntros "Hadv1_ret".
    (* (c) *)
    iApply (hts_spec_free C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nswitcher cstk
      with "[$Hctx $Hadv1_ret]"); try done.
    iIntros "Hfree_ret".
    (* (d) *)
    iApply (hts_spec_dangling C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nswitcher cstk
      with "[$Hctx $Hfree_ret]"); try done.
    iIntros "Hadv2_ret".
    (* (e) *)
    iApply (hts_spec_assert C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Nswitcher cstk
      with "[$Hctx $Hadv2_ret]"); done.
  Qed.
End Heap_Temporal_Safety_Main.
