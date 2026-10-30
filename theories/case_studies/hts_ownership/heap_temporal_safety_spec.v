From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel.
From griotte Require Import assert_spec switcher_base.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte Require Import world_interp_stack.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states hts_spec_malloc_blocks_1 hts_spec_share_blocks_2 hts_spec_free_blocks_3 hts_spec_dangling_blocks_4 hts_spec_assert_blocks_5.

Section Heap_Temporal_Safety_Main.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .

  #[local] Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The call stack of a thread that starts in this compartment, with the
      stack [b, e) and the export table word [w] *)
  #[local] Notation main_entry_cstack b e w :=
    (entry_cstack {| tf_csp := Cap RWL Local b e (stk_start_a b e);
                     tf_export_tbl := w;
                     tf_error_count := 0 |}) (only parsing).

  Lemma hts_main_spec

    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (csp_b csp_e : Addr)
    (rmap : LReg)

    (C_f : Sealable)
    (owner_a : Addr)

    (W_init_C : WORLD)

    (Ws : list WORLD)
    (Cs : list CmptName)
    (* The capability to the export table of the compartment, as the entry
       frame of the thread records it *)
    (w_main_tbl : LWord)

    :
    let a_alloc_exp_tbl_cgp := (allocator_exp_tbl_b ^+ ExportTable_offset_cgp) in
    let a_alloc_entry_malloc := (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off) in
    let a_alloc_entry_free := (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off) in

    let imports := hts_main_imports owner_a C_f in

    is_shadow_address owner_a = false ->
    withinBounds owner_a (owner_a ^+ 1) owner_a = true ->
    is_heap_address owner_a = false ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    is_heap_cap (WSealed ot_switcher C_f) = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->

    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    (forall r, r ∈ (dom rmap) -> is_Some (rmap !! r) ) ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code) ->

    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    (* The stack holds the saved buffer and the spill of the switcher calls *)
    (csp_b + 1 + SpillSlot_size + 2 * StackEntry_reserved_space <= csp_e)%Z ->

    LNonHeap (cgp_b)%a ∉ dom (std W_init_C) ->

    frame_match Ws Cs (main_entry_cstack csp_b csp_e w_main_tbl) W_init_C C ->
    (
      assert_static b_assert e_assert a_flag
      ∗ allocator_service_ctx ∗ allocator_service_static
      ∗ thread_in th C
      ∗ na_inv (tpool th) Ntstack trusted_stack_inv ∗ switcher_static
      ∗ allocator_exp_tbl_b ↦ₐ□ Cap RX Global
          allocator_pcc_b allocator_pcc_e allocator_pcc_b
      ∗ a_alloc_exp_tbl_cgp ↦ₐ□ Cap RW Global
          allocator_cgp_b allocator_cgp_e allocator_cgp_b
      ∗ a_alloc_entry_malloc ↦ₐ□
          WInt (encode_entry_point InterruptEnabled allocator_malloc_nargs allocator_malloc_min_stack
            allocator_malloc_pcc_off)
      ∗ a_alloc_entry_free ↦ₐ□
          WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
            allocator_free_pcc_off)
      ∗ na_own (tpool th) ⊤

      (* initial register file *)
      ∗ PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a
      ∗ cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b
      ∗ csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)
      ∗ cra ↦ᵣ[th] thread_return_sentry
      ∗ regs[th] rmap
      (* initial memory layout *)
      ∗ [[ pc_b , pc_a ]] ↦ₐ□ [[ lword_of_word <$> imports ]]
      ∗ codefrag_pers pc_a hts_main_code
      ∗ [[ cgp_b , cgp_e ]] ↦ₐ [[ lword_of_word <$> hts_main_data ]]
      (* owner of the imported allocator capability *)
      ∗ allocator_owner_id hts_main_owner_id ∅
      ∗ owner_a ↦ₐ WInt hts_main_owner_id

      ∗ world_interp W_init_C C

      ∗ interp_continuation (main_entry_cstack csp_b csp_e w_main_tbl) Ws Cs

      ∗ ◯(CSTK)[th] (main_entry_cstack csp_b csp_e w_main_tbl)

      ∗ interp W_init_C C (WSealed ot_switcher C_f)
      ∗ C_f ↦ₑ□{nargs} 1
      ∗ interp W_init_C C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e))

      ⊢ safe[th])%I.
  Proof.
    (* The proof follows the control flow of [hts_main_asm]; each segment
       ends at a switcher call or at the return:
       (a) blocks 0-4: initialization and call to malloc
           ([hts_spec_malloc], returning [hts_malloc_ret]);
       (b) blocks 5-9: malloc result check, saving the buffer, sharing it
           and first adversary call ([hts_spec_share], [hts_adv1_ret]);
       (c) blocks 10-15: reload, store of [&p] and call to free
           ([hts_spec_free], [hts_free_ret]);
       (d) blocks 16-20: free result check, quarantine and second
           adversary call ([hts_spec_dangling], [hts_adv2_ret]);
       (e) blocks 21-23: assertion and return ([hts_spec_assert]). *)
    intros a_alloc_exp_tbl_cgp a_alloc_entry_malloc a_alloc_entry_free imports.
    subst a_alloc_exp_tbl_cgp a_alloc_entry_malloc a_alloc_entry_free imports.
    set (cstk0 := main_entry_cstack csp_b csp_e w_main_tbl).
    iIntros (Howner_shadow Howner_bounds Howner_nonheap
      Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous
      Himports_contiguous Hstk_min Hp_fresh Hframe_match)
      "(#Hassert & #Hservice & #Hservice_static & #Hthread & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free & Hna
       & HPC & Hcgp & Hcsp & Hcra & Hrmap & Himports & Hcode & Hdata
       & Howner & Howner_word & Hworld & HK & Hcstk & #Hadv & #Hentry
       & #Hinterp_csp)".
    iDestruct (interp_cap_disjoint_wl with "Hinterp_csp")
      as %[Hstk_shadow Hstk_heap]; first done.
    iDestruct (hts_main_imports_pointsto_pers pc_b pc_a owner_a C_f Himports_contiguous
      with "Himports") as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap & _)".
    iDestruct (hts_private_data_initial cgp_b cgp_e Hcgp_contiguous
      with "Hdata") as "Hp".
    iAssert (hts_main_ctx C C_f W_init_C) as "#Hctx".
    { iFrame "#". }
    (* (a) *)
    iApply (hts_spec_malloc C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f owner_a W_init_C Ws Cs cstk0 rmap
      with "[$Hctx $Hna $HPC $Hcgp $Hcsp $Hcra $Hrmap $Howner $Hworld
        $Hinterp_csp $HK $Hcstk $Himport_switcher $Himport_assert
        $Himport_adv $Himport_malloc $Himport_free $Himport_alloc_cap
        $Hcode $Hp $Howner_word]"); try done.
    iIntros "Hmalloc_ret".
    (* (b) *)
    iApply (hts_spec_share C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f owner_a W_init_C Ws Cs cstk0
      with "[$Hthread $Hctx $Hmalloc_ret]"); try done.
    iIntros "Hadv1_ret".
    (* (c) *)
    iApply (hts_spec_free C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f owner_a W_init_C Ws Cs cstk0
      with "[$Hctx $Hadv1_ret]"); try done.
    iIntros "Hfree_ret".
    (* (d) *)
    iApply (hts_spec_dangling C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f owner_a W_init_C Ws Cs cstk0
      with "[$Hthread $Hctx $Hfree_ret]"); try done.
    iIntros "Hadv2_ret".
    (* (e) *)
    iApply (hts_spec_assert C pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f owner_a W_init_C cstk0
      with "[$Hctx $Hadv2_ret]"); done.
  Qed.
End Heap_Temporal_Safety_Main.
