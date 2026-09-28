From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region wp_rules_interp hts_blocks_groups_0_5 hts_blocks_groups_6_10
  hts_blocks_groups_11_15 hts_blocks_groups_16_22.
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
    iIntros (Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      Hcra_heap Hcs1_heap Hcs0_heap HNswitcher_assert HNswitcher_service
      HNassert_service Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous
      Himports_contiguous Hp_fresh Hsaved_fresh Hheap_empty Hframe_match)
      "Hinitial".
    iPoseProof (hts_phase_0_5 pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      rmap C_f W_init_C Ws Cs Nassert Nswitcher cstk
      Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      Hcra_heap Hcs1_heap Hcs0_heap HNswitcher_assert HNswitcher_service
      HNassert_service Hrmap_dom Hrmap_init HsubBounds Hcgp_contiguous
      Himports_contiguous Hp_fresh Hsaved_fresh Hheap_empty Hframe_match
      with "Hinitial") as "Hphase".
    iApply "Hphase".
    iIntros "Hphase6".
    iApply (hts_phase_6_10 pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      rmap C_f W_init_C Ws Cs Nassert Nswitcher cstk
      Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      HsubBounds Hcgp_contiguous Hheap_empty with "[$Hphase6]").
    iNext. iIntros "Hphase11".
    iApply (hts_phase_11_15 pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nassert Nswitcher cstk
      Hpc_shadow Hpc_nonheap Hcgp_heap HsubBounds Hcgp_contiguous
      with "[$Hphase11]").
    iNext. iIntros "Hphase16".
    iApply (hts_phase_16_22 pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nassert Nswitcher cstk
      Hpc_shadow Hpc_nonheap Hadv_nonheap Hcgp_shadow Hcgp_heap
      HsubBounds Hcgp_contiguous with "Hphase16").
  Qed.
End Heap_Temporal_Safety_Main.
