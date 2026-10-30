From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_base switcher_base_ktk.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states.
From griotte Require Import case_study_spec_helpers.

(** * Segment (a): blocks 0-4

    Initialize [p], fetch the allocator capability, the switcher and the
    malloc entry, revoke the stack, and call malloc. *)

Section HTS_Spec_Malloc.
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

  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (cstk : CSTK).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C).
  #[local] Notation hts_static := (hts_static_mem pc_b pc_a cgp_b C_f owner_a).
  #[local] Notation malloc_ret := (hts_malloc_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).

  Lemma hts_spec_malloc (rmap : LReg) :
    cstk.(cstk_frames) = [] ->
    is_shadow_address owner_a = false ->
    withinBounds owner_a (owner_a ^+ 1) owner_a = true ->
    is_heap_address owner_a = false ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + 1 + SpillSlot_size + 2 * StackEntry_reserved_space <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp ; cra ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code) ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    hts_ctx ∗
    na_own (tpool th) ⊤ ∗
    PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ[th] Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e) ∗
    cra ↦ᵣ[th] thread_return_sentry ∗
    regs[th] rmap ∗
    hts_static ∗
    allocator_owner_id hts_main_owner_id ∅ ∗
    world_interp W_init_C C ∗
    interp W_init_C C (Cap RWL Local csp_b csp_e (stk_start_a csp_b csp_e)) ∗
    interp_continuation cstk Ws Cs ∗
    ◯(CSTK)[th] cstk ∗
    (malloc_ret -∗
     safe[th])
    ⊢ safe[th].
  Proof.
    iIntros (Hframes Howner_shadow Howner_bounds Howner_nonheap Hpc_shadow Hpc_nonheap
      Hcgp_shadow Hcgp_heap Hcgp_contiguous Hstk_shadow Hstk_heap Hstk_min Hrmap_dom HsubBounds
      Himports_contiguous)
      "(#Hctx & Hna & HPC & Hcgp & Hcsp & Hcra & Hrmap & Hstatic & Howner & Hworld
       & #Hinterp_csp & HK & Hcstk & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hservice_static & #Hswitcher & #Hswitcher_static
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hstatic" as "(Himports & Hcode_main & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    codefrag_facts "Hcode_main". clear H0.
    unfold_code hts_main_code "Hcode_main".
    (* Block 0: initialize p and malloc size. *)
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0 0. *)
    iInstr "Hcode".
    { eapply disjoint_from_shadow_not_in; [exact Hcgp_shadow|rewrite /withinBounds; solve_addr]. }
    { apply withinBounds_true_iff; solve_addr. }
    iExtractList "Hrmap" [ca1] as ["Hca1"].
    (* Mov ca1 1. *)
    iInstr "Hcode".
    iEval (cbn) in "Hca1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 1: fetch the allocator capability for malloc. *)
    focus_block (hts_block ".Lhts_fetch_alloc_cap_malloc") "Hcode_main" of hts_main_blocks at pc_a as a_fetch1 Ha_fetch1 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ca0] as ["Hca0"].
    iApply (fetch_spec 5 _ ca0 RX Global
      pc_b pc_e a_fetch1 (allocator_capability Global owner_a)
      _ _ _ with "[- $HPC $Hca0 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply sealed_cap_nonheap. exact Howner_nonheap. }
    { done. }
    iFrame "Himport_alloc_cap".
    iNext; iIntros "(HPC & Hca0 & _ & Himport_alloc_cap)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 2: fetch the switcher for malloc. *)
    focus_block (hts_block ".Lhts_fetch_switcher_malloc") "Hcode_main" of hts_main_blocks at pc_a as a_fetch2 Ha_fetch2 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["Hctp"].
    iApply (fetch_spec 0 _ ctp RX Global
      pc_b pc_e a_fetch2
      switcher_entry_call
      _ _ _ with "[- $HPC $Hctp $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    replace (pc_b ^+ 0) with pc_b by solve_addr.
    iFrame "Himport_switcher".
    iNext; iIntros "(HPC & Hctp & _ & Himport_switcher)".
    iEval (cbn) in "Hctp".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 3: fetch the malloc entry. *)
    focus_block (hts_block ".Lhts_fetch_malloc") "Hcode_main" of hts_main_blocks at pc_a as a_fetch3 Ha_fetch3 "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["Hct1"].
    iApply (fetch_spec 3 _ ct1 RX Global
      pc_b pc_e a_fetch3
      (WSealed ot_switcher (allocator_malloc Global))
      _ _ _ with "[- $HPC $Hct1 $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { unfold allocator_malloc. apply sealed_cap_nonheap.
      exact hts_export_tbl_not_heap. }
    { done. }
    iFrame "Himport_malloc".
    iNext; iIntros "(HPC & Hct1 & _ & Himport_malloc)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".

    (* Block 4: save the return address of the thread and call malloc. *)
    focus_block (hts_block ".Lhts_call_malloc") "Hcode_main" of hts_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [cs0] as ["Hcs0"].
    (* Mov cs0 cra *)
    iInstr "Hcode".
    (* Jalr cra ctp. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert (a_call ^+ 2 = (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a) as Ha_ret
      by (offsets_compute; solve_addr).
    rewrite Ha_ret.
    clear Ha_fetch1 Ha_fetch2 Ha_fetch3.

    (* Revoke the stack before sharing it with the callee. *)
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld]")
      as (l) "(_ & Hworld & #Hstack_revoked & >%Hstack_revoked & >[%stk_mem Hstk] & _)".

    destruct (decide (ca0 = cnull)) as [Hnull|Hnonnull]; first done.
    iEval (cbn) in "Hca0".
    assert (is_Some (rmap !! cs1)) as [wcs1 Hwcs1].
    { apply elem_of_dom. rewrite Hrmap_dom. set_solver. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5;ct0] as ["Hca2";"Hca3";"Hca4";"Hca5";"Hct0"].
    iExtractList "Hrmap" [cs1] as ["Hcs1"].
    iInsertList "Hrmap" [ctp].
    set (rmap_arg := ({[ ca0 := lword_of_word (allocator_capability Global owner_a);
      ca1 := lword_of_word (WInt 1); ca2 := wca2;
      ca3 := wca3; ca4 := wca4; ca5 := wca5; ct0 := wct0 ]} : LReg)).
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    set (rmap_other :=
      <[ctp:=lword_of_word switcher_entry_call]>
       (delete cs1 (delete ct0 (delete ca5 (delete ca4 (delete ca3
         (delete ca2 (delete cs0 (delete ct1
           (delete ca0 (delete ca1 rmap))))))))))).
    (* The buffer avoids the identifiers of the heap keys of the world, so
       that its key is fresh. *)
    iPoseProof (allocator_malloc_switcher_spec (heap_ids (dom (std W_init_C)))
      Global owner_a hts_main_owner_id ∅ 1
      (Cap RW Global cgp_b cgp_e cgp_b)
      (Sentry (ret_kind mie) RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a)
      thread_return_sentry wcs1 csp_b csp_e (stk_start_a csp_b csp_e) rmap_arg cstk
      with "[$Hservice $Hservice_static]") as "Hmalloc_fun".
    { lia. }
    { exact Howner_shadow. }
    { exact Howner_bounds. }
    { subst rmap_arg. reflexivity. }
    { subst rmap_arg. reflexivity. }
    assert (dom rmap_other =
      all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8))
      as Hdom_other.
    { subst rmap_other.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_dom /dom_arg_rmap /=.
      set_solver+. }
    assert (is_arg_rmap rmap_arg 8) as Hargs_rmap.
    { subst rmap_arg. by rewrite /is_arg_rmap /dom_arg_rmap /=. }
    pose proof allocator_size_exports as Hsize.
    rewrite /allocator_export_table_entries in Hsize.
    (* The free part of the stack, below the space reserved at its top *)
    iDestruct (stk_start_region_split with "Hstk") as (stk_mem_free stk_res) "[Hstk _]";
      first (unfold SpillSlot_size, StackEntry_reserved_space in Hstk_min |- *;
             solve_addr+Hstk_min).
    iApply (switcher_cc_specification_known_to_known_end_to_end
      (Cap RW Global cgp_b cgp_e cgp_b)
      (Sentry (ret_kind mie) RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a)
      thread_return_sentry wcs1 csp_b csp_e (stk_start_a csp_b csp_e) stk_mem_free rmap_arg
      rmap_other cstk
      allocator_malloc_nargs allocator_malloc_min_stack ⊤
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_malloc_pcc_off _ false
      with "[- $Hswitcher $Hswitcher_static $Hexport_pcc $Hexport_cgp $Hexport_malloc
         $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
         $Hstk $Hcstk $Hmalloc_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { apply stk_start_cursor_ok.
      unfold SpillSlot_size, StackEntry_reserved_space in Hstk_min |- *; solve_addr+Hstk_min. }
    { apply hts_export_tbl_not_shadow.
      rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { exact hts_export_tbl_disjoint_from_shadow. }
    { exact hts_allocator_pcc_not_heap. }
    { exact hts_allocator_cgp_not_heap. }
    { solve_ndisj. }
    { solve_ndisj. }
    { rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { solve_addr. }
    { rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { rewrite /allocator_malloc_nargs; lia. }
    { exists allocator_code_b.
      rewrite /allocator_malloc_pcc_off -allocator_imports_length.
      exact allocator_size_imports. }
    { apply stk_start_callee_fits.
      rewrite /allocator_malloc_min_stack.
      unfold SpillSlot_size, StackEntry_reserved_space in Hstk_min |- *; solve_addr+Hstk_min. }
    { exact Hdom_other. }
    { exact Hargs_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iFrame "Howner Howner_word".
    iNext.
    iIntros "[Hcall|Hcall]".
    - iNamed "Hcall".
      destruct Hrestored as (Hgp & Hra & Hs0 & _).
      apply load_heap_nonheap in Hs0; [|exact thread_return_sentry_not_heap].
      apply load_heap_nonheap in Hgp.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=.
           reflexivity. }
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      subst rcgp rcra rcs0.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iEval (rewrite /allocator_malloc_result) in "HQ".
      iDestruct "HQ" as "(Howner_word & [(%Hoom & Howner)|Hok])".
      + (* Allocator failure. *)
        destruct Hoom as [-> ->].
        iLeft. iExists _.
        iExtractList "Hrmap" [ctp;ct0;ct2] as ["[Hctp _]";"[Hct0 _]";"[Hct2 _]"].
        iFrame "Hna HPC Hca0 Hct0 Hcs0 Hcra Hctp Hct2 Hcstk Hcode_main".
        done.
      + iDestruct "Hok" as (ι b e)
          "(%Hbounds & %Hι_fresh & _ & %Hret & #Hobj & Hright & Howner & Hzeroed)".
        rewrite union_empty_l_L.
        destruct Hret as [-> ->].
        assert (e = b ^+ 1) as -> by solve_addr.
        assert ((b + 1)%a = Some (b ^+ 1)) as Hsucc by solve_addr.
        assert (finz.dist b (b ^+ 1) = 1) as Hdist
          by (destruct (proj1 (finz_incr_iff_dist b (b ^+ 1) 1)) as [_ ?]; [solve_addr|done]).
        iEval (rewrite /heap_region_pointsto /region_addrs_zeroes
          (finz_seq_between_singleton b (b ^+ 1) Hsucc) Hdist) in "Hzeroed".
        iDestruct "Hzeroed" as "[Hb _]".
        iRight. iExists ι, b.
        iSplit; first (iPureIntro; rewrite /hts_buffer_bounds; solve_addr).
        iSplit.
        { iPureIntro. rewrite -revoke_dom_eq. by apply heap_ids_fresh. }
        iFrame "∗#".
        iPureIntro. split; [exact Hdom_rmap_ret|exact Hstack_revoked].
    - iNamed "Hcall".
      destruct Hrestored as (_ & Hra & Hs0 & _).
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      apply load_heap_nonheap in Hs0; [|exact thread_return_sentry_not_heap].
      subst rcra rcs0.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iLeft. iExists _.
      iExtractList "Hrmap" [ctp;ct0;ct2] as ["[Hctp _]";"[Hct0 _]";"[Hct2 _]"].
      iFrame "Hna HPC Hca0 Hct0 Hcs0 Hcra Hctp Hct2 Hcstk Hcode_main".
      done.
  Qed.
End HTS_Spec_Malloc.
