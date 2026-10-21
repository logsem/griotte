From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety heap_temporal_safety_preamble.
From griotte Require Import switcher_spec_KtK switcher_spec_KtK_call switcher_exception_stub.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.case_studies.hts_ownership Require Import heap_temporal_safety_allocator_spec.
From griotte Require Import world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte.case_studies.hts_ownership Require Import hts_spec_states.

(** * Segment (a): blocks 0-4

    Initialize [p], fetch the allocator capability, the switcher and the
    malloc entry, revoke the stack, and call malloc. *)

Section HTS_Spec_Malloc.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
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
  Context (Nswitcher : namespace).

  #[local] Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nswitcher).
  #[local] Notation hts_static := (hts_static_mem pc_b pc_a cgp_b C_f owner_a).
  #[local] Notation malloc_ret := (hts_malloc_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs []).

  Lemma hts_spec_malloc (rmap : LReg) :
    Nswitcher ## N_trap ->
    is_shadow_address owner_a = false ->
    withinBounds owner_a (owner_a ^+ 1)%a owner_a = true ->
    is_heap_address owner_a = false ->
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    disjoint_from_shadow cgp_b cgp_e ->
    not_heap_range cgp_b cgp_e ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    disjoint_from_mmio csp_b csp_e ->
    disjoint_from_heap csp_b csp_e ->
    (csp_b + 5 <= csp_e)%Z ->
    dom rmap = all_registers_s ∖ {[ cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (pc_b + hts_label ".Lhts_main")%a = Some pc_a ->
    hts_ctx ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ₚ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    hts_static ∗
    allocator_owner_id hts_main_owner_id ∅ ∗
    world_interp W_init_C C ∗
    interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b) ∗
    interp_continuation [] Ws Cs ∗
    cstack_frag [] ∗
    (malloc_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (HNtrap Howner_shadow Howner_bounds Howner_nonheap Hpc_shadow Hpc_nonheap
      Hcgp_shadow Hcgp_heap Hcgp_contiguous Hstk_shadow Hstk_heap Hstk_min Hrmap_dom HsubBounds
      Himports_contiguous)
      "(#Hctx & Hna & HPC & Hcgp & Hcsp & Hrmap & Hstatic & Howner & Hworld
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
      (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)
      _ _ _ with "[- $HPC $Hctp $Hcode]").
    { reflexivity. }
    { solve_addr. }
    { offsets_compute; solve_addr. }
    { apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply switcher_call_sentry_not_heap. }
    { done. }
    replace (pc_b ^+ 0)%a with pc_b by solve_addr.
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

    (* Block 4: call malloc. *)
    focus_block (hts_block ".Lhts_call_malloc") "Hcode_main" of hts_main_blocks at pc_a as a_call Ha_call "Hcode" "Hcont".
    iHide "Hcont" as hcont.
    iExtractList "Hrmap" [cra] as ["Hcra"].
    (* Jalr cra ctp. *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode_main".
    assert ((a_call ^+ 1)%a = (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a) as Ha_ret
      by (offsets_compute; solve_addr).
    rewrite Ha_ret.
    clear Ha_fetch1 Ha_fetch2 Ha_fetch3.

    (* Revoke the stack before sharing it with the callee. *)
    iMod (world_interp_revoke_stack with "[$Hinterp_csp $Hworld]")
      as (l) "(_ & Hworld & #Hstack_revoked & >%Hstack_revoked & >[%stk_mem Hstk] & _)".

    destruct (decide (ca0 = cnull)) as [Hnull|Hnonnull]; first done.
    iEval (cbn) in "Hca0".
    assert (is_Some (rmap !! cs0)) as [wcs0 Hwcs0].
    { apply elem_of_dom. rewrite Hrmap_dom. set_solver. }
    assert (is_Some (rmap !! cs1)) as [wcs1 Hwcs1].
    { apply elem_of_dom. rewrite Hrmap_dom. set_solver. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5;ct0] as ["Hca2";"Hca3";"Hca4";"Hca5";"Hct0"].
    iExtractList "Hrmap" [cs0] as ["Hcs0"].
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
      <[ctp:=lword_of_word (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call)]>
       (delete cs1 (delete cs0 (delete ct0 (delete ca5 (delete ca4 (delete ca3
         (delete ca2 (delete cra (delete ct1
           (delete ca0 (delete ca1 rmap)))))))))))).
    iPoseProof (hts_malloc_known_function
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry (ret_kind mie) true RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a)
      wcs0 wcs1 csp_b csp_e csp_b rmap_arg []
      Global owner_a hts_main_owner_id ∅
      with "[$Hservice $Hservice_static]") as "Hmalloc_fun".
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
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry (ret_kind mie) true RX Global pc_b pc_e (pc_a ^+ hts_label_offset ".Lhts_malloc_result")%a)
      wcs0 wcs1 csp_b csp_e csp_b stk_mem rmap_arg rmap_other []
      allocator_malloc_nargs allocator_malloc_min_stack ⊤
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_malloc_pcc_off _ false
      with "[- $Hswitcher $Hswitcher_static $Hexport_pcc $Hexport_cgp $Hexport_malloc
         $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
         $Hstk $Hcstk $Hmalloc_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { solve_addr. }
    { apply hts_export_tbl_not_shadow.
      rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { exact hts_export_tbl_disjoint_from_shadow. }
    { exact hts_allocator_pcc_not_heap. }
    { exact hts_allocator_cgp_not_heap. }
    { solve_ndisj. }
    { solve_ndisj. }
    { exact HNtrap. }
    { rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { solve_addr. }
    { rewrite /allocator_malloc_exp_tbl_off /allocator_entry_malloc. solve_addr. }
    { rewrite /allocator_malloc_nargs; lia. }
    { exists allocator_code_b.
      rewrite /allocator_malloc_pcc_off -allocator_imports_length.
      exact allocator_size_imports. }
    { rewrite /allocator_malloc_min_stack. solve_addr+Hstk_min. }
    { exact Hdom_other. }
    { exact Hargs_rmap. }
    { destruct mie; reflexivity. }
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
      reflexivity. }
    iFrame "Howner Howner_word".
    iNext.
    iIntros "[Hcall|Hcall]".
    - iNamed "Hcall".
      destruct Hrestored as (Hgp & Hra & _ & _).
      apply load_heap_nonheap in Hgp.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hcgp_nonheap /=.
           reflexivity. }
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      subst rcgp rcra.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iEval (rewrite /hts_malloc_result) in "HQ".
      iDestruct "HQ" as "(Howner_word & [(%Hoom & Howner)|Hok])".
      + (* Allocator failure. *)
        destruct Hoom as [-> ->].
        iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode_main".
        iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
        by iExists _.
      + iDestruct "Hok" as (ι b e)
          "(%Hbounds & _ & _ & %Hret & #Hobj & Hright & Howner & Hzeroed)".
        rewrite union_empty_l_L.
        destruct Hret as [-> ->].
        assert (e = (b ^+ 1)%a) as -> by solve_addr.
        assert ((b + 1)%a = Some (b ^+ 1)%a) as Hsucc by solve_addr.
        assert (finz.dist b (b ^+ 1)%a = 1) as Hdist
          by (destruct (proj1 (finz_incr_iff_dist b (b ^+ 1)%a 1)) as [_ ?]; [solve_addr|done]).
        iEval (rewrite /heap_region_pointsto /region_addrs_zeroes
          (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) Hdist) in "Hzeroed".
        iDestruct "Hzeroed" as "[Hb _]".
        iRight. iExists ι, b.
        iSplit; first (iPureIntro; rewrite /hts_buffer_bounds; solve_addr).
        iFrame "∗#".
        iPureIntro. split; [exact Hdom_rmap_ret|exact Hstack_revoked].
    - iNamed "Hcall".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      subst rcra.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode_main".
      iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
      by iExists _.
  Qed.
End HTS_Spec_Malloc.
