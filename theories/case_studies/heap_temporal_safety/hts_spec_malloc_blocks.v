From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region.
From griotte Require Import world_interp_stack region_invariants heap_ghost.
From griotte Require Import proofmode register_tactics map_simpl.
From griotte Require Import hts_spec_states.

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

  Local Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  Context (C : CmptName).
  Context (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr).
  Context (C_f : Sealable) (owner_a : Addr) (W_init_C : WORLD).
  Context (Ws : list WORLD) (Cs : list CmptName).
  Context (Nassert Nswitcher : namespace) (cstk : CSTK).

  Local Notation hts_ctx := (hts_main_ctx C C_f W_init_C Nassert Nswitcher).
  Local Notation hts_static := (hts_static_mem pc_b pc_a cgp_b C_f owner_a).
  Local Notation malloc_ret := (hts_malloc_ret C pc_b pc_e pc_a cgp_b cgp_e
    csp_b csp_e C_f owner_a W_init_C Ws Cs cstk).

  Lemma hts_spec_malloc (rmap : LReg) :
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
    dom rmap = all_registers_s ∖ {[ PC ; cgp ; csp]} ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    hts_ctx ∗
    na_own cerise_nais ⊤ ∗
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
    cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
    csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    hts_static ∗
    allocator_owner_id hts_main_owner_id ∅ ∗
    world_interp W_init_C C ∗
    interp W_init_C C (WCap true RWL Local csp_b csp_e csp_b) ∗
    interp_continuation cstk Ws Cs ∗
    cstack_frag cstk ∗
    (malloc_ret -∗
     WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Howner_shadow Howner_bounds Howner_nonheap Hpc_shadow Hpc_nonheap
      Hcgp_shadow Hcgp_heap Hcgp_contiguous Hstk_shadow Hstk_heap Hrmap_dom HsubBounds)
      "(#Hctx & Hna & HPC & Hcgp & Hcsp & Hrmap & Hstatic & Howner & Hworld
       & #Hinterp_csp & HK & Hcstk & Hcontinue)".
    iDestruct "Hctx" as "(#Hassert & #Hservice & #Hswitcher
       & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
       & #Hadv & #Hentry)".
    iDestruct "Hstatic" as "(Himports & Hcode & Hp & Howner_word)".
    iDestruct "Himports" as
      "(Himport_switcher & Himport_assert & Himport_adv & Himport_malloc
       & Himport_free & Himport_alloc_cap)".
    codefrag_facts "Hcode". clear H0.
    iEval (rewrite /hts_main_code) in "Hcode".
    (* Block 0: initialize p and malloc size. *)
    focus_block_0 "Hcode" as "Hblock" "Hcont"; iHide "Hcont" as hcont.
    (* Store cgp 0 0. *)
    iInstr "Hblock".
    iExtractList "Hrmap" [ca1] as ["Hca1"].
    (* Mov ca1 1. *)
    iInstr "Hblock".
    iEval (cbn) in "Hca1".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".

    (* Block 1: fetch the allocator capability for malloc. *)
    focus_block 1 "Hcode" as a_fetch1 Ha_fetch1 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ca0;ct0;ct2] as ["Hca0";"Hct0";"Hct2"].
    iApply (fetch_spec hts_alloc_cap_offset ca0 ct0 ct2 RX Global
      pc_b pc_e a_fetch1 (allocator_capability Global owner_a)
      _ _ _ _ with "[- $HPC $Hca0 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_alloc_cap_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { apply sealed_cap_nonheap. exact Howner_nonheap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_alloc_cap_offset)%a with (pc_b ^+ 5)%a by reflexivity.
    iFrame "Himport_alloc_cap".
    iNext; iIntros "(HPC & Hca0 & Hct0 & Hct2 & Hfetch & Himport_alloc_cap)".
    iEval (cbn) in "Hca0".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 2: fetch the switcher for malloc. *)
    focus_block 2 "Hcode" as a_fetch2 Ha_fetch2 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["Hctp"].
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch2
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

    (* Block 3: fetch the malloc entry. *)
    focus_block 3 "Hcode" as a_fetch3 Ha_fetch3 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1] as ["Hct1"].
    iApply (fetch_spec hts_malloc_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch3
      (WSealed ot_switcher (allocator_malloc Global))
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { solve_addr. }
    { rewrite /hts_malloc_offset. apply withinBounds_true_iff. solve_addr. }
    { exact Hpc_shadow. }
    { unfold allocator_malloc. apply sealed_cap_nonheap.
      exact hts_export_tbl_not_heap. }
    { done. }
    { done. }
    { done. }
    replace (pc_b ^+ hts_malloc_offset)%a with (pc_b ^+ 3)%a by reflexivity.
    iFrame "Himport_malloc".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_malloc)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".

    (* Block 4: call malloc. *)
    focus_block 4 "Hcode" as a_call Ha_call "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [cra] as ["Hcra"].
    (* Jalr cra ctp. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    assert (hts_block_addr pc_a 5 (a_call ^+ 1)%a) as Ha_ret.
    { rewrite /hts_block_addr. solve_addr. }
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
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as ["Hca2";"Hca3";"Hca4";"Hca5"].
    iExtractList "Hrmap" [cs0] as ["Hcs0"].
    iExtractList "Hrmap" [cs1] as ["Hcs1"].
    iInsertList "Hrmap" [ctp;ct2].
    set (rmap_arg := ({[ ca0 := lword_of_word (allocator_capability Global owner_a);
      ca1 := lword_of_word (WInt 1); ca2 := wca2;
      ca3 := wca3; ca4 := wca4; ca5 := wca5; ct0 := lword_of_word (WInt 0) ]} : LReg)).
    iAssert ([∗ map] rarg↦warg ∈ rmap_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hrmap_arg".
    { subst rmap_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]).
      done. }
    set (rmap_other := <[ct2:=lword_of_word (WInt 0)]>
      (<[ctp:=lword_of_word (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call)]>
       (delete cs1 (delete cs0 (delete ca5 (delete ca4 (delete ca3
         (delete ca2 (delete cra (delete ct1
           (delete ct0 (delete ca0 (delete ca1 rmap))))))))))))).
    iPoseProof (hts_malloc_known_function
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_call ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b rmap_arg cstk
      Global owner_a hts_main_owner_id ∅
      with "Hservice") as "Hmalloc_fun".
    { exact Howner_shadow. }
    { exact Howner_bounds. }
    { subst rmap_arg. reflexivity. }
    { subst rmap_arg. reflexivity. }
    pose proof allocator_size_exports as Hsize.
    rewrite /allocator_export_table_entries in Hsize.
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_call ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b stk_mem rmap_arg rmap_other cstk
      allocator_malloc_nargs ⊤ allocator_exp_tblN
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_malloc_pcc_off
      with "[- $Hswitcher $Hexport_pcc $Hexport_cgp $Hexport_malloc
         $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1 $Hrmap_arg $Hrmap
         $Hstk $Hcstk $Hmalloc_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { apply hts_export_tbl_not_shadow.
      rewrite /allocator_malloc_exp_tbl_off. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { apply hts_export_tbl_not_shadow. solve_addr. }
    { exact hts_allocator_pcc_not_heap. }
    { exact hts_allocator_cgp_not_heap. }
    { solve_ndisj. }
    { rewrite /allocator_malloc_exp_tbl_off. solve_addr. }
    { solve_addr. }
    { rewrite /allocator_malloc_exp_tbl_off. solve_addr. }
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
    iFrame "Howner Howner_word".
    iNext.
    iIntros "[Hcall|Hcall]".
    - iDestruct "Hcall" as
        (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret rmap_ret Hdom_rmap_ret)
        "(Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
          & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & Hmalloc_post)".
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
      iExists (a_call ^+ 1)%a.
      iSplit; first done.
      iEval (rewrite /hts_malloc_result) in "Hmalloc_post".
      iDestruct "Hmalloc_post" as "(Howner_word & [(%Hoom & Howner)|Hok])".
      + (* Allocator failure. *)
        destruct Hoom as [-> ->].
        iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode".
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
    - iDestruct "Hcall" as
        (rmap_exhaust stk_mem_exhaust rcgp rcra rcs0 rcs1 Hdom_rmap_exhaust)
        "(Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1 & Hca0 & Hca1
          & Hrmap & Hstk & Hcstk & %Hrestored & _)".
      destruct Hrestored as (_ & Hra & _ & _).
      apply load_heap_nonheap in Hra.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hpc_nonheap /=.
           reflexivity. }
      subst rcra.
      iEval (cbn) in "HPC".
      iApply "Hcontinue".
      iExists (a_call ^+ 1)%a.
      iSplit; first done.
      iLeft. iExists _. iFrame "Hna HPC Hca0 Hcode".
      iExtractList "Hrmap" [ct0] as ["[Hct0 _]"].
      by iExists _.
  Qed.
End HTS_Spec_Malloc.
