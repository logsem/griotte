From iris.proofmode Require Import proofmode.
From griotte Require Import rules logrel monotone interp_weakening.
From griotte Require Import fetch_spec assert_spec switcher_spec_call
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec_blocks.
From griotte Require Import switcher_spec_KtK.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte Require Import heap_temporal_safety_allocator_spec world_ghost_theory heap_region wp_rules_interp
  hts_blocks_groups_0_5 hts_blocks_groups_6_10.
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
    `{MP: MachineParameters}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf} {assertlayout : assertLayout}
  .
  Context {C : CmptName}.

  Lemma hts_phase_11_15
    (pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e : Addr)
    (C_f : Sealable) (W_init_C : WORLD)
    (Ws : list WORLD) (Cs : list CmptName)
    (Nassert Nswitcher : namespace) (cstk : CSTK) :
    disjoint_from_shadow pc_b pc_e ->
    is_heap_address pc_b = false ->
    not_heap_range cgp_b cgp_e ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_main_code)%a ->
    (cgp_b + length hts_main_data)%a = Some cgp_e ->
    (hts_phase11_pre (C:=C) pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
      C_f W_init_C Ws Cs Nassert Nswitcher cstk ∗
     ▷ (hts_phase16_pre (C:=C) pc_b pc_e pc_a cgp_b cgp_e csp_b csp_e
       C_f W_init_C Ws Cs Nassert Nswitcher cstk -∗
       WP Seq (Instr Executable)
         {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}))
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hpc_shadow Hpc_nonheap Hcgp_heap HsubBounds Hcgp_contiguous)
      "[Hphase11 Hcontinue]".
    rewrite /hts_phase11_pre.
    iDestruct "Hphase11" as
      (b a_reload a_check Wshare Wret obj_ret wcs0 wcs1 warg1 v_b
        rmap_after stk_after l lret) "Hphase11".
    iDestruct "Hphase11" as
      "(%Hbounds & %Hsucc & %Ha_check & %Hrelated_init_share
        & %Hrelated_share_ext_ret & %Hwf_ret & %Hlookup_rev
        & %Hobj_future & %Hlive_ret & %Hstd_rev & %Hb_heap & Hphase11)".
    iDestruct "Hphase11" as
      "(%Hdom_rmap_after & %Hcs0_nonheap & %Hcs1_nonheap
        & %Hstk_shadow & %Hstk_heap & %Hstack_revoked_W0
        & %Hexport_shadow & %Hstack_revoked_ret & %Hrevoked_lret
        & Hphase11)".
    iDestruct "Hphase11" as
      "(#Hstack_revoked_W0 & Hstack_revoked_ret
        & #Hassert & #Halloc & #Hservice & #Hswitcher
        & #Hexport_pcc & #Hexport_cgp & #Hexport_malloc & #Hexport_free
        & Hphase11)".
    iDestruct "Hphase11" as
      "(#Hadv & #Hinterp_adv_share & #Hentry & #Hinterp_csp
        & HK & Himport_assert & Himport_adv & Himport_free
        & Himports_tail & Hp & Himport_switcher & Himport_malloc
        & Hphase11)".
    iDestruct "Hphase11" as
      "(Hworld_open & Hstate_b & #Hrel_b & Hb_phys
        & Hrevoked_l & Hrevoked_lret & Hna & Hcra & Hcs0 & Hcs1
        & Hcsp & Hstk & Hcstk & Hallocation & Hrmap & Hca1
        & Hcgp & Hsaved & HPC & Hca0 & Hct0 & Hcode)".
    iEval (rewrite /hts_main_code /assembled_hts_main /assembled_hts_main') in "Hcode".
    iEval (cbv [fmap list_fmap concat]) in "Hcode".
    (* Block 11: store the narrowed private-data capability in live b.
       Keep the world entry open and retain physical ownership for free. *)
    focus_block 11 "Hcode" as a_private Ha_private "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ct1;ct2] as
      ["[Hct1 %Hwct1_after]";"[Hct2 %Hwct2_after]"].
    iApply (hts_store_private_spec pc_b pc_e a_private
      cgp_b cgp_e b (b ^+ 1)%a v_b _ _ _ with
      "[- $HPC $Hcgp $Hca0 $Hct0 $Hct1 $Hct2 $Hb_phys $Hblock]").
    { rewrite /disjoint_from_shadow elem_of_disjoint.
      intros a Ha Hsh.
      pose proof heap_shadow_disjoint as Hdisj.
      rewrite elem_of_disjoint in Hdisj.
      eapply Hdisj; last exact Hsh.
      apply elem_of_finz_seq_between.
      apply elem_of_finz_seq_between in Ha.
      clear -Ha Hbounds. solve_addr. }
    { rewrite /hts_main_data in Hcgp_contiguous.
      clear -Hcgp_contiguous. solve_addr. }
    { rewrite /hts_main_data in Hcgp_contiguous.
      clear -Hcgp_contiguous Hbounds. solve_addr. }
    { clear -HsubBounds Ha_private. solve_addr. }
    iNext.
    iIntros "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hb_phys & Hblock)".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    (* Block 12: fetch the switcher entry for free. *)
    focus_block 12 "Hcode" as a_fetch12 Ha_fetch12 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    iExtractList "Hrmap" [ctp] as ["[Hctp %Hwctp_after]"].
    (* Mov ctp PC; GetB ct0 ctp; GetA ct2 ctp; Sub ct0 ct0 ct2;
       Lea ctp ct0; Lea ctp 0; Load ctp ctp 0;
       Mov ct0 0; Mov ct2 0. *)
    iApply (fetch_spec hts_switcher_offset ctp ct0 ct2 RX Global
      pc_b pc_e a_fetch12
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
    (* Block 13: fetch the sealed free entry. *)
    focus_block 13 "Hcode" as a_fetch13 Ha_fetch13 "Hfetch" "Hcont";
      iHide "Hcont" as hcont.
    (* Mov ct1 PC; GetB ct0 ct1; GetA ct2 ct1; Sub ct0 ct0 ct2;
       Lea ct1 ct0; Lea ct1 4; Load ct1 ct1 0;
       Mov ct0 0; Mov ct2 0. *)
    iApply (fetch_spec hts_free_offset ct1 ct0 ct2 RX Global
      pc_b pc_e a_fetch13
      (WSealed ot_switcher (allocator_free Global))
      _ _ _ _ with "[- $HPC $Hct1 $Hct0 $Hct2 $Hfetch]").
    { reflexivity. }
    { exact H0. }
    { rewrite /hts_free_offset; solve_addr. }
    { exact Hpc_shadow. }
    { unfold allocator_free. apply sealed_cap_nonheap.
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
    all: try reflexivity; try discriminate; try assumption.
    replace (pc_b ^+ hts_free_offset)%a with (pc_b ^+ 4)%a by reflexivity.
    iFrame "Himport_free".
    iNext; iIntros "(HPC & Hct1 & Hct0 & Hct2 & Hfetch & Himport_free)".
    iEval (cbn) in "Hct1".
    subst hcont; unfocus_block "Hfetch" "Hcont" as "Hcode".
    (* Block 14: call the trusted free entry while the live world cell is open. *)
    focus_block 14 "Hcode" as a_freecall Ha_freecall "Hblock" "Hcont";
      iHide "Hcont" as hcont.
    clear Ha_check Ha_private Ha_fetch12 Ha_fetch13.
    (* Jalr cra ctp. *)
    iInstr "Hblock".
    subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    iAssert ([[b,(b ^+ 1)%a]] ↦ₐ
      [[ [WCap true RW Global cgp_b (cgp_b ^+ 1)%a cgp_b] ]])%I
      with "[Hb_phys]" as "Hfree_mem".
    { rewrite /region_pointsto
        (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) /=.
      iFrame. }
    iExtractList "Hrmap" [ca2;ca3;ca4;ca5] as
      ["[Hca2 %Hca2]";"[Hca3 %Hca3]";
       "[Hca4 %Hca4]";"[Hca5 %Hca5]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    subst wca2 wca3 wca4 wca5.
    set (free_arg := ({[ca0 := hts_buffer b; ca1 := warg1;
      ca2 := WInt 0; ca3 := WInt 0; ca4 := WInt 0;
      ca5 := WInt 0; ct0 := WInt 0]} : Reg)).
    iAssert ([∗ map] rarg↦warg ∈ free_arg, rarg ↦ᵣ warg)%I
      with "[Hca0 Hca1 Hca2 Hca3 Hca4 Hca5 Hct0]" as "Hfree_arg".
    { subst free_arg.
      repeat (iApply big_sepM_insert; [done|iFrame "∗#"]). done. }
    iInsertList "Hrmap" [ctp;ct2].
    set (free_other := <[ct2:=WInt 0]>
      (<[ctp:=WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call]>
       (delete ca5 (delete ca4 (delete ca3 (delete ca2
         (delete ct1 (delete ct0 rmap_after)))))))).
    iPoseProof (hts_free_known_function
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_freecall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b b (b ^+ 1)%a b
      free_arg cstk RW Global (0%Z,0%Z)
      [WCap true RW Global cgp_b (cgp_b ^+ 1)%a cgp_b]
      with "Hservice") as "Hfree_fun".
    { exact (proj1 Hbounds). }
    { rewrite (finz_seq_between_singleton b (b ^+ 1)%a Hsucc).
      reflexivity. }
    { subst free_arg. reflexivity. }
    iAssert (allocator_allocation b (b ^+ 1)%a (0%Z,0%Z) ∗
      [[b,(b ^+ 1)%a]] ↦ₐ
        [[ [WCap true RW Global cgp_b (cgp_b ^+ 1)%a cgp_b] ]])%I
      with "[$Hallocation $Hfree_mem]" as "Hfree_P".
    iApply (switcher_cc_specification_known_to_known_end_to_end
      Nswitcher
      (WCap true RW Global cgp_b cgp_e cgp_b)
      (WSentry true RX Global pc_b pc_e (a_freecall ^+ 1)%a)
      wcs0 wcs1 csp_b csp_e csp_b stk_after free_arg free_other cstk
      allocator_free_nargs ⊤ hts_allocator_exp_tblN
      allocator_exp_tbl_b
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a
      allocator_exp_tbl_e allocator_pcc_b allocator_pcc_e
      allocator_cgp_b allocator_cgp_e allocator_free_pcc_off
      with "[- $Halloc $Hswitcher $Hexport_pcc $Hexport_cgp $Hexport_free
        $Hna $HPC $Hcgp $Hcra $Hcsp $Hct1 $Hcs0 $Hcs1
        $Hfree_arg $Hrmap $Hstk $Hcstk $Hfree_fun]").
    { exact Hstk_heap. }
    { exact Hstk_shadow. }
    { apply Hexport_shadow. pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off
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
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off
        in Hsize |- *. solve_addr. }
    { pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries in Hsize. solve_addr. }
    { pose proof allocator_size_exports as Hsize.
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off
        in Hsize |- *. solve_addr. }
    { rewrite /allocator_free_nargs; lia. }
    { exists (allocator_code_b ^+ length allocator_malloc_instrs)%a.
      rewrite /allocator_free_pcc_off /allocator_malloc_pcc_off.
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      rewrite /allocator_code length_app in Hcode_size.
      solve_addr. }
    { subst free_other.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hdom_rmap_after /dom_arg_rmap /=. set_solver+. }
    { subst free_arg. rewrite /is_arg_rmap /dom_arg_rmap /=.
      reflexivity. }
    iFrame "Hfree_P".
    iNext.
    iIntros "[Hcall|Hcall]".
    2: {
      iDestruct "Hcall" as
        (free_rmap_exhaust stk_mem_exhaust rcgp rcra rcs0 rcs1
          Hdom_free_rmap_exhaust)
        "(Hna & HPC & Hcgp & Hcra & Hcsp & Hcs0 & Hcs1
          & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & Hfree_P)".
      iEval (cbn) in "HPC".
      destruct Hrestored as (Hgp_free & Hra_free & Hs0_free & Hs1_free).
      apply load_heap_nonheap in Hgp_free.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hcgp_nonheap /=. reflexivity. }
      apply load_heap_nonheap in Hra_free.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hpc_nonheap /=. reflexivity. }
      apply load_heap_nonheap in Hs0_free; [|exact Hcs0_nonheap].
      apply load_heap_nonheap in Hs1_free; [|exact Hcs1_nonheap].
      subst rcgp rcra rcs0 rcs1.
      iEval (cbn) in "HPC".
      (* Block 15: halt on trusted-stack exhaustion. *)
      focus_block 15 "Hcode" as a_free_result Ha_free_result "Hblock" "Hcont";
        iHide "Hcont" as hcont.
      iApply (hts_free_result_failure_spec pc_b pc_e a_free_result
        ENOTENOUGHTRUSTEDSTACK 0 with "[- $HPC $Hca0 $Hca1 $Hblock $Hna]").
      { left. unfold ENOTENOUGHTRUSTEDSTACK. lia. }
      { solve_addr. }
    }
    iDestruct "Hcall" as
        (rcgp rcra rcs0 rcs1 wca0_ret wca1_ret free_rmap_ret
          Hdom_free_rmap_ret)
        "(Hna & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
          & Hca0 & Hca1 & Hrmap & Hstk & Hcstk & %Hrestored & Hfree_post)".
      iEval (cbn) in "HPC".
      destruct Hrestored as (Hgp_free & Hra_free & Hs0_free & Hs1_free).
      apply load_heap_nonheap in Hgp_free.
      2: { destruct Hcgp_heap as [Hcgp_nonheap _].
           rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hcgp_nonheap /=. reflexivity. }
      apply load_heap_nonheap in Hra_free.
      2: { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=
             Hpc_nonheap /=. reflexivity. }
      apply load_heap_nonheap in Hs0_free; [|exact Hcs0_nonheap].
      apply load_heap_nonheap in Hs1_free; [|exact Hcs1_nonheap].
      subst rcgp rcra rcs0 rcs1.
      iEval (cbn) in "HPC".
      iEval (rewrite /hts_free_result) in "Hfree_post".
      iDestruct "Hfree_post" as
        "(Hallocation & Hreclaimed & %Hfree_values)".
      destruct Hfree_values as [-> ->].
      (* Block 15: validate the zero result and allocator status. *)
      focus_block 15 "Hcode" as a_free_result Ha_free_result "Hblock" "Hcont";
        iHide "Hcont" as hcont.
      iApply (hts_free_result_success_spec pc_b pc_e a_free_result
        with "[- $HPC $Hca0 $Hca1 $Hblock]").
      { solve_addr. }
      iNext. iIntros "(HPC & Hca0 & Hca1 & Hblock)".
      subst hcont; unfocus_block "Hblock" "Hcont" as "Hcode".
    (* Free-world transition: quarantine b and relinquish its reclaim token.
       The dangling saved alias remains private. *)
    destruct obj_ret as [base_ret end_ret status_ret].
    unfold alloc_object_future in Hobj_future.
    destruct Hobj_future as (Hbase_ret & Hend_ret & Hstatus_future).
    simpl in Hbase_ret, Hend_ret, Hlive_ret.
    subst base_ret end_ret status_ret.
    pose proof (heap_lookup_addr_sound _ _ _ _ Hlookup_rev)
      as [Hb_lookup Hb_contains].
    assert (heap_wf (heap_std (revoke Wret))) as Hwf_rev.
    { rewrite revoke_heap. exact Hwf_ret. }
    pose proof (hts_heap_quarantine_single_status
      (heap_std (revoke Wret)) b (b ^+ 1)%a Hwf_rev Hsucc Hb_lookup)
      as Hstatus_other.
    assert (b ∈ dom (std (revoke Wret))) as Hb_dom_rev.
    { rewrite elem_of_dom. eexists. exact Hstd_rev. }
    iDestruct (world_interp_open_heap_provenance with "Hworld_open")
      as "[Hworld_open #Hprovenance]".
    iDestruct (heap_provenance_quarantine with "Hprovenance")
      as "#Hprovenance_free".
    iMod (hts_world_open_heap_transition (revoke Wret) C b
      (heap_quarantine (heap_std (revoke Wret)) b)
      with "Hprovenance_free Hworld_open") as "Hworld_open".
    { apply heap_quarantine_future. }
    { apply heap_quarantine_wf. exact Hwf_rev. }
    { exact Hstatus_other. }
    { exact Hb_dom_rev. }
    set (Wfree := heap_std_update (revoke Wret)
      (heap_quarantine (heap_std (revoke Wret)) b)).
    assert (heap_lookup_addr (heap_std Wfree) b =
      Some (b, MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined))
      as Hlookup_free.
    { apply heap_lookup_original_base.
      - rewrite /Wfree /heap_std_update /=.
        apply heap_quarantine_wf. exact Hwf_rev.
      - rewrite /Wfree /heap_std_update /=.
        rewrite (heap_quarantine_lookup Wret.2 b _ Hb_lookup).
        reflexivity. }
    iEval (rewrite /allocator_reclaimed
      (finz_seq_between_singleton b (b ^+ 1)%a Hsucc) /=)
      in "Hreclaimed".
    iDestruct "Hreclaimed" as "[Hreclaimed _]".
    iDestruct (close_world_interp_quarantined_heap Wfree C b RW
      interp_in_memC Permanent b
      (MkAllocObject b (b ^+ 1)%a AllocObjectQuarantined)
      with "Hworld_open Hrel_b Hstate_b Hreclaimed") as "Hworld".
    { exact Hb_heap. }
    { exact Hlookup_free. }
    { reflexivity. }
    iApply "Hcontinue".
    rewrite /hts_phase16_pre.
    iExists b, a_freecall, a_free_result, Wshare, Wret, Wfree,
      wcs0, wcs1, free_rmap_ret, stk_after, l, lret.
    iSplit; first (iPureIntro; exact Hbounds).
    iSplit; first (iPureIntro; exact Hsucc).
    iSplit; first (iPureIntro; change ((pc_a + length
      (concat (take 15 (encodeInstrsW <$> assembled_hts_main))))%a =
      Some a_free_result) in Ha_free_result; exact Ha_free_result).
    iSplit; first (iPureIntro; exact Hrelated_init_share).
    iSplit; first (iPureIntro; exact Hrelated_share_ext_ret).
    iSplit; first (iPureIntro; reflexivity).
    iSplit; first (iPureIntro; exact Hdom_free_rmap_ret).
    iSplit; first (iPureIntro; exact Hcs0_nonheap).
    iSplit; first (iPureIntro; exact Hcs1_nonheap).
    iSplit; first (iPureIntro; exact Hstk_shadow).
    iSplit; first (iPureIntro; exact Hstk_heap).
    iSplit; first (iPureIntro; exact Hstack_revoked_W0).
    iFrame "Hstack_revoked_W0 Hstack_revoked_ret".
    iSplit; first (iPureIntro; exact Hstack_revoked_ret).
    iFrame "∗#".
    assert (a_free_result = (a_freecall ^+ 1)%a) as Hfree_next
      by (clear -Ha_freecall Ha_free_result; solve_addr).
    rewrite Hfree_next.
    iFrame "Hcra".
  Qed.
End Heap_Temporal_Safety_Blocks.
