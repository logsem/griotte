From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl.
From griotte Require Import world_interp_stack switcher_spec_return.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Import allocator_header_spec.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** Execute malloc for an arbitrary caller and return a safe result. *)
  Lemma malloc_exec_entry_point (W : WORLD) (C : CmptName)
    (Nswitcher : namespace) :
    allocator_ctx ∗ allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_malloc_nargs W C.
  Proof.
    (* Unpack the entry register map and the caller's continuation. *)
    iIntros "(#Halloc & #Hservice & #Hswitcher)".
    iIntros (cstk Ws Cs regs a_stk e_stk)
      "#Halloc' (Hcont & %Hframe & Hregister & Hrmap & Hworld & %Hsync & Hcstk & Hna)".
    rewrite /interp_conf.
    iDestruct "Hregister" as
      "(%Hfull_rmap & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_csp & Hregs)".
    iDestruct "Hregs" as "[#Hargs #Hzeros]".
    rewrite /registers_pointsto.
    cbn in Hfull_rmap.
    getRegValList [PC;cgp;cra;csp;ca0;ca1;ca2;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    iExtractList "Hrmap"
      [PC;cgp;cra;csp;ca0;ca1;ca2;ct0;ct1;ct2;ct3;ct4;ctp;cnull]
      as ["HPCr";"Hcgpr";"Hcrar";"Hcspr";"Hca0";"Hca1";"Hca2";
          "Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    (* Prepare the caller stack and the switcher return state. *)
    rewrite HwPC in HPC. injection HPC as HeqPC. subst wPC.
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
      (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
      "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
    iAssert (world_interp (revoke W) C ∗
      heap_provenance (heap_std (revoke W)))%I with "[Hworld]"
      as "[Hworld #Hprovenance]".
    { rewrite world_interp_eq /world_interp_def region_eq /region_def.
      iDestruct "Hworld" as
        "((%M & %Mρ & HM & %Hdom & %Hdomρ & Hmap) & Hsts & Hseal)".
      rewrite /region_map_def.
      iDestruct "Hmap" as "[%Hcovered [[Hfrags #Hprov] Hentries]]".
      iFrame "Hprov Hsts Hseal".
      iExists M, Mρ. iFrame "HM Hfrags Hentries". iFrame "%". }
    iAssert (□ (∀ next b e allocations,
      ⌜allocator_chain (heap_b ^+ 1)%a next allocations⌝ -∗
      ⌜allocator_header_bounds next heap_e b e⌝ -∗
      allocator_history allocations -∗
      allocator_history allocations ∗
      ⌜heap_fresh (heap_std (revoke W)) b e⌝))%I as "#Hobserver".
    { iModIntro.
      iIntros (next b e allocations) "%Hchain %Hchunk Hhistory".
      iDestruct (allocator_history_heap_fresh (heap_std (revoke W))
        allocations next b e Hchain Hchunk with "Hhistory Hprovenance")
        as %Hfresh.
      iFrame. done. }
    (* Split the requested size into the physical allocator's two cases. *)
    assert (Hsize_dec :
      allocator_positive_size wca0 \/ ~ allocator_positive_size wca0).
    { destruct wca0 as [n|s|tag p g b e a|ot s].
      - destruct (decide (0 < n)%Z) as [Hn|Hn].
        + left. exists n. auto.
        + right. intros (m & Heq & Hm). inversion Heq; lia.
      - right. intros (m & Heq & Hm). discriminate.
      - right. intros (m & Heq & Hm). discriminate.
      - right. intros (m & Heq & Hm). discriminate. }
    destruct Hsize_dec as [Hvalid|Hinvalid].
    2: { (* Reject an invalid size and return ALLOC_INVALID. *)
      iApply (allocator_malloc_invalid_correct ⊤ wca0
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try exact Hinvalid.
      iFrame "Halloc Hservice Hna HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
      iNext.
      iIntros "(Hna & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull)".
      iDestruct "Hstack_mem" as (stk_mem) "Hstk".
      iDestruct "Hca2" as (wca2') "Hca2".
      iDestruct "Hct0" as (wct0') "Hct0".
      iDestruct "Hct1" as (wct1') "Hct1".
      iDestruct "Hct2" as (wct2') "Hct2".
      iDestruct "Hct3" as (wct3') "Hct3".
      iDestruct "Hct4" as (wct4') "Hct4".
      iDestruct "Hctp" as (wctp') "Hctp".
      iInsertList "Hrmap" [cnull;ctp;ct4;ct3;ct2;ct1;ct0;ca2;cra;cgp].
      set (Wfixed := close_list
        (l ++ finz.seq_between (a_stk ^+ 4)%a e_stk) (revoke W)).
      destruct Htemps as [Hnodup Htemps].
      iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld")
        as %Hheap_wf_cur.
      assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed
        by (subst Wfixed; rewrite close_list_heap; exact Hheap_wf_cur).
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      iDestruct (RevokedResources_mono_pub W Wfixed C l l
        Hheap_wf_fixed Hrelated_pub with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_weakening.interp_int. }
      iAssert (interp Wfixed C (WInt ALLOC_INVALID))
        as "#Hinterp_status".
      { iApply interp_weakening.interp_int. }
      iApply (switcher_ret_specification Nswitcher W (revoke W) C _
        e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
        (WInt 0) (WInt ALLOC_INVALID)
        with "[$Halloc $Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply regmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
      { exact Hnodup. }
      { intros a Ha. apply Htemps in Ha. exact Ha. } }
    - (* For a valid size, run the allocation blocks or the out-of-memory block. *)
      destruct Hvalid as (n & -> & Hpositive).
      iApply (allocator_malloc_valid_observe_correct
        (heap_fresh (heap_std (revoke W))) ⊤ n
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try exact Hpositive.
      iFrame "Hobserver Halloc Hservice Hna HPCr Hcgpr Hcrar Hca0".
      iFrame "Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
      iNext.
      iIntros "(Hna & HPCr & Hcgpr & Hcrar & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hresult)".
      iDestruct "Hresult" as "[Hoom|Hsuccess]".
      + (* Capacity exhausted: restore the caller and return ALLOC_NO_MEMORY. *)
        iDestruct "Hoom" as "[Hca0 Hca1]".
        iDestruct "Hstack_mem" as (stk_mem) "Hstk".
        iDestruct "Hca2" as (wca2') "Hca2".
        iDestruct "Hct0" as (wct0') "Hct0".
        iDestruct "Hct1" as (wct1') "Hct1".
        iDestruct "Hct2" as (wct2') "Hct2".
        iDestruct "Hct3" as (wct3') "Hct3".
        iDestruct "Hct4" as (wct4') "Hct4".
        iDestruct "Hctp" as (wctp') "Hctp".
        iInsertList "Hrmap" [cnull;ctp;ct4;ct3;ct2;ct1;ct0;ca2;cra;cgp].
        set (Wfixed := close_list
          (l ++ finz.seq_between (a_stk ^+ 4)%a e_stk) (revoke W)).
        destruct Htemps as [Hnodup Htemps].
        iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld")
          as %Hheap_wf_cur.
        assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed
          by (subst Wfixed; rewrite close_list_heap; exact Hheap_wf_cur).
        assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
        { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
        iDestruct (RevokedResources_mono_pub W Wfixed C l l
          Hheap_wf_fixed Hrelated_pub with "Hrevoked") as "Hrevoked".
        iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
        { iApply interp_weakening.interp_int. }
        iAssert (interp Wfixed C (WInt ALLOC_NO_MEMORY))
          as "#Hinterp_status".
        { iApply interp_weakening.interp_int. }
        iApply (switcher_ret_specification Nswitcher W (revoke W) C _
          e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
          (WInt 0) (WInt ALLOC_NO_MEMORY)
          with "[$Halloc $Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
        { exact Hrelated_pub. }
        { apply regmap_full_dom in Hfull_rmap.
          repeat rewrite dom_insert_L.
          repeat rewrite dom_delete_L.
          rewrite Hfull_rmap. set_solver+. }
        { exact Hframe. }
        { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
        { exact Hnodup. }
        { intros a Ha. apply Htemps in Ha. exact Ha. }
      + (* Allocate the fresh heap object and install its zeroed payload. *)
        iDestruct "Hsuccess" as (b e)
          "(%Hbounds_size & Hca0 & Hca1 & %Hfresh & #Hreceipt & Hzeroed)".
        destruct Hbounds_size as [Hbounds Hsize].
        iDestruct (malloc_heap_unused_range (revoke W) C b e Hfresh
          with "Hworld") as %Hstd_none.
        { destruct Hbounds as (Hb & Hbe & He). split; assumption. }
        iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld")
          as %Hwf_old.
        set (Walloc := heap_std_update (revoke W)
          (heap_allocate (heap_std (revoke W)) b e)).
        assert (heap_wf (heap_std Walloc)) as Hwf_alloc.
        { subst Walloc. apply heap_allocate_wf; assumption. }
        assert (Forall (heap_addr_live (heap_std Walloc))
          (finz.seq_between b e)) as Hlive.
        { apply Forall_forall. intros a Ha.
          apply heap_addr_live_lookup with (b := b)
            (o := MkAllocObject b e AllocObjectLive).
          - apply heap_lookup_addr_complete; first exact Hwf_alloc.
            + subst Walloc. simpl. rewrite /heap_allocate lookup_insert.
              case_decide; [reflexivity|congruence].
            + apply elem_of_finz_seq_between in Ha. exact Ha.
          - reflexivity. }
        assert (Forall (λ a, std Walloc !! a = None)
          (finz.seq_between b e)) as Hstd_none_alloc.
        { apply Forall_forall. intros a Ha.
          apply Forall_forall with (x := a) in Hstd_none; last exact Ha.
          destruct (std Walloc !! a) eqn:Hlook; last reflexivity.
          exfalso. apply Hstd_none.
          apply (proj2 (elem_of_dom (std (revoke W)) a)).
          exists r. exact Hlook. }
        iMod (hts_world_heap_allocate (revoke W) C b e (0%Z, 0%Z)
          Hfresh with "Hreceipt Hworld") as "Hworld".
        set (Wshare := std_update_multiple Walloc
          (finz.seq_between b e) Permanent).
        iMod (world_interp_extend_perm_sepL2 Walloc C
          (finz.seq_between b e)
          (replicate (length (finz.seq_between b e)) (WInt 0))
          RW interp_in_memC with "Hworld [Hzeroed]")
          as "[Hworld #Hrels]".
        1: exact Hlive.
        1: reflexivity.
        1: exact Hstd_none_alloc.
        { rewrite big_sepL2_replicate_r; last reflexivity.
          iEval (rewrite /allocator_zeroed) in "Hzeroed".
          iApply (big_sepL_mono with "Hzeroed").
          iIntros (k y Hy) "Hy".
          iApply (init_PermRes Walloc C y RW interp_in_memC (WInt 0)
            with "[] Hy []").
          { reflexivity. }
          { iApply interp_weakening.future_priv_mono_interp_in_mem_z. }
          iApply interp_weakening.interp_int. }
        (* The returned heap capability is valid for this live object. *)
        assert (is_heap_address b = true) as Hb_heap.
        { apply withinBounds_true_iff.
          destruct Hbounds as (Hb & Hbe & He).
          split; [solve_addr|solve_addr]. }
        assert (heap_lookup_addr (heap_std Wshare) b =
          Some (b, MkAllocObject b e AllocObjectLive)) as Hlookup_b.
        { apply heap_lookup_addr_complete.
          - subst Wshare. rewrite std_update_multiple_heap. exact Hwf_alloc.
          - subst Wshare Walloc. rewrite std_update_multiple_heap. cbn.
            rewrite /heap_allocate lookup_insert.
            case_decide; [reflexivity|congruence].
          - destruct Hbounds as (Hb & Hbe & He).
            unfold alloc_object_contains. cbn. split; solve_addr. }
        assert (heap_cap_valid Wshare RW b e) as Hcap_valid.
        { unfold heap_cap_valid, heap_cap_live.
          destruct Hbounds as (Hb & Hbe & He).
          intros Hbe'. rewrite Hb_heap Hlookup_b. cbn.
          repeat split; try reflexivity; solve_addr. }
        assert (disjoint_from_shadow b e) as Hshadow.
        { unfold disjoint_from_shadow. intros a Ha Hsa.
          apply (heap_shadow_disjoint a); last exact Hsa.
          apply elem_of_finz_seq_between in Ha.
          apply elem_of_finz_seq_between.
          destruct Hbounds as (Hb & Hbe & He). solve_addr. }
        iAssert (interp Wshare C (WCap true RW Global b e b))
          with "[]" as "#Hinterp_result".
        { iEval (rewrite fixpoint_interp1_eq interp1_eq /=).
          iSplit; last (iPureIntro; split; [exact I|split; assumption]).
          iApply big_sepL_intro.
          iIntros (k a Ha).
          iExists RW, (interp_in_mem RWL).
          iModIntro.
          iSplit; first (iPureIntro; reflexivity).
          iSplit; first
            (iPureIntro; apply interp_weakening.persistent_cond_interp_in_mem).
          iSplit.
          { iApply (big_sepL_lookup with "Hrels"); exact Ha. }
          iSplit.
          { iNext. iApply interp_weakening.zcond_interp_in_mem. }
          iSplit.
          { iNext. iApply interp_weakening.rcond_interp_in_mem. }
          iSplit.
          { iNext. iApply interp_weakening.wcond_interp_in_mem. }
          iSplit.
          { iApply interp_weakening.monoReq_interp_in_mem.
            - apply std_sta_update_multiple_lookup_in_i.
              exact (list_elem_of_lookup_2 _ _ _ Ha).
            - intros _. reflexivity. }
          iPureIntro. apply std_sta_update_multiple_lookup_in_i.
          exact (list_elem_of_lookup_2 _ _ _ Ha). }
        (* Close the caller's temporary regions in the extended world. *)
        set (closing := l ++ finz.seq_between (a_stk ^+ 4)%a e_stk).
        set (Wfixed := close_list closing Wshare).
        assert (related_sts_pub_world Wshare Wfixed) as Hshare_fixed.
        { subst Wfixed. apply close_list_related_sts_pub. }
        assert (heap_wf (heap_std Wfixed)) as Hwf_fixed.
        { subst Wfixed Wshare.
          rewrite close_list_heap std_update_multiple_heap.
          exact Hwf_alloc. }
        iAssert (interp Wfixed C (WCap true RW Global b e b))
          with "[]" as "#Hinterp_fixed".
        { iApply (monotone.interp_monotone_cap_valid Wshare Wfixed C
            true RW Global b e b with "[] Hinterp_result").
          - intros _. exact Hcap_valid.
          - iPureIntro. exact Hshare_fixed. }
        destruct Htemps as [Hnodup Htemps].
        assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
        { subst Wfixed Wshare Walloc closing.
          apply malloc_related_pub; assumption. }
        (* Restore the return registers and pass the heap capability to the caller. *)
        iDestruct "Hstack_mem" as (stk_mem) "Hstk".
        iDestruct "Hca2" as (wca2') "Hca2".
        iDestruct "Hct0" as (wct0') "Hct0".
        iDestruct "Hct1" as (wct1') "Hct1".
        iDestruct "Hct2" as (wct2') "Hct2".
        iDestruct "Hct3" as (wct3') "Hct3".
        iDestruct "Hct4" as (wct4') "Hct4".
        iDestruct "Hctp" as (wctp') "Hctp".
        iInsertList "Hrmap" [cnull;ctp;ct4;ct3;ct2;ct1;ct0;ca2;cra;cgp].
        iDestruct (RevokedResources_mono_pub W Wfixed C l l
          Hwf_fixed Hrelated_pub with "Hrevoked") as "Hrevoked".
        iAssert (interp Wfixed C (WInt ALLOC_OK))
          with "[]" as "#Hinterp_status".
        { iApply interp_weakening.interp_int. }
        iApply (switcher_ret_specification Nswitcher W Wshare C _
          e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
          (WCap true RW Global b e b) (WInt ALLOC_OK)
          with "[$Halloc $Hswitcher $Hinterp_fixed $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
        { exact Hrelated_pub. }
        { apply regmap_full_dom in Hfull_rmap.
          repeat rewrite dom_insert_L.
          repeat rewrite dom_delete_L.
          rewrite Hfull_rmap. set_solver+. }
        { exact Hframe. }
        { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
        { exact Hnodup. }
        { intros a Ha. apply Htemps in Ha. exact Ha. }
  Qed.

  Lemma malloc_entry_point_spec
    (g_allocator_exp_tbl : Locality)
    (W : WORLD)
    (C : CmptName)
    (Nswitcher : namespace) :
    allocator_ctx ∗
    allocator_service_ctx ∗
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
    WSealed ot_switcher (allocator_malloc g_allocator_exp_tbl)
      ↦□ₑ allocator_malloc_nargs ∗
    WSealed ot_switcher (allocator_malloc Local)
      ↦□ₑ allocator_malloc_nargs -∗
    ot_switcher_prop W C
      (WCap true RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a).
  Proof.
    iIntros "(#Halloc & #Hservice & #Hswitcher & #HPCC & #HCGP & #Hentry & #Hsealed & #Hsealed_local)".
    iExists g_allocator_exp_tbl, allocator_exp_tbl_b, allocator_exp_tbl_e,
      (allocator_exp_tbl_b ^+ allocator_malloc_exp_tbl_off)%a,
      allocator_pcc_b, allocator_pcc_e, allocator_cgp_b, allocator_cgp_e,
      allocator_malloc_nargs, allocator_malloc_pcc_off, hts_allocator_exp_tblN.
    iFrame "#".
    iSplit; first done.
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_malloc_exp_tbl_off in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).
    iSplit; first (iPureIntro; rewrite /allocator_malloc_exp_tbl_off;
      pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).
    iSplit; first (iPureIntro; rewrite /allocator_malloc_nargs; lia).
    iSplit; first (iPureIntro; pose proof allocator_size_imports as Himports;
      rewrite /allocator_malloc_pcc_off -allocator_imports_length; eauto).

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
    iSplit; first (iPureIntro; apply Hexport_shadow;
      pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_malloc_exp_tbl_off in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; apply Hexport_shadow;
      pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).
    iSplit; first (iPureIntro; apply Hexport_shadow;
      pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).

    iSplit.
    { iPureIntro.
      apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      clear - Hregions Hheap Himports_size Hcode_size.
      assert (allocator_pcc_b ∈ finz.seq_between allocator_pcc_b allocator_pcc_e)
        as Hpcc by (apply elem_of_finz_seq_between; solve_addr).
      assert (allocator_pcc_b ∈ finz.seq_between heap_b heap_e)
        as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    iSplit.
    { iPureIntro.
      apply not_true_is_false; intros Hheap.
      pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions.
      cbn [union_list] in Hregions.
      apply withinBounds_true_iff in Hheap.
      pose proof allocator_size_data as Hdata_size.
      clear - Hregions Hheap Hdata_size.
      assert (allocator_cgp_b ∈ finz.seq_between allocator_cgp_b allocator_cgp_e)
        as Hcgp by (apply elem_of_finz_seq_between; solve_addr).
      assert (allocator_cgp_b ∈ finz.seq_between heap_b heap_e)
        as Hhelem by (apply elem_of_finz_seq_between; solve_addr).
      set_solver. }
    iModIntro.
    iIntros (W') "%Hpriv".
    iNext.
    change (allocator_pcc_b ^+ allocator_malloc_pcc_off)%a with allocator_malloc_pcc_addr.
    iApply (malloc_exec_entry_point W' C Nswitcher).
    iFrame "#".
  Qed.


End Heap_Temporal_Safety_Interp.
