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
    {allocator_historyg : allocatorHistoryG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** Execute free for an arbitrary caller and update the shared heap world. *)
  Lemma free_exec_entry_point W C (Nswitcher : namespace) :
    allocator_ctx ∗ allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
    (* Unpack the entry register map and classify the requested capability. *)
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
    rewrite HwPC in HPC. injection HPC as HeqPC. subst wPC.
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
      (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
      "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
    assert (Hshape :
      (∃ p g b e a, wca0 = WCap true p g b e a) ∨
      (∀ next allocations,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1)%a next allocations →
        ¬ allocator_free_valid next allocations wca0)).
    { destruct wca0 as [n|s|tag p g b e a|ot s].
      - right. intros next allocations _ _ (p & g & b & e & a & Hcap & _).
        discriminate Hcap.
      - destruct s as [tag p g b e a|tag p g b e a].
        + destruct tag.
          * left. exists p,g,b,e,a. reflexivity.
          * right. intros next allocations _ _ (p' & g' & b' & e' & a' & Hcap & _).
            discriminate Hcap.
        + right. intros next allocations _ _ (p' & g' & b' & e' & a' & Hcap & _).
          discriminate Hcap.
      - right. intros next allocations _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap.
      - right. intros next allocations _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap. }
    destruct Hshape as [Hcap|Hinvalid].
    2: {
      iApply (allocator_free_invalid_correct ⊤ wca0
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
    (* WIP: the remaining branch has a tagged capability in ca0. Its shape
       alone does not provide the payload points-to required by
       allocator_free_valid_correct. In particular, interp_cap_O is True, so
       an O-permission argument supplies no live-region resources. *)
    (* Search the service headers and reject invalid or narrowed bounds. *)
    (* Handle an already quarantined allocation without consuming its receipt. *)
    (* Open the world payload of an exact live allocation and execute free. *)
    (* Quarantine the logical object and invalidate retained aliases. *)
    (* Restore the allocator service and return through the switcher. *)
  Admitted.


  Lemma free_entry_point_spec
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
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a)
      ((allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a ↦ₐ
        WInt (encode_entry_point allocator_free_nargs allocator_free_pcc_off)) ∗
    WSealed ot_switcher (allocator_free g_allocator_exp_tbl)
      ↦□ₑ allocator_free_nargs ∗
    WSealed ot_switcher (allocator_free Local)
      ↦□ₑ allocator_free_nargs -∗
    ot_switcher_prop W C
      (WCap true RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a).
  Proof.
    iIntros "(#Halloc & #Hservice & #Hswitcher & #HPCC & #HCGP & #Hentry & #Hsealed & #Hsealed_local)".
    iExists g_allocator_exp_tbl, allocator_exp_tbl_b, allocator_exp_tbl_e,
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a,
      allocator_pcc_b, allocator_pcc_e, allocator_cgp_b, allocator_cgp_e,
      allocator_free_nargs, allocator_free_pcc_off, hts_allocator_exp_tblN.
    iFrame "#".
    iSplit; first done.
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; rewrite /allocator_free_nargs; lia).
    iSplit; first (iPureIntro; pose proof allocator_size_imports as Himports;
      pose proof allocator_size_code as Hcode;
      rewrite /allocator_code length_app in Hcode;
      rewrite /allocator_free_pcc_off /allocator_malloc_pcc_off in Hcode |- *;
      solve_addr).

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
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off in Hsize |- *;
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
    change (allocator_pcc_b ^+ allocator_free_pcc_off)%a with allocator_free_pcc_addr.
    iApply (free_exec_entry_point W' C Nswitcher).
    iFrame "#".
  Qed.

End Heap_Temporal_Safety_Interp.
