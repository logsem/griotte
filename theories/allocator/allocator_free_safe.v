From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl.
From griotte Require Import world_interp_stack switcher_spec_return model_interp_stack.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Import allocator_header_spec.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec allocator_otype.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ} {relg : relGS Σ}
    {allocator_historyg : allocatorHistoryG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  Lemma free_world_heap_receipt W C base obj :
    heap_std W !! base = Some obj ->
    world_interp W C -∗
    world_interp W C ∗
    ∃ reserved,
      allocator_allocation
        (allocator_historyg := @allocator_historyG_instance Σ allocatorg)
        base (alloc_object_end obj) reserved.
  Proof.
    iIntros (Hbase) "Hworld".
    iDestruct (world_interp_open_heap_provenance W C [] with "[Hworld]")
      as "[Hworld #Hprovenance]".
    { by rewrite -open_world_interp_empty. }
    iDestruct (big_sepM_lookup with "Hprovenance")
      as (reserved) "#Hreceipt"; first exact Hbase.
    rewrite -open_world_interp_empty.
    iFrame "Hworld". iExists reserved. iFrame "Hreceipt".
  Qed.

  Lemma free_quarantine_range h b e :
    heap_wf h ->
    h !! b = Some (MkAllocObject b e AllocObjectLive) ->
    Forall (fun x => is_heap_address x = true) (finz.seq_between b e) ->
    Forall (fun x => is_heap_address x = true /\ exists obj',
      heap_lookup_addr (heap_quarantine h b) x = Some (b,obj') /\
      alloc_object_status obj' = AllocObjectQuarantined)
      (finz.seq_between b e).
  Proof.
    intros Hwf Hb Hheap.
    apply Forall_forall. intros x Hx. split.
    - apply Forall_forall with (x := x) in Hheap; done.
    - exists (MkAllocObject b e AllocObjectQuarantined). split; last done.
      apply heap_lookup_addr_complete.
      + apply heap_quarantine_wf; done.
      + rewrite (heap_quarantine_lookup h b _ Hb). reflexivity.
      + unfold alloc_object_contains.
        apply elem_of_finz_seq_between in Hx. exact Hx.
  Qed.

  (** Open the payload of an allocation. Only the region and the standard
      states are involved, so the sealing resources may be open. *)
  Lemma free_region_open_list W C la :
    NoDup la ->
    Forall (λ a,
      heap_addr_live (heap_std W) a ∧
      ∃ ρ, ρ ≠ Revoked ∧ std W !! a = Some ρ) la ->
    region W C ∗ sts_full_world W C
    ==∗
    ∃ ws,
      open_region_many W C la ∗
      sts_full_world W C ∗
      ([∗ list] a;v ∈ la;ws, a ↦ₐ v) ∗
      ([∗ list] a ∈ la,
        ∃ p φ ρ,
          ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
          rel C a p φ ∗
          sts_state_std C a ρ).
  Proof.
    intros Hnodup Hstates.
    induction la as [|a la IH].
    - iIntros "[Hregion Hsts]". iModIntro. iExists [].
      rewrite -region_open_nil. iFrame. simpl. done.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hstates as [Ha_state Hstates].
      destruct Ha_state as [Hlive (ρ & Hnr & Hstd)].
      iIntros "Hworld".
      iMod (region_rel_get_state W C a ρ Hstd with "Hworld")
        as "(Hregion & Hsts & Hrel)".
      iDestruct "Hrel" as (p φ) "[%Hpers #Hrel]".
      iMod (IH Hnodup Hstates with "[$Hregion $Hsts]") as (ws)
        "(Hregion & Hsts & Hmem & Hhandles)".
      iDestruct (region_open_next W C φ la a p ρ Hnr Hlive Hnotin
        Hstd with "[$Hregion $Hrel $Hsts]") as (v)
        "(Hsts & Hstate & Hregion & Ha & Hmono & Hφ & %HnonO)".
      iModIntro. iExists (v :: ws). simpl.
      iFrame "Hregion Hsts Ha Hmem Hhandles".
      iExists p, φ, ρ. iFrame "Hstate Hrel". done.
  Qed.

  Lemma free_world_close_quarantined_list W C la :
    NoDup la ->
    Forall (λ a,
      is_heap_address a = true ∧
      ∃ base obj,
        heap_lookup_addr (heap_std W) a = Some (base,obj) ∧
        alloc_object_status obj = AllocObjectQuarantined) la ->
    world_interp_open W C la ∗
    ([∗ list] a ∈ la,
      ∃ p φ ρ,
        ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
        rel C a p φ ∗
        sts_state_std C a ρ) ∗
    ([∗ list] a ∈ la, reclaim_token a)
    -∗
    world_interp W C.
  Proof.
    intros Hnodup Hquarantined.
    induction la as [|a la IH].
    - iIntros "(Hworld & _ & _)".
      by rewrite -open_world_interp_empty.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hquarantined as [Ha_status Hquarantined].
      destruct Ha_status as [Hheap (base & obj & Hlookup & Hstatus)].
      iIntros "(Hworld & Hhandles & Htokens)".
      iDestruct "Hhandles" as "[Hhandle Hhandles]".
      iDestruct "Htokens" as "[Htoken Htokens]".
      iDestruct "Hhandle" as (p φ ρ) "(%Hpers & #Hrel & Hstate)".
      iDestruct (close_world_interp_next_quarantined_heap W C la a p φ ρ
        base obj with "Hworld Hrel Hstate Htoken") as "Hworld"; eauto.
      iApply (IH Hnodup Hquarantined with "[$Hworld $Hhandles $Htokens]").
  Qed.

  (** Execute free for an arbitrary caller and update the shared heap world. *)
  Lemma free_exec_entry_point W C (Nswitcher : namespace) :
    allocator_ctx ∗ allocator_service_ctx ∗
    seal_pred AllocOtype allocator_otype_propC ∗
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
    (* Unpack the entry register map and classify the requested capability. *)
    iIntros "(#Halloc & #Hservice & #Hspred & #Hswitcher)".
    iIntros (cstk Ws Cs regs a_stk e_stk)
      "#Halloc' (Hcont & %Hframe & Hregister & Hrmap & Hworld & %Hsync & Hcstk & Hna)".
    rewrite /interp_conf.
    iDestruct "Hregister" as
      "(%Hfull_rmap & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_csp & Hregs)".
    iDestruct "Hregs" as "[#Hargs #Hzeros]".
    rewrite /registers_pointsto.
    cbn in Hfull_rmap.
    getRegValList [PC;cgp;cra;csp;ca0;ca1;ca2;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    iExtractList "Hrmap" [PC;cgp;cra;csp;ca0;ca1;ca2]
      as ["HPCr";"Hcgpr";"Hcrar";"Hcspr";"Hca0";"Hca1";"Hca2"].
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;ctp;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    rewrite HwPC in HPC. injection HPC as HeqPC. subst wPC.
    (* A malformed allocator capability traps in the owner macro. *)
    destruct (get_tag wca0 && is_sealed_with_o wca0 AllocOtype) eqn:Hcap_valid;
      cycle 1.
    { iApply (allocator_free_invalid_capability_spec ⊤ wca0
        with "[$Hservice $Hna $HPCr $Hca0 $Hctp $Hct3 $Hct4]"); first solve_ndisj.
      apply andb_false_iff in Hcap_valid as [?|?]; auto. }
    apply andb_true_iff in Hcap_valid as [Hwca0_tag Hwca0_sealed].
    iDestruct ("Hargs" $! ca0 wca0 with "[] []") as "#Hinterp_ca0".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca0. }
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    assert (Hshape :
      (∃ p g b e a,
        wca1 = WCap true p g b e a ∧
        (heap_b < b ∧ b < e ∧ e <= heap_e)%a) ∨
      (∀ next allocations id,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1)%a next allocations →
        ¬ allocator_free_valid next allocations id wca1)).
    { destruct wca1 as [n|s|tag p g b e a|ot s].
      - right. intros next allocations id _ _ (p & g & b & e & a & Hcap & _).
        discriminate Hcap.
      - destruct s as [tag p g b e a|tag p g b e a].
        + destruct tag.
          * destruct (decide (heap_b < b ∧ b < e ∧ e <= heap_e)%a)
              as [Hbounds|Hbad].
            -- left. exists p,g,b,e,a. split; [reflexivity|exact Hbounds].
            -- right. intros next allocations id Hnext _
                 (p' & g' & b' & e' & a' & Hcap & Hrange & _).
               inversion Hcap; subst. apply Hbad. destruct Hnext.
               destruct Hrange as (Hbb & Hbe & Hen).
               repeat split; solve_addr.
          * right. intros next allocations id _ _ (p' & g' & b' & e' & a' & Hcap & _).
            discriminate Hcap.
        + right. intros next allocations id _ _ (p' & g' & b' & e' & a' & Hcap & _).
          discriminate Hcap.
      - right. intros next allocations id _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap.
      - right. intros next allocations id _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap. }
    destruct Hshape as [Hcap|Hinvalid].
    2: {
      iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
        (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      (* Take the owner word and identifier out of the sealing predicate. *)
      iMod (allocator_otype_open W (revoke W) C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id S)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hclose)".
      iApply (allocator_free_invalid_correct ⊤ g_owner a_owner id S wca1
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try assumption.
      iFrame "Halloc Hservice Hna Hid Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
      iNext.
      iIntros "(Hna & Hid & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull)".
      (* Close the sealing predicate of the allocator capability. *)
      iDestruct ("Hclose" $! S with "[$Ha_owner $Hid $Hrights]") as "Hworld".
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
        (WInt ALLOC_INVALID) (WInt 0)
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
    (* A tagged argument carries the heap and active-region conditions. *)
    destruct Hcap as (p & g & b & e & a & -> & Hbounds).
    iDestruct ("Hargs" $! ca1 (WCap true p g b e a) with "[] []")
      as "#Hinterp_ca1".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca1. }
    iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld")
      as %Hheap_wf.
    iDestruct (interp_cap_heap_conditions W C p g b e a
      with "Hinterp_ca1") as %Hcapvalid.
    pose proof (free_heap_cap_payload W p g b e Hheap_wf Hbounds Hcapvalid)
      as Hcap_payload.
    destruct Hcap_payload as [Hobj Hpayload].
    destruct Hobj as (base & obj & Hlookup & Hlive & Hend).
    apply heap_lookup_addr_sound in Hlookup as [Hbase Hcontains].
    iDestruct (free_world_heap_receipt W C base obj Hbase with "Hworld")
      as "[Hworld #Hreceipt]".
    destruct obj as [objbase objend objstatus].
    cbn in Hlive. cbn in Hend. cbn in Hbase. cbn in Hcontains.
    destruct (Hheap_wf base _ Hbase) as (Hobjbase & Hobjnonempty & Hunique).
    change (base = objbase) in Hobjbase. subst objbase.
    assert (Hsubrange : (base <= b /\ b < e /\ e <= objend)%a).
    { repeat split; try assumption; unfold alloc_object_contains in Hcontains;
        solve_addr. }
    destruct (decide ((b,e)=(base,objend))) as [Hexact|Hnarrow].
    - injection Hexact as Hb_eq He_eq. subst b e.
      iDestruct "Hreceipt" as (reserved) "#Hreceipt".
      destruct reserved as [id' r].
      (* Take the owner word and identifier out of the sealing predicate,
         keeping the region available to open the payload. *)
      iDestruct (world_interp_open_heap_provenance W C [] with "[Hworld]")
        as "[Hworld #Hprovenance]".
      { by rewrite -open_world_interp_empty. }
      iEval (rewrite -open_world_interp_empty) in "Hworld".
      iMod (allocator_otype_sopen W W C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id S)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hregion & Hsts & Hclose)".
      destruct (decide (id' = id)) as [->|Hid_ne]; cycle 1.
      { (* The allocation belongs to another owner and is not freed. *)
        iMod (monotone_revoke_stack W C (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a
          with "[$Hinterp_csp $Hsts $Hregion]") as (l)
          "(%Htemps & Hsts & Hregion & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
        iApply (allocator_free_wrong_owner_spec ⊤ p g base objend a id' r
          g_owner a_owner id S
          (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
          with "[-]"); try solve_ndisj; try assumption.
        iFrame "Halloc Hservice Hna Hreceipt Hid Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
        iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
        iNext.
        iIntros "(Hna & _ & Hid & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull)".
        (* Close the sealing predicate in the revoked world. *)
        iEval (rewrite region_open_nil) in "Hregion".
        iDestruct (allocator_owned_rights_mono (revoke W) with "Hrights")
          as "Hrights".
        { rewrite revoke_heap. apply related_sts_heap_std_refl. }
        iDestruct ("Hclose" $! (revoke W) [] S
          with "[] [] [] [$Hregion $Hsts $Ha_owner $Hid $Hrights]")
          as "Hworld".
        { iPureIntro. rewrite revoke_heap. exact Hheap_wf. }
        { done. }
        { iPureIntro. apply revoke_related_sts_priv_world. }
        iEval (rewrite -open_world_interp_empty) in "Hworld".
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
        assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed
          by (subst Wfixed; rewrite close_list_heap; exact Hheap_wf).
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
          (WInt ALLOC_INVALID) (WInt 0)
          with "[$Halloc $Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
        { exact Hrelated_pub. }
        { apply regmap_full_dom in Hfull_rmap.
          repeat rewrite dom_insert_L.
          repeat rewrite dom_delete_L.
          rewrite Hfull_rmap. set_solver+. }
        { exact Hframe. }
        { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
        { exact Hnodup. }
        { intros x Hx. apply Htemps in Hx. exact Hx. } }
      iMod (free_region_open_list W C (finz.seq_between base objend)
        (finz_seq_between_NoDup base objend) Hpayload with "[$Hregion $Hsts]")
        as (ws) "(Hregion & Hsts & Hmem & Hhandles)".
      iDestruct (big_sepL2_length _ _ _ with "Hmem") as %Hlen.
      iApply (allocator_free_valid_correct ⊤ p g base objend a r
        g_owner a_owner id S ws
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        (λ v, (⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I) with "[-]");
        try solve_ndisj; try exact Hbounds; try (symmetry; exact Hlen);
        try assumption.
      iFrame "Halloc Hservice Hna Hreceipt Hid Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2
        Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hmem".
      iNext.
      iIntros "(Hna_post & Hreceipt_post & Hid & %Hbase_S & Ha_owner & HPCr_post & Hcgpr_post &
        Hcrar_post & Hca0_post & Hca1_post & Hca2_post & Hct0_post &
        Hct1_post & Hct2_post & Hct3_post & Hct4_post & Hctp_post &
        Hcnull_post & Htokens & Hlc)".
      (* The sealing predicate holds the right to free the live object. *)
      iDestruct (big_sepS_delete _ _ base with "Hrights")
        as "[Hright_base Hrights]"; first exact Hbase_S.
      subst objstatus.
      iDestruct "Hright_base" as "[%Hquarantined_base|Hright_base]".
      { destruct Hquarantined_base as [e' He']. rewrite Hbase in He'. discriminate. }
      iEval (rewrite /allocator_reclaimed) in "Htokens".
      iDestruct (heap_provenance_quarantine W.2 base with "Hprovenance")
        as "#Hprovenance_q".
      set (h' := heap_quarantine W.2 base).
      pose proof (heap_quarantine_future W.2 base) as Hheap_future.
      pose proof (heap_quarantine_wf W.2 base Hheap_wf) as Hheap_wf_q.
      pose proof (related_sts_pub_world_heap_update W
        (heap_quarantine W.2 base) Hheap_future) as Hrelated_W_q.
      assert (Houtside : forall x,
          x ∉ finz.seq_between base objend ->
          heap_addr_status W.2 x = heap_addr_status h' x)
        by (intros x Hnotin; unfold h';
            eapply free_heap_quarantine_status_outside; eauto).
      assert (Hdom_l : Forall
          (fun x => x ∈ dom (std W)) (finz.seq_between base objend))
        by (apply Forall_forall; intros x Hx;
            apply Forall_forall with (x := x) in Hpayload;
            last exact Hx;
            destruct Hpayload as [_ (ρ & _ & Hstd)];
            rewrite elem_of_dom; eexists; exact Hstd).
      (* Quarantine the object before closing the sealing predicate. *)
      iMod (free_region_open_heap_transition_range W C
          (finz.seq_between base objend) base h' Hheap_future Hheap_wf_q
          Houtside Hdom_l with "Hprovenance_q Hright_base [$Hregion $Hsts]")
        as "[Hregion Hsts]"; first reflexivity.
      (* Close the sealing predicate in the quarantined world. *)
      iDestruct ("Hclose" $! (heap_std_update W h') _ S
        with "[] [] [] [$Hregion $Hsts $Ha_owner $Hid Hrights]")
        as "Hworld_open_q".
      { done. }
      { done. }
      { iPureIntro. by apply related_sts_pub_priv_world. }
      { rewrite /allocator_owned_rights.
        iApply (big_sepS_delete _ _ base); first exact Hbase_S.
        iSplitR.
        - iLeft. iPureIntro. exists objend.
          rewrite /= /h' (heap_quarantine_lookup W.2 base _ Hbase).
          reflexivity.
        - iApply (allocator_owned_rights_mono W (heap_std_update W h')
            with "Hrights").
          exact Hheap_future. }
      assert (Hheap_range : Forall
          (fun x => is_heap_address x=true)
          (finz.seq_between base objend))
        by (apply Forall_forall; intros x Hx;
            apply withinBounds_true_iff;
            apply elem_of_finz_seq_between in Hx;
            destruct Hbounds as (Hb_heap & _ & He_heap);
            solve_addr).
      pose proof (free_quarantine_range W.2 base objend Hheap_wf Hbase
        Hheap_range) as Hquarantined.
      iAssert (world_interp (heap_std_update W h') C)
        with "[Hworld_open_q Hhandles Htokens]" as "Hworld_q".
      { assert (Hquarantined_close : Forall
            (fun x => is_heap_address x=true /\
              exists b0 obj',
                heap_lookup_addr (heap_std (heap_std_update W h')) x =
                  Some (b0,obj') /\
                alloc_object_status obj'=AllocObjectQuarantined)
            (finz.seq_between base objend))
          by (apply Forall_forall; intros x Hx;
              apply Forall_forall with (x:=x) in Hquarantined;
              last exact Hx;
              destruct Hquarantined as
                [Hheap (obj' & Hlookup' & Hstatus)];
              split; first exact Hheap;
              exists base,obj'; split; first exact Hlookup'; exact Hstatus).
        iApply (free_world_close_quarantined_list
          (heap_std_update W h') C (finz.seq_between base objend)
          (finz_seq_between_NoDup base objend) Hquarantined_close).
        iFrame "Hworld_open_q Hhandles Htokens". }
      iDestruct (interp_cap_disjoint_wl W C RWL Local
        (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a eq_refl
        with "Hinterp_csp") as %[_ Hstack_disjoint].
      iAssert (interp (heap_std_update W h') C
        (WCap true RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a))
        with "[Hinterp_csp]" as "Hinterp_csp_q".
      { iApply (monotone.interp_monotone_cap_nonheap
          W (heap_std_update W h') C true RWL Local
          (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a
          Hstack_disjoint Hrelated_W_q).
        iExact "Hinterp_csp". }
      iMod (world_interp_revoke_stack (heap_std_update W h') C
          (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a
          with "[$Hinterp_csp_q $Hworld_q]")
        as (l) "(%Htemps & Hworld_rev & Hstack_revoked &
          Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      iMod (lc_fupd_elim_later with "Hlc Hrevoked") as "Hrevoked".
      iMod "Hstack_mem" as (stk_mem) "Hstk".
      iEval (cbn) in "HPCr_post".
      iDestruct "Hca2_post" as (wca2') "Hca2_post".
      iDestruct "Hct0_post" as (wct0') "Hct0_post".
      iDestruct "Hct1_post" as (wct1') "Hct1_post".
      iDestruct "Hct2_post" as (wct2') "Hct2_post".
      iDestruct "Hct3_post" as (wct3') "Hct3_post".
      iDestruct "Hct4_post" as (wct4') "Hct4_post".
      iDestruct "Hctp_post" as (wctp') "Hctp_post".
      iInsertList "Hrmap" [cnull;ctp;ct4;ct3;ct2;ct1;ct0;ca2;cra;cgp].
      set (Wq := heap_std_update W h').
      set (Wfixed := close_list
        (l ++ finz.seq_between (a_stk ^+ 4)%a e_stk) (revoke Wq)).
      destruct Htemps as [Hnodup Htemps].
      assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed
        by (subst Wfixed; rewrite close_list_heap revoke_heap; exact Hheap_wf_q).
      assert (related_sts_pub_world Wq Wfixed) as Hrelated_q_fixed.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub
        by (eapply related_sts_pub_trans_world; eauto).
      iDestruct (RevokedResources_mono_pub Wq Wfixed C l l
        Hheap_wf_fixed Hrelated_q_fixed with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_weakening.interp_int. }
      iApply (switcher_ret_specification Nswitcher W (revoke Wq) C _
        e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
        (WInt ALLOC_OK) (WInt 0)
        with "[$Halloc $Hswitcher $Hinterp0 $Hstk $Hcstk $Hcont $Hworld_rev $Hna_post $HPCr_post $Hrevoked $Hrmap $Hca0_post $Hca1_post $Hcspr]").
      { exact Hrelated_pub. }
      { apply regmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
      { exact Hnodup. }
      { intros x Hx. apply Htemps. exact Hx. }
    - (* A strict subrange of the allocation is rejected. *)
      iDestruct "Hreceipt" as (reserved) "#Hreceipt".
      iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
        (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      (* Take the owner word and identifier out of the sealing predicate. *)
      iMod (allocator_otype_open W (revoke W) C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id S)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hclose)".
      iApply (allocator_free_narrowed_spec ⊤ p g base objend reserved b e a
        g_owner a_owner id S
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try exact Hsubrange; try exact Hnarrow;
        try assumption.
      iFrame "Halloc Hservice Hna Hreceipt Hid Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull".
      iNext.
      iIntros "(Hna & _ & Hid & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull)".
      (* Close the sealing predicate of the allocator capability. *)
      iDestruct ("Hclose" $! S with "[$Ha_owner $Hid $Hrights]") as "Hworld".
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
      assert (heap_wf (heap_std Wfixed)) as Hheap_wf_fixed
        by (subst Wfixed; rewrite close_list_heap; exact Hheap_wf).
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
        (WInt ALLOC_INVALID) (WInt 0)
        with "[$Halloc $Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply regmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
      { exact Hnodup. }
      { intros x Hx. apply Htemps in Hx. exact Hx. }
  Qed.


  Lemma free_entry_point_spec
    (g_allocator_exp_tbl : Locality)
    (W : WORLD)
    (C : CmptName)
    (Nswitcher : namespace) :
    allocator_ctx ∗
    allocator_service_ctx ∗
    seal_pred AllocOtype allocator_otype_propC ∗
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
    iIntros "(#Halloc & #Hservice & #Hspred & #Hswitcher & #HPCC & #HCGP & #Hentry & #Hsealed & #Hsealed_local)".
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
