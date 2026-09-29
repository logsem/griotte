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

  (* TODO: move to world_ghost_theory.v. *)
  Lemma free_region_rel_get W C a ρ :
    std W !! a = Some ρ ->
    world_interp W C
    ==∗
    world_interp W C ∗
    ∃ p φ, ⌜∀ WCv, Persistent (φ WCv)⌝ ∗ rel C a p φ.
  Proof.
    iIntros (Hlookup) "Hworld".
    rewrite world_interp_eq /world_interp_def.
    iDestruct "Hworld" as "(Hr & Hsts & Hseal)".
    rewrite region_eq /region_def.
    iDestruct "Hr" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hmap)".
    rewrite /region_map_def.
    iDestruct "Hmap" as "(%Hcovered & Hheap & Hentries)".
    assert (is_Some (M !! a)) as [γp Hγp].
    { apply elem_of_dom. rewrite -Hdom elem_of_dom. eauto. }
    destruct γp as [γ p].
    iMod (reg_get with "[$HM]") as "[HM Hrel]";
      first (iPureIntro; exact Hγp).
    iDestruct (big_sepM_delete _ _ a with "Hentries") as "[Hentry Hentries]";
      first exact Hγp.
    iDestruct "Hentry" as (ρ' Hρ') "[Hstate Hentry]".
    iDestruct (sts_full_state_std with "Hsts Hstate") as %Hρeq.
    rewrite Hlookup in Hρeq. injection Hρeq as <-.
    iDestruct "Hentry" as (γpred p' φ Heq Hpers) "(#Hsaved & Haddr)".
    iDestruct (big_sepM_delete _ _ a with "[Hstate Haddr $Hentries]")
      as "Hentries"; [exact Hγp| |].
    { iExists ρ. iFrame "∗#%". }
    iModIntro. iSplitL "HM Hheap Hentries Hsts Hseal".
    { iFrame "Hsts Hseal". iExists M, Mρ. iFrame "HM".
      iFrame "%". rewrite /region_map_def. iFrame "Hheap Hentries". }
    iExists p', φ. iSplit; first done.
    rewrite rel_eq /rel_def. iExists γpred.
    simplify_eq. iFrame "Hsaved Hrel".
  Qed.

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

  Lemma free_world_open_list W C la :
    NoDup la ->
    Forall (λ a,
      heap_addr_live (heap_std W) a ∧
      ∃ ρ, ρ ≠ Revoked ∧ std W !! a = Some ρ) la ->
    world_interp W C
    ==∗
    ∃ ws,
      world_interp_open W C la ∗
      ([∗ list] a;v ∈ la;ws, a ↦ₐ v) ∗
      ([∗ list] a ∈ la,
        ∃ p φ ρ,
          ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
          rel C a p φ ∗
          sts_state_std C a ρ).
  Proof.
    intros Hnodup Hstates.
    induction la as [|a la IH].
    - iIntros "Hworld". iModIntro. iExists [].
      rewrite open_world_interp_empty. iFrame. simpl. done.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hstates as [Ha_state Hstates].
      destruct Ha_state as [Hlive (ρ & Hnr & Hstd)].
      iIntros "Hworld".
      iMod (free_region_rel_get W C a ρ Hstd with "Hworld")
        as "[Hworld Hrel]".
      iDestruct "Hrel" as (p φ) "[%Hpers #Hrel]".
      iMod (IH Hnodup Hstates with "Hworld") as (ws)
        "(Hworld & Hmem & Hhandles)".
      rewrite world_interp_open_eq /world_interp_open_def.
      iDestruct "Hworld" as "(Hregion & Hsts & Hseal)".
      iDestruct (region_open_next W C φ la a p ρ Hnr Hlive Hnotin
        Hstd with "[$Hregion $Hrel $Hsts]") as (v)
        "(Hsts & Hstate & Hregion & Ha & Hmono & Hφ & %HnonO)".
      iModIntro. iExists (v :: ws). simpl.
      iSplitL "Hregion Hsts Hseal".
      { iFrame. }
      iFrame "Ha Hmem Hhandles".
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

  (* TODO: move to heap_region.v. *)
  Lemma free_heap_quarantine_status_outside h b e :
    heap_wf h ->
    h !! b = Some (MkAllocObject b e AllocObjectLive) ->
    ∀ a, a ∉ finz.seq_between b e ->
      heap_addr_status h a =
      heap_addr_status (heap_quarantine h b) a.
  Proof.
    intros Hwf Hb a Houtside.
    rewrite /heap_addr_status.
    destruct (is_heap_address a) eqn:Ha; last reflexivity.
    destruct (heap_lookup_addr h a) as [ [c o] |] eqn:Hlookup.
    - apply heap_lookup_addr_sound in Hlookup as [Hc Hcontains].
      assert (c <> b) as Hcne.
      { intro Heq. subst c. rewrite Hb in Hc. injection Hc as <-.
        apply Houtside. apply elem_of_finz_seq_between.
        unfold alloc_object_contains in Hcontains. simpl in Hcontains.
        exact Hcontains. }
      assert (heap_lookup_addr (heap_quarantine h b) a = Some (c,o))
        as Hnew.
      { eapply heap_lookup_addr_complete.
        - apply heap_quarantine_wf. exact Hwf.
        - rewrite heap_quarantine_lookup_ne; [exact Hc|congruence].
        - exact Hcontains. }
      rewrite Hnew. reflexivity.
    - pose proof (proj1 (heap_lookup_addr_none h a Hwf) Hlookup) as Hnone.
      destruct (heap_lookup_addr (heap_quarantine h b) a)
        as [ [c o] |] eqn:Hnew; last reflexivity.
      apply heap_lookup_addr_sound in Hnew as [Hc Hcontains].
      destruct (decide (c = b)) as [->|Hcne].
      + rewrite (heap_quarantine_lookup h b _ Hb) in Hc.
        injection Hc as <-. exfalso. apply Houtside.
        apply elem_of_finz_seq_between.
        unfold alloc_object_contains in Hcontains. simpl in Hcontains.
        exact Hcontains.
      + rewrite heap_quarantine_lookup_ne in Hc; [|congruence].
        exfalso. exact (Hnone c o Hc Hcontains).
  Qed.

  Lemma free_lookup_delete_list_some {A} (l : list Addr)
    (M : gmap Addr A) a x :
    delete_list l M !! a = Some x -> a ∉ l.
  Proof.
    induction l as [|b l IH]; simpl; first set_solver.
    intros Hlookup. apply not_elem_of_cons. split.
    - intro Heq. subst a. rewrite lookup_delete in Hlookup.
      destruct (decide (b = b)); [discriminate|congruence].
    - assert (b ≠ a) as Hne.
      { intro Heq. subst a. rewrite lookup_delete in Hlookup.
        destruct (decide (b = b)); [discriminate|congruence]. }
      rewrite lookup_delete_ne in Hlookup; last exact Hne.
      apply IH. exact Hlookup.
  Qed.

  (* TODO: move to world_ghost_theory.v. *)
  Lemma free_world_open_heap_transition_range W C l h' :
    related_sts_heap_std (heap_std W) h' ->
    heap_wf h' ->
    (∀ a, a ∉ l ->
      heap_addr_status (heap_std W) a = heap_addr_status h' a) ->
    Forall (λ a, a ∈ dom (std W)) l ->
    heap_provenance h' -∗
    world_interp_open W C l
    ==∗
    world_interp_open (heap_std_update W h') C l.
  Proof.
    iIntros (Hheap_future Hwf_new Hstatus Hdom_l)
      "#Hprovenance Hworld".
    pose proof (related_sts_pub_world_heap_update W h' Hheap_future)
      as Hrelated.
    rewrite world_interp_open_eq /world_interp_open_def.
    iDestruct "Hworld" as "(Hregion & Hsts & Hseal)".
    rewrite open_region_many_eq /open_region_many_def.
    iDestruct "Hregion" as (M Mρ) "(HM & %Hdom & %Hdomρ & Hmap)".
    iDestruct "Hsts" as "(Hstd & Hloc & Hseals & Hheap)".
    iDestruct "Hmap" as "[%Hcovered_old [[Hfrags _] Hentries]]".
    iMod (heap_std_full_update C (heap_std W) h' Hheap_future
      with "Hheap Hfrags") as "[Hheap Hfrags]".
    iModIntro. iSplitL "HM Hfrags Hentries".
    { iExists M, Mρ. iFrame "HM".
      iSplit; first done. iSplit; first done.
      rewrite /region_map_def.
      iSplit.
      { iPureIntro. intros a Hquarantined.
        destruct (decide (a ∈ l)) as [Hin|Hnin].
        - apply Forall_forall with (x := a) in Hdom_l; done.
        - apply Hcovered_old. rewrite (Hstatus a Hnin).
          exact Hquarantined. }
      iFrame "Hfrags Hprovenance".
      iApply (big_sepM_mono with "Hentries").
      iIntros (a γ Hsome) "Hentry".
      assert (a ∉ l) as Hne by (eapply free_lookup_delete_list_some; eauto).
      iDestruct "Hentry" as (ρ Hρ) "[Hstate Hentry]".
      iExists ρ. iFrame "Hstate". iSplitR; first done.
      iDestruct "Hentry" as (γpred p φ Heq Hpers) "(#Hsavedφ & Hl)".
      iExists γpred, p, φ. iFrame "%#".
      iAssert (heap_addr_resource (heap_std W) a
        (region_std_interp W C a p φ ρ))%I with "[Hl]" as "Hl".
      { iExact "Hl". }
      iAssert (heap_addr_resource h' a
        (region_std_interp (heap_std_update W h') C a p φ ρ))%I
        with "[Hl]" as "Hnew".
      { iEval (rewrite heap_addr_resource_status).
        iEval (rewrite heap_addr_resource_status) in "Hl".
        iEval (rewrite (Hstatus a Hne)) in "Hl".
        destruct (heap_addr_status h' a) as [status|] eqn:Hstatus_a;
          [destruct status|].
        - destruct ρ; cbn [region_std_interp]; last done.
          + iDestruct "Hl" as (v HnonO) "(Hl & #HmonoV & Hφ)".
            iFrame "%#∗".
            destruct (isWL p); [| destruct (isDL p)].
            * iApply ("HmonoV" with "[] [] Hφ"); done.
            * iApply ("HmonoV" with "[] [] Hφ"); done.
            * iApply ("HmonoV" with "[] [] Hφ"); last done.
              iPureIntro. by apply related_sts_pub_priv_world.
          + iDestruct "Hl" as (v HnonO) "(Hl & #HmonoV & Hφ)".
            iFrame "%#∗".
            iApply "HmonoV"; iFrame "∗#"; auto.
            iPureIntro.
            apply related_sts_pub_priv_world in Hrelated; naive_solver.
        - iExact "Hl".
        - iExact "Hl". }
      iExact "Hnew". }
    iSplitL "Hstd Hloc Hseals Hheap".
    { rewrite /sts_full_world /heap_std_update /=. iFrame "∗#". }
    iApply (sealing_map_monotone_pub with "Hseal"); eauto.
  Qed.

  (* TODO: move to logrel.v. *)
  Lemma free_heap_cap_payload W p g b e :
    heap_wf (heap_std W) ->
    (heap_b < b ∧ b < e ∧ e <= heap_e)%a ->
    heap_cap_O_valid W p g b e ->
    (∃ base obj, heap_lookup_addr (heap_std W) b = Some (base,obj) ∧
      alloc_object_status obj = AllocObjectLive ∧ (e <= alloc_object_end obj)%a) ∧
    Forall (λ x, heap_addr_live (heap_std W) x ∧
      ∃ ρ, ρ ≠ Revoked ∧ std W !! x = Some ρ) (finz.seq_between b e).
  Proof.
    intros Hwf (Hb & Hbe & He) (Hvalid & Hcoverage).
    assert (Hbheap : is_heap_address b = true).
    { apply withinBounds_true_iff. solve_addr. }
    pose proof (Hvalid Hbe) as Hlive.
    rewrite /heap_cap_live Hbheap in Hlive.
    destruct (heap_lookup_addr (heap_std W) b) as [ [base obj] | ] eqn:Hlookup.
    2: { rewrite Hlookup in Hlive. contradiction. }
    rewrite Hlookup in Hlive.
    destruct (alloc_object_status obj) eqn:Hstatus.
    2: { contradiction. }
    destruct Hlive as (Hend & Hexec & Hwl).
    split.
    { exists base,obj. repeat split; eauto. }
    apply Forall_forall. intros x Hx. split.
    { eapply heap_cap_valid_addr_live; eauto.
      apply withinBounds_true_iff.
      apply elem_of_finz_seq_between in Hx. solve_addr. }
    assert (Hxheap : is_heap_address x = true).
    { apply withinBounds_true_iff.
      apply elem_of_finz_seq_between in Hx. solve_addr. }
    specialize (Hcoverage x Hx Hxheap).
    destruct g.
    - exists Permanent. split; first discriminate. exact Hcoverage.
    - destruct Hcoverage as [Hperm|Htemp].
      + exists Permanent; split; first discriminate. exact Hperm.
      + exists Temporary; split; first discriminate. exact Htemp.
  Qed.

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
    iExtractList "Hrmap" [PC;cgp;cra;csp;ca0;ca1;ca2]
      as ["HPCr";"Hcgpr";"Hcrar";"Hcspr";"Hca0";"Hca1";"Hca2"].
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;ctp;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    rewrite HwPC in HPC. injection HPC as HeqPC. subst wPC.
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    assert (Hshape :
      (∃ p g b e a,
        wca0 = WCap true p g b e a ∧
        (heap_b < b ∧ b < e ∧ e <= heap_e)%a) ∨
      (∀ next allocations,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1)%a next allocations →
        ¬ allocator_free_valid next allocations wca0)).
    { destruct wca0 as [n|s|tag p g b e a|ot s].
      - right. intros next allocations _ _ (p & g & b & e & a & Hcap & _).
        discriminate Hcap.
      - destruct s as [tag p g b e a|tag p g b e a].
        + destruct tag.
          * destruct (decide (heap_b < b ∧ b < e ∧ e <= heap_e)%a)
              as [Hbounds|Hbad].
            -- left. exists p,g,b,e,a. split; [reflexivity|exact Hbounds].
            -- right. intros next allocations Hnext _
                 (p' & g' & b' & e' & a' & Hcap & Hrange & _).
               inversion Hcap; subst. apply Hbad. destruct Hnext.
               destruct Hrange as (Hbb & Hbe & Hen).
               repeat split; solve_addr.
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
      iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
        (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
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
    (* A tagged argument carries the heap and active-region conditions. *)
    destruct Hcap as (p & g & b & e & a & -> & Hbounds).
    iDestruct ("Hargs" $! ca0 (WCap true p g b e a) with "[] []")
      as "#Hinterp_ca0".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca0. }
    iDestruct (wp_rules_interp.world_interp_heap_wf with "Hworld")
      as %Hheap_wf.
    iDestruct (interp_weakening.interp_cap_heap_conditions W C p g b e a
      with "Hinterp_ca0") as %Hcapvalid.
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
      iMod (free_world_open_list W C (finz.seq_between base objend)
        (finz_seq_between_NoDup base objend) Hpayload with "Hworld")
        as (ws) "(Hworld_open & Hmem & Hhandles)".
      iDestruct (big_sepL2_length _ _ _ with "Hmem") as %Hlen.
      iApply (allocator_free_valid_correct ⊤ p g base objend a reserved ws
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        (λ v, (⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I) with "[-]");
        try solve_ndisj; try exact Hbounds; try (symmetry; exact Hlen).
      iFrame "Halloc Hservice Hna Hreceipt HPCr Hcgpr Hcrar Hca0 Hca1 Hca2
        Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hmem".
      iNext.
      iIntros "(Hna_post & Hreceipt_post & HPCr_post & Hcgpr_post &
        Hcrar_post & Hca0_post & Hca1_post & Hca2_post & Hct0_post &
        Hct1_post & Hct2_post & Hct3_post & Hct4_post & Hctp_post &
        Hcnull_post & Htokens)".
      iEval (rewrite /allocator_reclaimed) in "Htokens".
      iDestruct (world_interp_open_heap_provenance W C
        (finz.seq_between base objend) with "Hworld_open")
        as "[Hworld_open #Hprovenance]".
      iDestruct (heap_provenance_quarantine W.2 base with "Hprovenance")
        as "#Hprovenance_q".
      subst objstatus.
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
      iMod (free_world_open_heap_transition_range W C
          (finz.seq_between base objend) h' Hheap_future Hheap_wf_q
          Houtside Hdom_l with "Hprovenance_q Hworld_open")
        as "Hworld_open_q".
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
      assert (Hquarantined_close : Forall
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
      iFrame "Hworld_open_q Hhandles Htokens".
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
      (* CHECKPOINT: a fresh interactive MCP session replayed and accepted the
         proof script through the world_interp_revoke_stack call above, then
         stopped at the resulting WP goal. No full-mode compile of this file
         was completed. Everything still needed after this point is
         UNVERIFIED and INCOMPLETE: the exact-allocation branch's switcher
         return, the narrowed-capability branch, and the remainder of this
         theorem. The Admitted below marks this boundary; free_exec_entry_point
         is not proved. *)
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
