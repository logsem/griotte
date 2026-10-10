From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl.
From griotte Require Import world_interp_stack switcher_spec_return.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Import allocator_header_spec.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** The safe [free] runs with the core [FreeAuth] instance, whose client
      part is [emp]: an arbitrary caller holds no right to free. *)
  Local Instance free_auth_core_inst : FreeAuth Σ := free_auth_core.

  (** The world's provenance of [ι]: the allocation's identifier and bounds. *)
  Lemma free_world_alloc_obj W C ι obj :
    heap_std W !! ι = Some obj ->
    world_interp W C -∗
    world_interp W C ∗
    alloc_obj ι (alloc_object_base obj) (alloc_object_end obj).
  Proof.
    iIntros (Hι) "Hworld".
    iDestruct (world_interp_open_heap_provenance W C [] with "[Hworld]")
      as "[Hworld #Hprovenance]".
    { by rewrite -open_world_interp_empty. }
    iDestruct (heap_provenance_alloc_obj with "Hprovenance") as "#Hobj"; first exact Hι.
    rewrite -open_world_interp_empty.
    iFrame "Hworld Hobj".
  Qed.

  Lemma free_world_open_list W C (lk : list LAddr) :
    NoDup lk ->
    Forall (λ k,
      heap_key_live (heap_std W) k ∧
      ∃ ρ, ρ ≠ Revoked ∧ std W !! k = Some ρ) lk ->
    world_interp W C
    ==∗
    ∃ ws,
      world_interp_open W C lk ∗
      ([∗ list] k;v ∈ lk;ws, k ↦ₖ v) ∗
      ([∗ list] k ∈ lk,
        ∃ p φ ρ,
          ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
          rel C k p φ ∗
          sts_state_std C k ρ).
  Proof.
    intros Hnodup Hstates.
    induction lk as [|k lk IH].
    - iIntros "Hworld". iModIntro. iExists [].
      rewrite open_world_interp_empty. iFrame. simpl. done.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hstates as [Hk_state Hstates].
      destruct Hk_state as [Hlive (ρ & Hnr & Hstd)].
      iIntros "Hworld".
      iMod (free_region_rel_get W C k ρ Hstd with "Hworld")
        as "[Hworld Hrel]".
      iDestruct "Hrel" as (p φ) "[%Hpers #Hrel]".
      iMod (IH Hnodup Hstates with "Hworld") as (ws)
        "(Hworld & Hmem & Hhandles)".
      rewrite world_interp_open_eq /world_interp_open_def.
      iDestruct "Hworld" as "(Hregion & Hsts & Hseal)".
      iDestruct (region_open_next W C φ lk k p ρ Hnr Hlive Hnotin
        Hstd with "[$Hregion $Hrel $Hsts]") as (v)
        "(Hsts & Hstate & Hregion & Ha & Hmono & Hφ & %HnonO)".
      iModIntro. iExists (v :: ws). simpl.
      iSplitL "Hregion Hsts Hseal".
      { iFrame. }
      iFrame "Ha Hmem Hhandles".
      iExists p, φ, ρ. iFrame "Hstate Hrel". done.
  Qed.

  (** Quarantined cells close on the [emp] branch: the world's entry for [ι]
      carries [ι ⊒ AQuar]. *)
  Lemma free_world_close_quarantined_list W C ι o (la : list Addr) :
    NoDup la ->
    heap_std W !! ι = Some o ->
    alloc_object_status o = AllocObjectQuarantined ->
    Forall (alloc_object_contains o) la ->
    world_interp_open W C ((λ a, LHeap a ι) <$> la) ∗
    ([∗ list] a ∈ la,
      ∃ p φ ρ,
        ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
        rel C (LHeap a ι) p φ ∗
        sts_state_std C (LHeap a ι) ρ)
    -∗
    world_interp W C.
  Proof.
    intros Hnodup Hι Hstatus Hcontains.
    induction la as [|a la IH].
    - iIntros "(Hworld & _)".
      by rewrite -open_world_interp_empty.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hcontains as [Ha Hcontains].
      iIntros "(Hworld & Hhandles)".
      iDestruct "Hhandles" as "[Hhandle Hhandles]".
      iDestruct "Hhandle" as (p φ ρ) "(%Hpers & #Hrel & Hstate)".
      iDestruct (close_world_interp_next_quarantined_heap W C _ a ι p φ ρ o
        with "Hworld Hrel Hstate") as "Hworld"; eauto.
      { intros Hin. apply list_elem_of_fmap in Hin as (a' & Heq & Hin).
        simplify_eq. done. }
      iApply (IH Hnodup Hcontains with "[$Hworld $Hhandles]").
  Qed.

  (** The registers outside the arguments carry no identifier at entry: the
      switcher's return sentry and the stack capability have none, and every
      other non-argument register holds zero (D23). *)
  Lemma free_entry_regs_idfree (regs : LReg) (wcsp : Word) (nargs : nat) :
    regs !! csp = Some (lword_of_word wcsp) ->
    (∀ (r : RegName) (v : LWord),
      r ∉ ({[PC; cra; cgp; csp]} ∪ dom_arg_rmap nargs : gset RegName) ->
      regs !! r = Some v -> v = WInt 0) ->
    ∀ r w, (r ∉ ({[PC; cra; cgp]} ∪ dom_arg_rmap nargs : gset RegName)) ->
      regs !! r = Some w -> has_authority w.(lw) -> w.(lprov) = None.
  Proof.
    intros Hcsp Hzeros r w Hr Hw _.
    destruct (decide (r = csp)) as [->|Hne].
    - rewrite Hcsp in Hw. by simplify_eq.
    - rewrite (Hzeros r w); [done| |exact Hw]. set_solver.
  Qed.

  (** Execute free for an arbitrary caller and update the shared heap world. *)
  Lemma free_exec_entry_point W C (Nswitcher : namespace) :
    allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
    (* Unpack the entry register map and classify the requested capability. *)
    iIntros "(#Hservice & #Hswitcher)".
    iIntros (cstk Ws Cs regs a_stk e_stk)
      "(Hcont & %Hframe & Hregister & Hrmap & Hworld & %Hsync & Hcstk & Hna)".
    rewrite /interp_conf.
    iDestruct "Hregister" as
      "(%Hfull_rmap & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_csp & Hregs)".
    iDestruct "Hregs" as "[#Hargs %Hzeros]".
    pose proof (free_entry_regs_idfree regs _ allocator_free_nargs Hcsp Hzeros)
      as Hidfree.
    rewrite /registers_pointsto.
    cbn in Hfull_rmap.
    getRegValList [PC;cgp;cra;csp;ca0;ca1;ca2;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    iExtractList "Hrmap" [PC;cgp;cra;ca0;ca1;ca2]
      as ["HPCr";"Hcgpr";"Hcrar";"Hca0";"Hca1";"Hca2"].
    iExtractList "Hrmap" [ct0;ct1;ct2;ct3;ct4;ctp;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    rewrite HwPC in HPC. injection HPC as HeqPC. subst wPC.
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    destruct wca0 as [wa0 π].
    assert (Hshape :
      (∃ p g b e a,
        wa0 = WCap true p g b e a ∧
        (heap_b < b ∧ b < e ∧ e <= heap_e)%a) ∨
      (∀ next allocations,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1)%a next allocations →
        ¬ allocator_free_valid next allocations wa0)).
    { destruct wa0 as [n|s|tag p g b e a|ot s].
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
      iExtract "Hrmap" csp as "Hcspr".
      iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
        (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      iApply (allocator_free_invalid_correct ⊤ (wa0 @@? π)
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try exact Hinvalid.
      iFrame "Hservice Hna HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
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
        (l ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) (revoke W)).
      destruct Htemps as [Hnodup Htemps].
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      iDestruct (RevokedResources_mono_pub W Wfixed C l l
        Hrelated_pub with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_int. }
      iAssert (interp Wfixed C (WInt ALLOC_INVALID))
        as "#Hinterp_status".
      { iApply interp_int. }
      iApply (switcher_ret_specification Nswitcher W (revoke W) C _
        e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
        (WInt ALLOC_INVALID) (WInt 0)
        with "[$Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
      { exact Hnodup. }
      { intros a Ha. apply Htemps in Ha. exact Ha. } }
    (* A tagged heap argument is a live capability of the object [ι] that
       the world records, whose bounds cover the argument's. *)
    destruct Hcap as (p & g & b & e & a & -> & Hbounds).
    iDestruct ("Hargs" $! ca0 (WCap true p g b e a @@? π) with "[] []")
      as "#Hinterp_ca0".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca0. }
    iDestruct (interp_cap_heap_conditions W C p g b e a π
      with "Hinterp_ca0") as %Hcapvalid.
    destruct (free_heap_cap_payload W p g b e π Hbounds Hcapvalid)
      as (ι & obj & -> & Hι & Hlive & Hbase & Hend & Hpayload).
    iDestruct (free_world_alloc_obj W C ι obj Hι with "Hworld")
      as "(Hworld & #Hobj)".
    destruct obj as [base objend objstatus].
    cbn in Hlive, Hbase, Hend, Hι |- *. subst objstatus.
    destruct (decide ((b,e)=(base,objend))) as [Hexact|Hnarrow].
    - (* Exact bounds: collect every cell of [ι] from the world and free it. *)
      injection Hexact as <- <-.
      set (lk := (λ x, LHeap x ι) <$> finz.seq_between b e).
      assert (Hpayload_keys : Forall (λ k,
          heap_key_live (heap_std W) k ∧
          ∃ ρ, ρ ≠ Revoked ∧ std W !! k = Some ρ) lk).
      { by apply Forall_fmap. }
      assert (Hlk_nodup : NoDup lk).
      { apply NoDup_fmap_2; last apply finz_seq_between_NoDup.
        intros x y Heq. by injection Heq. }
      iMod (free_world_open_list W C lk Hlk_nodup Hpayload_keys with "Hworld")
        as (ws) "(Hworld_open & Hcells & Hhandles)".
      iDestruct (big_sepL2_length _ _ _ with "Hcells") as %Hlen.
      rewrite length_fmap in Hlen.
      rewrite big_sepL2_fmap_l.
      iAssert (free_auth_held ι)%I as "Hheld".
      { rewrite /free_auth_held /free_auth_core_inst /free_auth_core /=. done. }
      set (rmap := delete cnull (delete ctp (delete ct4 (delete ct3 (delete ct2
        (delete ct1 (delete ct0 (delete ca2 (delete ca1 (delete ca0
        (delete cra (delete cgp (delete PC regs))))))))))))).
      iApply (allocator_free_valid_correct ⊤ p g ι b e a ws
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        rmap (λ v, (⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I) with "[-]");
        try solve_ndisj; try exact Hbounds; try (symmetry; exact Hlen).
      { subst rmap. apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { intros r w Hr. subst rmap. rewrite !lookup_delete_Some in Hr.
        destruct Hr as (_&_&_&_&_&_&_&_&_&Hca0&Hcra&Hcgp&HPC&Hr).
        apply (Hidfree r w); last exact Hr.
        clear -Hca0 Hcra Hcgp HPC.
        rewrite /allocator_free_nargs /dom_arg_rmap /=. set_solver. }
      iFrame "Hservice Hna Hobj Hheld HPCr Hcgpr Hcrar Hca0 Hca1 Hca2
        Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hrmap Hcells".
      iNext.
      iIntros "(Hna_post & HPCr_post & Hcgpr_post &
        Hcrar_post & Hca0_post & Hca1_post & Hca2_post & Hct0_post &
        Hct1_post & Hct2_post & Hct3_post & Hct4_post & Hctp_post &
        Hcnull_post & Hrmap & #Hq & Hlc)".
      subst rmap. iExtract "Hrmap" csp as "Hcspr".
      (* Move the world's entry for [ι] to Quarantined and close its cells. *)
      set (h' := heap_quarantine W.2 ι).
      pose proof (heap_quarantine_future W.2 ι) as Hheap_future.
      pose proof (related_sts_pub_world_heap_update W
        (heap_quarantine W.2 ι) Hheap_future) as Hrelated_W_q.
      assert (Houtside : ∀ k, k ∉ lk ->
          heap_key_status W.2 k = heap_key_status h' k).
      { intros [x|x κ] Hnotin; first done. cbn.
        destruct (decide (κ = ι)) as [->|Hne].
        - subst h'. rewrite (heap_quarantine_lookup _ _ _ Hι) Hι /=.
          rewrite /alloc_object_contains /=.
          destruct (decide (b <= x < e)%a) as [Hx|]; last done.
          exfalso. apply Hnotin. apply list_elem_of_fmap. exists x.
          split; first done. by apply elem_of_finz_seq_between.
        - subst h'. by rewrite heap_quarantine_lookup_ne. }
      assert (Hdom_l : Forall (fun k => k ∈ dom (std W)) lk).
      { eapply Forall_impl; first exact Hpayload_keys.
        intros k [_ (ρ & _ & Hstd)]. rewrite elem_of_dom. by eexists. }
      iMod (free_world_open_heap_transition_range W C lk ι
          Houtside Hdom_l with "Hq Hworld_open")
        as "Hworld_open_q".
      iAssert (world_interp (heap_std_update W h') C)
        with "[Hworld_open_q Hhandles]" as "Hworld_q".
      { iApply (free_world_close_quarantined_list
          (heap_std_update W h') C ι
          (MkAllocObject b e AllocObjectQuarantined)
          (finz.seq_between b e)
          (finz_seq_between_NoDup b e)).
        - exact (heap_quarantine_lookup _ _ _ Hι).
        - reflexivity.
        - apply Forall_forall. intros x Hx. by apply elem_of_finz_seq_between in Hx.
        - rewrite big_sepL_fmap. iFrame "Hworld_open_q Hhandles". }
      iDestruct (interp_cap_disjoint_wl W C RWL Local
        (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a None eq_refl
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
        (l ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) (revoke Wq)).
      destruct Htemps as [Hnodup Htemps].
      assert (related_sts_pub_world Wq Wfixed) as Hrelated_q_fixed.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub
        by (eapply related_sts_pub_trans_world; eauto).
      iDestruct (RevokedResources_mono_pub Wq Wfixed C l l
        Hrelated_q_fixed with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_int. }
      iApply (switcher_ret_specification Nswitcher W (revoke Wq) C _
        e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
        (WInt ALLOC_OK) (WInt 0)
        with "[$Hswitcher $Hinterp0 $Hstk $Hcstk $Hcont $Hworld_rev $Hna_post $HPCr_post $Hrevoked $Hrmap $Hca0_post $Hca1_post $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { destruct Hsync as [Hsync Heq]. rewrite <- Heq. exact Hsync. }
      { exact Hnodup. }
      { intros x Hx. apply Htemps. exact Hx. }
    - (* Narrowed bounds: a strict subrange of the allocation is rejected. *)
      iExtract "Hrmap" csp as "Hcspr".
      iMod (world_interp_revoke_stack W C (a_stk ^+ 4)%a e_stk
        (a_stk ^+ 4)%a with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      iApply (allocator_free_narrowed_spec ⊤ p g ι base objend b e a
        (WSentry true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]"); try solve_ndisj; try exact Hnarrow.
      { destruct Hbounds as (_ & Hbe & _). solve_addr. }
      iFrame "Hservice Hna Hobj HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
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
        (l ++ (LNonHeap <$> finz.seq_between (a_stk ^+ 4)%a e_stk)) (revoke W)).
      destruct Htemps as [Hnodup Htemps].
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      iDestruct (RevokedResources_mono_pub W Wfixed C l l
        Hrelated_pub with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_int. }
      iAssert (interp Wfixed C (WInt ALLOC_INVALID))
        as "#Hinterp_status".
      { iApply interp_int. }
      iApply (switcher_ret_specification Nswitcher W (revoke W) C _
        e_stk (a_stk ^+ 4)%a l stk_mem cstk Ws Cs
        (WInt ALLOC_INVALID) (WInt 0)
        with "[$Hswitcher $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
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
    allocator_service_ctx ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN allocator_exp_tblN)
      (allocator_exp_tbl_b ↦ₐ WCap true RX Global
        allocator_pcc_b allocator_pcc_e allocator_pcc_b) ∗
    inv (export_table_CGPN allocator_exp_tblN)
      ((allocator_exp_tbl_b ^+ 1)%a ↦ₐ WCap true RW Global
        allocator_cgp_b allocator_cgp_e allocator_cgp_b) ∗
    inv (export_table_entryN allocator_exp_tblN
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
    iIntros "(#Hservice & #Hswitcher & #HPCC & #HCGP & #Hentry & #Hsealed & #Hsealed_local)".
    iExists g_allocator_exp_tbl, allocator_exp_tbl_b, allocator_exp_tbl_e,
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a,
      allocator_pcc_b, allocator_pcc_e, allocator_cgp_b, allocator_cgp_e,
      allocator_free_nargs, allocator_free_pcc_off, allocator_exp_tblN.
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
