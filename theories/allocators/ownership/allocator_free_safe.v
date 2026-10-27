From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher_base switcher_base_ktk.
From griotte Require Import register_tactics map_simpl.
From griotte Require Import world_interp_stack model_interp_stack.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.allocators.ownership Require Import allocator_header_spec.
From griotte.allocators.common Require Import allocator_common_safe.
From griotte.allocators.ownership Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec allocator_otype.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {allocator_ownerg : allocatorOwnerG Σ}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** The safe [free] runs with the ownership layer's [FreeAuth] instance:
      the right to free an object is held by the sealing predicate of its
      owner's allocator capability. *)
  #[local] Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  (** Open the cells of [lk] in the region, with the standard states held
      separately (the sealing map may be open). *)
  Lemma free_region_open_list W C (lk : list LAddr) :
    NoDup lk ->
    Forall (λ k,
      heap_key_live (heap_std W) k ∧
      ∃ ρ, ρ ≠ Revoked ∧ std W !! k = Some ρ) lk ->
    region W C ∗ sts_full_world W C
    ==∗
    ∃ ws,
      open_region_many W C lk ∗
      sts_full_world W C ∗
      ([∗ list] k;v ∈ lk;ws, k ↦ₖ v) ∗
      ([∗ list] k ∈ lk,
        ∃ p φ ρ,
          ⌜∀ WCv, Persistent (φ WCv)⌝ ∗
          rel C k p φ ∗
          sts_state_std C k ρ).
  Proof.
    intros Hnodup Hstates.
    induction lk as [|k lk IH].
    - iIntros "[Hregion Hsts]". iModIntro. iExists [].
      rewrite -region_open_nil. iFrame. simpl. done.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hstates as [Hk_state Hstates].
      destruct Hk_state as [Hlive (ρ & Hnr & Hstd)].
      iIntros "[Hregion Hsts]".
      iMod (region_rel_get_state W C k ρ Hstd with "[$Hregion $Hsts]")
        as "(Hregion & Hsts & Hrel)".
      iDestruct "Hrel" as (p φ) "[%Hpers #Hrel]".
      iMod (IH Hnodup Hstates with "[$Hregion $Hsts]") as (ws)
        "(Hregion & Hsts & Hmem & Hhandles)".
      iDestruct (region_open_next W C φ lk k p ρ Hnr Hlive Hnotin
        Hstd with "[$Hregion $Hrel $Hsts]") as (v)
        "(Hsts & Hstate & Hregion & Ha & Hmono & Hφ & %HnonO)".
      iModIntro. iExists (v :: ws). simpl.
      iFrame "Hregion Hsts Ha Hmem Hhandles".
      iExists p, φ, ρ. iFrame "Hstate Hrel". done.
  Qed.

  (** Execute free for an arbitrary caller and update the shared heap world. *)
  Lemma free_exec_entry_point W C :
    allocator_pcc_b ≠ b_switcher ->
    allocator_service_ctx ∗
    allocator_service_static ∗
    seal_pred AllocOtype allocator_otype_propC ∗
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    no_handler allocator_exp_tbl_b ⊢
    execute_entry_point allocator_exp_tbl_b
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs allocator_free_min_stack W C.
  Proof.
    (* Unpack the entry register map and classify the requested capability. *)
    iIntros (Hpc_b)
      "(#Hservice & #Hstatic & #Hspred & #Hswitcher & #Hswitcher_static & #Hno_handler)".
    iIntros (cstk Ws Cs regs b_stk e_stk)
      "(Hcont & %Hframe & %Htop_tbl & HPCr & Hregister & Hrmap & Hworld & %Hsync & _ &
        Hcstk & Hna)".
    rewrite /interp_conf.
    iDestruct "Hregister" as
      "(%Hfull_rmap & %Hcgp & [%mie %Hcra] & %Hcsp & #Hinterp_csp & Hregs)".
    iDestruct "Hregs" as "[#Hargs %Hzeros]".
    pose proof (free_entry_regs_idfree regs _ allocator_free_nargs Hcsp Hzeros)
      as Hidfree.
    rewrite /registers_pointsto.
    cbn in Hfull_rmap.
    getRegValList [cgp;cra;csp;ca0;ca1;ca2;ct0;ct1;ct2;ca3;ca4;ctp;cnull].
    iExtractList "Hrmap" [cgp;cra;ca0;ca1;ca2]
      as ["Hcgpr";"Hcrar";"Hca0";"Hca1";"Hca2"].
    iExtractList "Hrmap" [ct0;ct1;ct2;ca3;ca4;ctp;cnull]
      as ["Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    (* A malformed allocator capability traps in the owner block. *)
    destruct (get_tag wca0.(lw) && is_sealed_with_o wca0.(lw) AllocOtype) eqn:Hcap_valid;
      cycle 1.
    { iApply (allocator_free_invalid_capability_spec ⊤ ⊤ wca0
        with "[- $Hstatic $Hna $HPCr $Hca0 $Hctp $Hct3 $Hct4]");
        [ solve_ndisj
        | apply andb_false_iff in Hcap_valid as [Hnot_tagged|Hnot_sealed];
          [right; exact Hnot_tagged | left; exact Hnot_sealed] |].
      iIntros (a Ha) "(Hna & [%wctp' Hctp] & Hca0 & [%wct3' Hct3] & [%wct4' Hct4])".
      (* Unwind to the caller: nothing was revoked or changed yet. *)
      iInsertRegs "Hrmap" ["Hcgpr";"Hcrar";"Hca0";"Hca1";"Hca2";
                           "Hct0";"Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
      iApply (trap_safe_unwind_logrel with "Hswitcher Hswitcher_static [] [-]");
        [|exact Hframe| | |]; cycle 1.
      { (* The fault is outside the switcher's code: it is not resumed *)
        by apply trap_no_resume_cap. }
      { (* The allocator's table declares no handler *)
        iRight. destruct Htop_tbl as (_ & -> & _ & Htbl_ok). iFrame "Hno_handler".
        iPureIntro. by apply tf_export_tbl_ok_nonzero. }
      { iModIntro. iFrame. }
      intros r. destruct (Hfull_rmap r) as [wr Hwr].
      rewrite !lookup_insert_is_Some' !lookup_delete_is_Some.
      repeat (match goal with |- ?r' = r ∨ _ =>
        destruct (decide (r' = r)); [by left | right] end).
      repeat split; by eauto. }
    apply andb_true_iff in Hcap_valid as [Hwca0_tag Hwca0_sealed].
    iDestruct ("Hargs" $! ca0 wca0 with "[] []") as "#Hinterp_ca0".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca0. }
    rewrite Hwcgp in Hcgp. injection Hcgp as Heqcgp. subst wcgp.
    rewrite Hwcra in Hcra. injection Hcra as Heqcra. subst wcra.
    rewrite Hwcsp in Hcsp. injection Hcsp as Heqcsp. subst wcsp.
    destruct wca1 as [wa1 π].
    assert (Hshape :
      (∃ p g b e a,
        wa1 = WCap true p g b e a ∧
        (heap_b < b ∧ b < e ∧ e <= heap_e)%a) ∨
      (∀ next allocations o,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1)%a next allocations →
        ¬ allocator_free_valid next allocations o wa1)).
    { destruct wa1 as [n|s|tag p g b e a|ot s].
      - right. intros next allocations o _ _ (p & g & b & e & a & Hcap & _).
        discriminate Hcap.
      - destruct s as [tag p g b e a|tag p g b e a].
        + destruct tag.
          * destruct (decide (heap_b < b ∧ b < e ∧ e <= heap_e)%a)
              as [Hbounds|Hbad].
            -- left. exists p,g,b,e,a. split; [reflexivity|exact Hbounds].
            -- right. intros next allocations o Hnext _
                 (p' & g' & b' & e' & a' & Hcap & Hrange & _).
               inversion Hcap; subst. apply Hbad. destruct Hnext.
               destruct Hrange as (Hbb & Hbe & Hen).
               repeat split; solve_addr.
          * right. intros next allocations o _ _ (p' & g' & b' & e' & a' & Hcap & _).
            discriminate Hcap.
        + right. intros next allocations o _ _ (p' & g' & b' & e' & a' & Hcap & _).
          discriminate Hcap.
      - right. intros next allocations o _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap.
      - right. intros next allocations o _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap. }
    destruct Hshape as [Hcap|Hinvalid].
    2: {
      iExtract "Hrmap" csp as "Hcspr".
      iMod (world_interp_revoke_stack W C b_stk e_stk
        (stk_start_a b_stk e_stk) with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      (* Take the owner word and token out of the sealing predicate. *)
      iMod (allocator_otype_open W (revoke W) C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hclose)".
      iApply (allocator_free_invalid_correct ⊤ ⊤ g_owner a_owner id (wa1 @@? π)
        (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]");
        [ intros next allocations Hnext Hchain; exact (Hinvalid next allocations id Hnext Hchain)
        | solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner
        | apply jalr_target_ok_switcher_return_sentry |].
      iFrame "Hservice Hstatic Hna Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iNext.
      iIntros "(Hna & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
      (* Close the sealing predicate of the allocator capability. *)
      iDestruct ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights]") as "Hworld".
      iDestruct "Hstack_mem" as (stk_mem) "Hstk".
      iDestruct "Hca2" as (wca2') "Hca2".
      iDestruct "Hct0" as (wct0') "Hct0".
      iDestruct "Hct1" as (wct1') "Hct1".
      iDestruct "Hct2" as (wct2') "Hct2".
      iDestruct "Hct3" as (wct3') "Hct3".
      iDestruct "Hct4" as (wct4') "Hct4".
      iDestruct "Hctp" as (wctp') "Hctp".
      iInsertList "Hrmap" [cnull;ctp;ca4;ca3;ct2;ct1;ct0;ca2;cra;cgp].
      set (Wfixed := close_list
        (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W)).
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
      iApply (switcher_ret_specification W (revoke W) C _
        e_stk b_stk l stk_mem cstk Ws Cs
        (WInt ALLOC_INVALID) (WInt 0)
        with "[$Hswitcher $Hswitcher_static $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { exact Hsync. }
      { exact Hnodup. }
      { intros a Ha. apply Htemps in Ha. exact Ha. } }
    (* A tagged heap argument is a live capability of the object [ι] that
       the world records, whose bounds cover the argument's. *)
    destruct Hcap as (p & g & b & e & a & -> & Hbounds).
    iDestruct ("Hargs" $! ca1 (WCap true p g b e a @@? π) with "[] []")
      as "#Hinterp_ca1".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca1. }
    iDestruct (interp_cap_heap_conditions W C p g b e a π
      with "Hinterp_ca1") as %Hcapvalid.
    destruct (free_heap_cap_payload W p g b e π Hbounds Hcapvalid)
      as (ι & obj & -> & Hι & Hlive & Hbase & Hend & Hpayload).
    iDestruct (free_world_alloc_obj W C ι obj Hι with "Hworld")
      as "(Hworld & #Hobj)".
    destruct obj as [base objend objstatus].
    cbn in Hlive, Hbase, Hend, Hι |- *. subst objstatus.
    destruct (decide ((b,e)=(base,objend))) as [Hexact|Hnarrow].
    - (* Exact bounds: the owner set of the allocator capability decides. *)
      injection Hexact as <- <-.
      set (lk := (λ x, LHeap x ι) <$> finz.seq_between b e).
      assert (Hpayload_keys : Forall (λ k,
          heap_key_live (heap_std W) k ∧
          ∃ ρ, ρ ≠ Revoked ∧ std W !! k = Some ρ) lk).
      { by apply Forall_fmap. }
      assert (Hlk_nodup : NoDup lk).
      { apply NoDup_fmap_2; last apply finz_seq_between_NoDup.
        intros x y Heq. by injection Heq. }
      (* Take the owner word and token out of the sealing predicate, keeping
         the region available to open the payload. *)
      iMod (allocator_otype_sopen W W C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hregion & Hsts & Hclose)".
      destruct (decide (ι ∈ Ω)) as [HιΩ|HιΩ]; cycle 1.
      { (* The object belongs to another owner and is not freed. *)
        iExtract "Hrmap" csp as "Hcspr".
        iMod (monotone_revoke_stack W C b_stk e_stk (stk_start_a b_stk e_stk)
          with "[$Hinterp_csp $Hsts $Hregion]") as (l)
          "(%Htemps & Hsts & Hregion & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
        iApply (allocator_free_wrong_owner_spec ⊤ ⊤ g_owner a_owner id Ω p g ι b e a
          (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)
          with "[-]");
          [ solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner | exact HιΩ
          | apply jalr_target_ok_switcher_return_sentry |].
        iFrame "Hservice Hstatic Hna Hid Hobj Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
        iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
        iNext.
        iIntros "(Hna & Hid & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
        (* Close the sealing predicate in the revoked world. *)
        iDestruct ("Hclose" $! (revoke W) [] Ω
          with "[] [] [$Hsts $Ha_owner $Hid $Hrights Hregion]") as "Hworld".
        { done. }
        { iPureIntro. apply revoke_related_sts_priv_world. }
        { by rewrite -region_open_nil. }
        iEval (rewrite -open_world_interp_empty) in "Hworld".
        iDestruct "Hstack_mem" as (stk_mem) "Hstk".
        iDestruct "Hca2" as (wca2') "Hca2".
        iDestruct "Hct0" as (wct0') "Hct0".
        iDestruct "Hct1" as (wct1') "Hct1".
        iDestruct "Hct2" as (wct2') "Hct2".
        iDestruct "Hct3" as (wct3') "Hct3".
        iDestruct "Hct4" as (wct4') "Hct4".
        iDestruct "Hctp" as (wctp') "Hctp".
        iInsertList "Hrmap" [cnull;ctp;ca4;ca3;ct2;ct1;ct0;ca2;cra;cgp].
        set (Wfixed := close_list
          (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W)).
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
        iApply (switcher_ret_specification W (revoke W) C _
          e_stk b_stk l stk_mem cstk Ws Cs
          (WInt ALLOC_INVALID) (WInt 0)
          with "[$Hswitcher $Hswitcher_static $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
        { exact Hrelated_pub. }
        { apply lregmap_full_dom in Hfull_rmap.
          repeat rewrite dom_insert_L.
          repeat rewrite dom_delete_L.
          rewrite Hfull_rmap. set_solver+. }
        { exact Hframe. }
        { exact Hsync. }
        { exact Hnodup. }
        { intros x Hx. apply Htemps in Hx. exact Hx. } }
      (* Accept: collect every cell of [ι] from the world and free it. *)
      iMod (free_region_open_list W C lk Hlk_nodup Hpayload_keys
        with "[$Hregion $Hsts]")
        as (ws) "(Hregion & Hsts & Hcells & Hhandles)".
      iDestruct (big_sepL2_length _ _ _ with "Hcells") as %Hlen.
      rewrite length_fmap in Hlen.
      rewrite big_sepL2_fmap_l.
      (* The sealing predicate holds the right to free the live object: a
         quarantine witness is refuted by any cell. *)
      iDestruct (allocator_owned_rights_delete with "Hrights")
        as "[Hright Hrights]"; first exact HιΩ.
      iDestruct "Hright" as "[#Hq_old|Hright]".
      { iExFalso.
        assert (finz.seq_between b e = b :: finz.seq_between (b ^+ 1)%a e) as Hseq.
        { apply finz_seq_between_cons. destruct Hbounds as (_ & ? & _). solve_addr. }
        iEval (rewrite Hseq) in "Hcells".
        iDestruct (big_sepL2_cons_inv_l with "Hcells") as (w0 ws' ->) "[Hc _]".
        iApply (heap_pointsto_quar_false with "Hc Hq_old"). }
      iAssert (free_auth_held ι)%I with "[Hright]" as "Hheld".
      { rewrite /free_auth_held /free_auth_owner_inst /free_auth_owner /=. done. }
      set (rmap := delete cnull (delete ctp (delete ca4 (delete ca3 (delete ct2
        (delete ct1 (delete ct0 (delete ca2 (delete ca1 (delete ca0
        (delete cra (delete cgp regs)))))))))))).
      (* MTDC, for the quarantine, from the switcher invariant. *)
      iMod (na_inv_acc with "Hswitcher Hna") as "(Hsw & Hna & Hsw_close)";
        [solve_ndisj|solve_ndisj|].
      iDestruct "Hsw" as (a_tstk cstk' save_area tstk_next) "[>Hmtdc Hsw]".
      iApply (allocator_free_valid_correct ⊤ (⊤ ∖ ↑Nswitcher) g_owner a_owner id Ω p g ι b e a ws
        (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)
        (WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack) rmap
        (HO th) with "[-]");
        [ solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner | exact HιΩ
        | exact Hbounds | symmetry; exact Hlen | | | intros _; reflexivity
        | intros _; reflexivity | apply jalr_target_ok_switcher_return_sentry |].
      { subst rmap. apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { intros r w Hr. subst rmap. rewrite !lookup_delete_Some in Hr.
        destruct Hr as (_&_&_&_&_&_&_&_&Hca1&Hca0&Hcra&Hcgp&Hr).
        apply (Hidfree r w); last exact Hr.
        clear -Hca1 Hca0 Hcra Hcgp.
        rewrite /allocator_free_nargs /dom_arg_rmap /=. set_solver. }
      iFrame "Hservice Hstatic Hna Hid Ha_owner Hobj Hheld HPCr Hcgpr Hcrar Hca0 Hca1 Hca2
        Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hrmap Hmtdc Hcells".
      iNext.
      iIntros "(Hna_post & Hid & Ha_owner & HPCr_post & Hcgpr_post &
        Hcrar_post & Hca0_post & Hca1_post & Hca2_post & Hct0_post &
        Hct1_post & Hct2_post & Hct3_post & Hct4_post & Hctp_post &
        Hrmap & Hmtdc & #Hq & Hlc)".
      iMod ("Hsw_close" with "[$Hna_post Hmtdc Hsw]") as "Hna_post".
      { iNext. iExists a_tstk, cstk', save_area, tstk_next. iFrame. }
      subst rmap. iExtract "Hrmap" csp as "Hcspr".
      (* Move the world's entry for [ι] to Quarantined. *)
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
      iMod (free_region_open_heap_transition_range W C lk ι
          Houtside Hdom_l with "Hq [$Hregion $Hsts]")
        as "[Hregion Hsts]".
      (* Close the sealing predicate in the quarantined world: the right to
         free [ι] is replaced by [ι ⊒ AQuar]. *)
      iDestruct ("Hclose" $! (heap_std_update W h') lk Ω
        with "[] [] [$Hregion $Hsts $Ha_owner $Hid Hrights]")
        as "Hworld_open_q".
      { done. }
      { iPureIntro. by apply related_sts_pub_priv_world. }
      { iApply (allocator_owned_rights_delete _ _ HιΩ). iFrame "Hrights".
        iLeft. iExact "Hq". }
      (* Close the cells' regions on the quarantined branch. *)
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
        b_stk e_stk (stk_start_a b_stk e_stk) None eq_refl
        with "Hinterp_csp") as %[_ Hstack_disjoint].
      iAssert (interp (heap_std_update W h') C
        (WCap true RWL Local b_stk e_stk (stk_start_a b_stk e_stk)))
        with "[Hinterp_csp]" as "Hinterp_csp_q".
      { iApply (monotone.interp_monotone_cap_nonheap
          W (heap_std_update W h') C true RWL Local
          b_stk e_stk (stk_start_a b_stk e_stk)
          Hstack_disjoint Hrelated_W_q).
        iExact "Hinterp_csp". }
      iMod (world_interp_revoke_stack (heap_std_update W h') C
          b_stk e_stk (stk_start_a b_stk e_stk)
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
      iInsertList "Hrmap" [cnull;ctp;ca4;ca3;ct2;ct1;ct0;ca2;cra;cgp].
      set (Wq := heap_std_update W h').
      set (Wfixed := close_list
        (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke Wq)).
      destruct Htemps as [Hnodup Htemps].
      assert (related_sts_pub_world Wq Wfixed) as Hrelated_q_fixed.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub
        by (eapply related_sts_pub_trans_world; eauto).
      iDestruct (RevokedResources_mono_pub Wq Wfixed C l l
        Hrelated_q_fixed with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_int. }
      iApply (switcher_ret_specification W (revoke Wq) C _
        e_stk b_stk l stk_mem cstk Ws Cs
        (WInt ALLOC_OK) (WInt 0)
        with "[$Hswitcher $Hswitcher_static $Hinterp0 $Hstk $Hcstk $Hcont $Hworld_rev $Hna_post $HPCr_post $Hrevoked $Hrmap $Hca0_post $Hca1_post $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { exact Hsync. }
      { exact Hnodup. }
      { intros x Hx. apply Htemps. exact Hx. }
    - (* Narrowed bounds: a strict subrange of the allocation is rejected. *)
      iExtract "Hrmap" csp as "Hcspr".
      iMod (world_interp_revoke_stack W C b_stk e_stk
        (stk_start_a b_stk e_stk) with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      (* Take the owner word and token out of the sealing predicate. *)
      iMod (allocator_otype_open W (revoke W) C wca0 Hwca0_tag Hwca0_sealed
        with "Hspred Hinterp_ca0 Hworld")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hclose)".
      iApply (allocator_free_narrowed_spec ⊤ ⊤ g_owner a_owner id p g ι base objend b e a
        (WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]");
        [ destruct Hbounds as (_ & Hbe & _); solve_addr | exact Hnarrow | solve_ndisj | solve_ndisj
        | exact Hshadow_owner | exact Hbounds_owner
        | apply jalr_target_ok_switcher_return_sentry |].
      iFrame "Hservice Hstatic Hna Hobj Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iNext.
      iIntros "(Hna & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
      (* Close the sealing predicate of the allocator capability. *)
      iDestruct ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights]") as "Hworld".
      iDestruct "Hstack_mem" as (stk_mem) "Hstk".
      iDestruct "Hca2" as (wca2') "Hca2".
      iDestruct "Hct0" as (wct0') "Hct0".
      iDestruct "Hct1" as (wct1') "Hct1".
      iDestruct "Hct2" as (wct2') "Hct2".
      iDestruct "Hct3" as (wct3') "Hct3".
      iDestruct "Hct4" as (wct4') "Hct4".
      iDestruct "Hctp" as (wctp') "Hctp".
      iInsertList "Hrmap" [cnull;ctp;ca4;ca3;ct2;ct1;ct0;ca2;cra;cgp].
      set (Wfixed := close_list
        (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W)).
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
      iApply (switcher_ret_specification W (revoke W) C _
        e_stk b_stk l stk_mem cstk Ws Cs
        (WInt ALLOC_INVALID) (WInt 0)
        with "[$Hswitcher $Hswitcher_static $Hinterp0 $Hinterp_status $Hstk $Hcstk $Hcont $Hworld $Hna $HPCr $Hrevoked $Hrmap $Hca0 $Hca1 $Hcspr]").
      { exact Hrelated_pub. }
      { apply lregmap_full_dom in Hfull_rmap.
        repeat rewrite dom_insert_L.
        repeat rewrite dom_delete_L.
        rewrite Hfull_rmap. set_solver+. }
      { exact Hframe. }
      { exact Hsync. }
      { exact Hnodup. }
      { intros x Hx. apply Htemps in Hx. exact Hx. }
  Qed.


  Lemma free_entry_point_spec
    (g_allocator_exp_tbl : Locality)
    (W : WORLD)
    (C : CmptName) :
    allocator_pcc_b ≠ b_switcher ->
    let a_alloc_exp_tbl_cgp := (allocator_exp_tbl_b ^+ ExportTable_offset_cgp)%a in
    let a_alloc_entry_free := (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a in
    allocator_service_ctx ∗
    allocator_service_static ∗
    seal_pred AllocOtype allocator_otype_propC ∗
    na_inv (tpool th) Nswitcher switcher_inv ∗
    switcher_static ∗
    allocator_exp_tbl_b ↦ₐ□ WCap true RX Global
      allocator_pcc_b allocator_pcc_e allocator_pcc_b ∗
    a_alloc_exp_tbl_cgp ↦ₐ□ WCap true RW Global
      allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    no_handler allocator_exp_tbl_b ∗
    a_alloc_entry_free ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
        allocator_free_pcc_off) -∗
    ot_switcher_prop W C
      (WCap true RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        a_alloc_entry_free).
  Proof.
    intros Hpc_b a_alloc_exp_tbl_cgp a_alloc_entry_free.
    subst a_alloc_exp_tbl_cgp a_alloc_entry_free.
    iIntros "(#Hservice & #Hstatic & #Hspred & #Hswitcher & #Hswitcher_static & #HPCC & #HCGP &
      [#Heh #Hehs] & #Hentry)".
    iExists g_allocator_exp_tbl, allocator_exp_tbl_b, allocator_exp_tbl_e,
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off)%a,
      allocator_pcc_b, allocator_pcc_e, allocator_cgp_b, allocator_cgp_e,
      allocator_free_nargs, allocator_free_min_stack, allocator_free_pcc_off.
    iFrame "#".
    iSplit; first done.
    iSplit.
    { iPureIntro. pose proof allocator_regions_disjoint as Hregions.
      rewrite !disjoint_list_cons in Hregions. cbn [union_list] in Hregions.
      rewrite /disjoint_from_shadow. set_solver+Hregions. }
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off /allocator_entry_free in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries in Hsize; solve_addr).
    iSplit; first (iPureIntro; pose proof allocator_size_exports as Hsize;
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off /allocator_entry_free in Hsize |- *;
      solve_addr).
    iSplit; first (iPureIntro; rewrite /allocator_free_nargs; lia).
    iSplit; first (iPureIntro; rewrite /allocator_free_min_stack; lia).
    iSplit; first (iPureIntro; pose proof allocator_size_imports as Himports;
      pose proof allocator_size_code as Hcode;
      rewrite /allocator_code length_app in Hcode;
      rewrite allocator_free_pcc_off_eq /allocator_malloc_pcc_off in Hcode |- *;
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
      rewrite /allocator_export_table_entries /allocator_free_exp_tbl_off /allocator_entry_free in Hsize |- *;
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
    iAssert (no_handler allocator_exp_tbl_b) as "#Hno_handler"; first iFrame "Heh Hehs".
    iApply (free_exec_entry_point W' C Hpc_b).
    iFrame "#".
  Qed.

End Heap_Temporal_Safety_Interp.
