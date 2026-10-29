From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher_base switcher_base_ktk.
From griotte Require Import register_tactics map_simpl rules_registry.
From griotte Require Import world_interp_stack wp_rules_interp.
From griotte.allocators.ownership Require Import allocator allocator_preamble.
From griotte.allocators.ownership Require Import allocator_header_spec.
From griotte.allocators.common Require Import allocator_common_safe.
From griotte.allocators.ownership Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec allocator_otype.

Section Heap_Temporal_Safety_Interp.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {allocator_ownerg : allocatorOwnerG Σ}
    {allocator_otypeg : allocatorOtypeG Σ}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}
  .

  (** The safe [free] runs with the ownership layer's [FreeAuth] instance:
      the right to free an object is held by the registry entry of its
      owner's allocator capability. *)
  #[local] Instance free_auth_owner_inst : FreeAuth Σ := free_auth_owner.

  (** Open the cells of [lk], keys of the object [ι], in the world. A live
      status share of [ι] refutes their tombstones, and a Global region of a
      key that is also Temporary. *)
  Lemma free_region_open_list W C g ι q (lk : list LAddr) :
    NoDup lk ->
    Forall (λ k, ∃ x, k = LHeap x ι) lk ->
    ι ↦st{q} ALive -∗
    ([∗ list] k ∈ lk, heap_cap_O_key W C g k) -∗
    world_interp W C -∗
    ◇ ∃ ws,
      ι ↦st{q} ALive ∗
      world_interp_open W C lk ∗
      ([∗ list] k;v ∈ lk;ws, k ↦ₖ v) ∗
      ([∗ list] k ∈ lk, region_key W C k).
  Proof.
    intros Hnodup Hkeys.
    induction lk as [|k lk IH].
    - iIntros "Hst _ Hworld". iModIntro. iExists [].
      rewrite -open_world_interp_empty. iFrame. cbn. done.
    - apply NoDup_cons in Hnodup as [Hnotin Hnodup].
      apply Forall_cons in Hkeys as [ [x ->] Hkeys].
      iIntros "Hst [#Hcov Hcovs] Hworld".
      iMod (IH Hnodup Hkeys with "Hst Hcovs Hworld") as (ws) "(Hst & Hworld & Hmem & Hkeys)".
      iAssert (◇ (world_interp_open W C ({[LHeap x ι]} ∪ lk) ∗ ι ↦st{q} ALive ∗
                 (∃ v, LHeap x ι ↦ₖ v) ∗ region_key W C (LHeap x ι)))%I
        with "[Hst Hworld]" as ">(Hworld & Hst & [%v Ha] & Hkey)".
      { iDestruct "Hcov" as "[(%p & %φ & %Hpers & #Hrel) | Hloc]".
        - destruct (decide (std W !! LHeap x ι = Some Temporary)) as [HT|HnT].
          + iDestruct (world_interp_open_rel_g_temporary with "Hworld Hrel")
              as "[_ (%a' & %ι' & %Hk & #Hq)]"; [done|done|].
            injection Hk as <- <-.
            iDestruct (live_quar_false with "Hst Hq") as "[]".
          + iDestruct (open_world_interp_permanent with "Hworld Hrel")
              as "[Hworld Hres]"; [done|done|].
            iDestruct (heap_key_resource_live with "Hst Hres") as "[Hres Hst]".
            iDestruct "Hres" as (v) "(>%HpO & >Ha & _)".
            iModIntro. iFrame "Hworld Hst". iSplitL "Ha"; first by iExists v.
            iRight. iExists p, φ. by iFrame "Hrel %".
        - destruct g; [by iDestruct "Hloc" as "[]"|].
          iDestruct "Hloc" as (p φ Hpers) "(#Hrel & %HT)".
          iDestruct (open_world_interp_temporary with "Hworld Hrel")
            as "[Hworld Hres]"; [done|done|].
          iDestruct (heap_key_resource_live with "Hst Hres") as "[Hres Hst]".
          iDestruct "Hres" as (v) "(>%HpO & >Ha & _)".
          iModIntro. iFrame "Hworld Hst". iSplitL "Ha"; first by iExists v.
          iLeft. iExists p, φ. by iFrame "Hrel %". }
      iModIntro. iExists (v :: ws). cbn. iFrame "Hst Ha Hmem Hkey Hkeys Hworld".
  Qed.

  (** Execute free for an arbitrary caller and update the shared heap world. *)
  Lemma free_exec_entry_point W C :
    allocator_pcc_b ≠ b_switcher ->
    allocator_service_ctx ∗
    allocator_service_static ∗
    allocator_otype_registry ∗
    AllocOtype ↪ₒ{SealGlobal} allocator_otype_propC ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    no_handler allocator_exp_tbl_b ⊢
    execute_entry_point allocator_exp_tbl_b
      (Cap RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs allocator_free_min_stack W C.
  Proof.
    (* Unpack the entry register map and classify the requested capability. *)
    iIntros (Hpc_b)
      "(#Hservice & #Hstatic & #Hreg & #Hspred & #Hswitcher & #Hswitcher_static & #Hno_handler)".
    iIntros (cstk Ws Cs regs b_stk e_stk)
      "(Hcont & %Hframe & %Htop_tbl & HPCr & Hregister & Hrmap & Hworld & %Hsync & _ &
        Hcstk & Hna)".
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
        wa1 = Cap p g b e a ∧
        (heap_b < b ∧ b < e ∧ e <= heap_e)%a) ∨
      (∀ next allocations o,
        (heap_b < next ∧ next <= heap_e)%a →
        allocator_chain (heap_b ^+ 1) next allocations →
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
    (* Rejecting a request that is not a valid argument of [free]: the
       world is revoked around the return, and nothing else changes. *)
    iAssert (∀ wreq : LWord,
      ⌜∀ next allocations o, (heap_b < next ∧ next <= heap_e)%a →
         allocator_chain (heap_b ^+ 1) next allocations →
         ¬ allocator_free_valid next allocations o wreq.(lw)⌝ -∗
      interp_continuation cstk Ws Cs -∗
      PC ↦ₚ[th] Cap RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr -∗
      world_interp W C -∗
      ◯(CSTK)[th] cstk -∗
      na_own (tpool th) ⊤ -∗
      cgp ↦ᵣ[th] (Cap RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b @@? None) -∗
      cra ↦ᵣ[th] (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return
                    @@? None) -∗
      ca0 ↦ᵣ[th] wca0 -∗
      ca1 ↦ᵣ[th] wreq -∗
      ca2 ↦ᵣ[th] wca2 -∗
      ct0 ↦ᵣ[th] wct0 -∗
      ct1 ↦ᵣ[th] wct1 -∗
      ct2 ↦ᵣ[th] wct2 -∗
      ca3 ↦ᵣ[th] wca3 -∗
      ca4 ↦ᵣ[th] wca4 -∗
      ctp ↦ᵣ[th] wctp -∗
      cnull ↦ᵣ[th] wcnull -∗
      regs[th] (delete cnull (delete ctp (delete ca4 (delete ca3 (delete ct2
        (delete ct1 (delete ct0 (delete ca2 (delete ca1 (delete ca0
        (delete cra (delete cgp regs)))))))))))) -∗
      safe[th])%I with "[]" as "Hreject".
    { iIntros (wreq Hinvalid) "Hcont HPCr Hworld Hcstk Hna Hcgpr Hcrar Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hrmap".
      iExtract "Hrmap" csp as "Hcspr".
      iMod (world_interp_revoke_stack W C b_stk e_stk
        (stk_start_a b_stk e_stk) with "[$Hinterp_csp $Hworld]") as (l)
        "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
      (* Take the owner word and token out of the registry. *)
      iMod (allocator_otype_acc ⊤ ⊤ W C wca0 with "Hreg Hspred Hinterp_ca0 Hna")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hna & Hclose)";
        [solve_ndisj | solve_ndisj | done | done |].
      iApply (allocator_free_invalid_correct ⊤ (⊤ ∖ ↑Nallocator_otype) g_owner a_owner id wreq
        (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]");
        [ intros next allocations Hnext Hchain; exact (Hinvalid next allocations id Hnext Hchain)
        | solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner
        | apply jalr_target_ok_switcher_return_sentry |].
      iFrame "Hservice Hstatic Hna Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iNext.
      iIntros "(Hna & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
      (* Close the registry. *)
      iMod ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights $Hna]") as "Hna".
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
      { intros a Ha. apply Htemps in Ha. exact Ha. }
    }
    destruct Hshape as [Hcap|Hinvalid].
    2: { iApply ("Hreject" $! (wa1 @@? π) with "[%] Hcont HPCr Hworld Hcstk Hna Hcgpr Hcrar Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hrmap").
         exact Hinvalid. }
    (* A tagged heap argument is a capability of the object [ι] that the
       registry records, whose bounds cover the argument's. *)
    destruct Hcap as (p & g & b & e & a & -> & Hbounds).
    iDestruct ("Hargs" $! ca1 (Cap p g b e a @@? π) with "[] []")
      as "#Hinterp_ca1".
    { iPureIntro. rewrite /allocator_free_nargs /dom_arg_rmap. set_solver. }
    { iPureIntro. exact Hwca1. }
    iDestruct (interp_cap_heap_conditions W C p g b e a π
      with "Hinterp_ca1") as "#Hcapvalid".
    iDestruct (free_heap_cap_payload W C p g b e π Hbounds with "Hcapvalid")
      as (ι base objend) "(-> & #Hobj & [%Hbase %Hend] & #Hcov)".
    destruct (decide ((b,e)=(base,objend))) as [Hexact|Hnarrow].
    - (* Exact bounds: the owner set of the allocator capability decides. *)
      injection Hexact as <- <-.
      set (lk := (λ x, LHeap x ι) <$> finz.seq_between b e).
      assert (Hpayload_keys : Forall (λ k, ∃ x, k = LHeap x ι) lk).
      { apply Forall_fmap, Forall_forall. intros x _. by exists x. }
      assert (Hlk_nodup : NoDup lk).
      { apply NoDup_fmap_2; last apply finz_seq_between_NoDup.
        intros x y Heq. by injection Heq. }
      (* Take the owner word and token out of the registry. *)
      iMod (allocator_otype_acc ⊤ ⊤ W C wca0 with "Hreg Hspred Hinterp_ca0 Hna")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hna & Hclose)";
        [solve_ndisj | solve_ndisj | done | done |].
      destruct (decide (ι ∈ Ω)) as [HιΩ|HιΩ]; cycle 1.
      { (* The object belongs to another owner and is not freed. *)
        iExtract "Hrmap" csp as "Hcspr".
        iMod (world_interp_revoke_stack W C b_stk e_stk (stk_start_a b_stk e_stk)
          with "[$Hinterp_csp $Hworld]") as (l)
          "(%Htemps & Hworld & Hstack_revoked & Hstack_forall & Hstack_mem & Hrevoked & %Hrevoked_forall)".
        iApply (allocator_free_wrong_owner_spec ⊤ (⊤ ∖ ↑Nallocator_otype) g_owner a_owner id Ω p g ι b e a
          (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return)
          with "[-]");
          [ solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner | exact HιΩ
          | apply jalr_target_ok_switcher_return_sentry |].
        iFrame "Hservice Hstatic Hna Hid Hobj Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
        iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
        iNext.
        iIntros "(Hna & Hid & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
        (* Close the registry. *)
        iMod ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights $Hna]") as "Hna".
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
      (* The registry holds the right to free [ι], or the witness
         that [ι] is already quarantined. *)
      iDestruct (allocator_owned_rights_delete with "Hrights")
        as "[Hright Hrights]"; first exact HιΩ.
      iDestruct "Hright" as "[#Hq_old|Hright]".
      { (* A stale request: the tag of the argument is cleared, and the
           request is rejected. *)
        iDestruct "Hcapvalid" as "[Hok _]".
        iDestruct (heap_cap_ok_id with "Hok") as %(Hb_heap & _ & _);
          first (destruct Hbounds as (_ & ? & _); solve_addr).
        assert (has_authority (Cap p g b e a)) as Hauth.
        { split; first done. exists b.
          rewrite /heap_authority_base decide_True;
            last (destruct Hbounds as (_ & ? & _); solve_addr).
          by rewrite /heap_cap_base /memory_cap_base /= Hb_heap. }
        iMod (reg_refilter _ ca1 (Cap p g b e a @@? Some ι) ι Hauth eq_refl
                with "Hq_old Hca1") as "Hca1".
        iAssert (allocator_owned_rights Ω) with "[Hrights]" as "Hrights".
        { iApply (allocator_owned_rights_delete _ _ HιΩ). iFrame "Hrights".
          iLeft. iExact "Hq_old". }
        iMod ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights $Hna]") as "Hna".
        iApply ("Hreject" $! (lclear_tag (Cap p g b e a @@? Some ι))
                 with "[%] Hcont HPCr Hworld Hcstk Hna Hcgpr Hcrar Hca0 Hca1 Hca2 Hct0 Hct1 Hct2 Hct3 Hct4 Hctp Hcnull Hrmap").
        intros next allocations o _ _ (p' & g' & b' & e' & a' & Hcap & _).
        discriminate Hcap. }
      (* Accept: open every cell of [ι], with the right to free it refuting
         their tombstones, and free it. *)
      iMod (free_region_open_list W C g ι (1/2) lk Hlk_nodup Hpayload_keys
        with "Hright [] Hworld")
        as (ws) "(Hright & Hworld_open & Hcells & Hhandles)".
      { rewrite /lk big_sepL_fmap. iExact "Hcov". }
      iDestruct (big_sepL2_length _ _ _ with "Hcells") as %Hlen.
      rewrite length_fmap in Hlen.
      rewrite big_sepL2_fmap_l.
      iAssert (free_auth_held ι)%I with "[Hright]" as "Hheld".
      { rewrite /free_auth_held /free_auth_owner_inst /free_auth_owner /=. done. }
      set (rmap := delete cnull (delete ctp (delete ca4 (delete ca3 (delete ct2
        (delete ct1 (delete ct0 (delete ca2 (delete ca1 (delete ca0
        (delete cra (delete cgp regs)))))))))))).
      (* MTDC, for the quarantine, from the trusted-stack invariant. *)
      iMod (na_inv_acc with "Hswitcher Hna") as "(Hsw & Hna & Hsw_close)";
        [solve_ndisj|solve_ndisj|].
      iDestruct "Hsw" as (a_tstk cstk' save_area tstk_next) "[>Hmtdc Hsw]".
      iApply (allocator_free_valid_correct ⊤ (⊤ ∖ ↑Nallocator_otype ∖ ↑Ntstack) g_owner a_owner id Ω p g ι b e a ws
        (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return)
        (Capₗ RWL _ b_trusted_stack e_trusted_stack b_trusted_stack) rmap
        (HO th) with "[-]");
        [ solve_ndisj | solve_ndisj | exact Hshadow_owner | exact Hbounds_owner | exact HιΩ
        | exact Hbounds | symmetry; exact Hlen | | | intros _; reflexivity
        | intros vm [g_tstk ->] _; done | apply jalr_target_ok_switcher_return_sentry |].
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
      (* The world is unchanged: the registry gets [ι ⊒ AQuar] in
         place of the right to free [ι], and the cells of [ι] close as
         tombstones. *)
      iMod ("Hclose" $! Ω with "[$Ha_owner $Hid Hrights $Hna_post]") as "Hna_post".
      { iApply (allocator_owned_rights_delete _ _ HιΩ). iFrame "Hrights".
        iLeft. iExact "Hq". }
      iAssert (world_interp W C)
        with "[Hworld_open Hhandles]" as "Hworld_q".
      { iApply (free_world_close_quarantined_list W C ι
          (finz.seq_between b e) (finz_seq_between_NoDup b e) with "Hq").
        rewrite big_sepL_fmap. iFrame "Hworld_open Hhandles". }
      iMod (world_interp_revoke_stack W C
          b_stk e_stk (stk_start_a b_stk e_stk)
          with "[$Hinterp_csp $Hworld_q]")
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
      set (Wfixed := close_list
        (l ++ (LNonHeap <$> finz.seq_between b_stk e_stk)) (revoke W)).
      destruct Htemps as [Hnodup Htemps].
      assert (related_sts_pub_world W Wfixed) as Hrelated_pub.
      { subst Wfixed. apply related_pub_revoke_close_list. exact Htemps. }
      iDestruct (RevokedResources_mono_pub W Wfixed C l l
        Hrelated_pub with "Hrevoked") as "Hrevoked".
      iAssert (interp Wfixed C (WInt 0)) as "#Hinterp0".
      { iApply interp_int. }
      iApply (switcher_ret_specification W (revoke W) C _
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
      (* Take the owner word and token out of the registry. *)
      iMod (allocator_otype_acc ⊤ ⊤ W C wca0 with "Hreg Hspred Hinterp_ca0 Hna")
        as (g_owner a_owner id Ω)
        "(-> & %Hbounds_owner & %Hshadow_owner & Ha_owner & Hid & Hrights & Hna & Hclose)";
        [solve_ndisj | solve_ndisj | done | done |].
      iApply (allocator_free_narrowed_spec ⊤ (⊤ ∖ ↑Nallocator_otype) g_owner a_owner id p g ι base objend b e a
        (Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return)
        with "[-]");
        [ destruct Hbounds as (_ & Hbe & _); solve_addr | exact Hnarrow | solve_ndisj | solve_ndisj
        | exact Hshadow_owner | exact Hbounds_owner
        | apply jalr_target_ok_switcher_return_sentry |].
      iFrame "Hservice Hstatic Hna Hobj Ha_owner HPCr Hcgpr Hcrar Hca0 Hca1 Hca2".
      iFrame "Hct0 Hct1 Hct2 Hct3 Hct4 Hctp".
      iNext.
      iIntros "(Hna & Ha_owner & HPCr & Hcgpr & Hcrar & Hca0 & Hca1 & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp)".
      (* Close the registry. *)
      iMod ("Hclose" $! Ω with "[$Ha_owner $Hid $Hrights $Hna]") as "Hna".
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
    let a_alloc_exp_tbl_cgp := (allocator_exp_tbl_b ^+ ExportTable_offset_cgp) in
    let a_alloc_entry_free := (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off) in
    allocator_service_ctx ∗
    allocator_service_static ∗
    allocator_otype_registry ∗
    AllocOtype ↪ₒ{SealGlobal} allocator_otype_propC ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    allocator_exp_tbl_b ↦ₐ□ Cap RX Global
      allocator_pcc_b allocator_pcc_e allocator_pcc_b ∗
    a_alloc_exp_tbl_cgp ↦ₐ□ Cap RW Global
      allocator_cgp_b allocator_cgp_e allocator_cgp_b ∗
    no_handler allocator_exp_tbl_b ∗
    a_alloc_entry_free ↦ₐ□
      WInt (encode_entry_point InterruptEnabled allocator_free_nargs allocator_free_min_stack
        allocator_free_pcc_off) -∗
    ot_switcher_prop W C
      (Cap RO g_allocator_exp_tbl allocator_exp_tbl_b allocator_exp_tbl_e
        a_alloc_entry_free).
  Proof.
    intros Hpc_b a_alloc_exp_tbl_cgp a_alloc_entry_free.
    subst a_alloc_exp_tbl_cgp a_alloc_entry_free.
    iIntros "(#Hservice & #Hstatic & #Hreg & #Hspred & #Hswitcher & #Hswitcher_static & #HPCC & #HCGP &
      [#Heh #Hehs] & #Hentry)".
    iExists g_allocator_exp_tbl, allocator_exp_tbl_b, allocator_exp_tbl_e,
      (allocator_exp_tbl_b ^+ allocator_free_exp_tbl_off),
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

    assert (forall a, a ∈ₐ [allocator_exp_tbl_b, allocator_exp_tbl_e) ->
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
    iIntros (W').
    iNext.
    change (allocator_pcc_b ^+ allocator_free_pcc_off) with allocator_free_pcc_addr.
    iAssert (no_handler allocator_exp_tbl_b) as "#Hno_handler"; first iFrame "Heh Hehs".
    iApply (free_exec_entry_point W' C Hpc_b).
    iFrame "#".
  Qed.

End Heap_Temporal_Safety_Interp.
