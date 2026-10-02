From iris.proofmode Require Import proofmode.
From griotte Require Import logrel proofmode switcher switcher_preamble.
From griotte Require Import switcher_spec_KtK register_tactics map_simpl.
From griotte Require Import heap_temporal_safety_preamble.
From griotte.allocator Require Import allocator allocator_preamble.
From griotte.allocator Require Export allocator_malloc_spec allocator_free_spec
  allocator_resource_spec.

(** Trusted calls use [allocator_malloc_valid_correct] at size one and
    [allocator_free_valid_correct] with the singleton containing [&p]. Both
    take the caller's allocator capability in [ca0] and require its owner id
    with the matching physical owner word, which they give back. Their
    continuations retain an original-bounds receipt recording the owner and
    return physical ownership / reclaim tokens, respectively.
    Compose them with [switcher_cc_specification_known_to_known_function];
    neither trusted call requires the private pointer to satisfy [interp].

    The separate unknown-caller entry contracts below follow the service
    boundary in the KVS case study. They must cover arbitrary safe arguments,
    allocation failure, invalid frees, narrowed ranges and repeated free.
    The current physical free proof requires memory ownership, so it cannot
    simply be applied to a capability retained by an unknown compartment. *)

Section Heap_Temporal_Safety_Allocator.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType Word Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    {allocator_ownerg : allocatorOwnerG Σ}
    `{MP : MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
    {alloclayout : allocatorLayout} {allocwf : allocatorLayoutWf}.

  Definition hts_malloc_result (id : Z) (S : gset Addr) (a_owner : Addr)
    : Word -> Word -> iProp Σ :=
    λ w0 w1, (a_owner ↦ₐ WInt id ∗
      ((allocator_owner_id id S ∗
        ⌜w0 = WInt ALLOC_NO_MEMORY ∧ w1 = WInt 0⌝) ∨
       (∃ b e : Addr,
         ⌜(heap_b < b /\ b < e /\ e <= heap_e)%a ∧ (e - b = 1)%Z⌝ ∗
         ⌜w0 = WCap true RW Global b e b ∧ w1 = WInt 0⌝ ∗
         allocator_owner_id id (S ∪ {[b]}) ∗
         free_right b ∗
         allocator_allocation b e (id, 0%Z) ∗
         allocator_zeroed b e)))%I.

  Lemma hts_malloc_known_function
    (wcgp wcra wcs0 wcs1 : Word)
    (b_stk e_stk a_stk : Addr) (arg_rmap : Reg) (cstk : CSTK)
    (g_owner : Locality) (a_owner : Addr) (id : Z) (S : gset Addr) :
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    arg_rmap !! ca0 = Some (allocator_capability g_owner a_owner) ->
    arg_rmap !! ca1 = Some (WInt 1) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (allocator_owner_id id S ∗
       a_owner ↦ₐ WInt id)
      (hts_malloc_result id S a_owner) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_malloc_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_malloc_pcc_off%I.
  Proof.
    iIntros (Hshadow_owner Hbounds_owner Harg Harg1) "#Hservice".
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros (arg_rmap' rmap')
      "#Halloc (%Hargdom & %Hrmapdom & Hna & HPC & Hcgp & Hcra & Hcsp
        & Hargs & Hrmap & Hstk & Hcstk & (Howner & Ha_owner) & Hpost)".
    iEval (cbn) in "HPC".
    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0] as
      ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
       "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
       "[Hct0 %Hwct0]"].
    iClear "Hargs".
    rewrite Harg in Hwca0. rewrite Harg1 in Hwca1. simplify_eq.
    iExtractList "Hrmap" [ct1;ct2;ct3;ct4;ctp;cnull] as
      ["Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    iDestruct "Hct1" as "[Hct1 %Hct1]".
    iDestruct "Hct2" as "[Hct2 %Hct2]".
    iDestruct "Hct3" as "[Hct3 %Hct3]".
    iDestruct "Hct4" as "[Hct4 %Hct4]".
    iDestruct "Hctp" as "[Hctp %Hctp]".
    iDestruct "Hcnull" as "[Hcnull %Hcnull]".
    simplify_eq.
    iApply (allocator_malloc_valid_correct ⊤ g_owner a_owner 1 id S _ with
      "[- $Halloc $Hservice $Hna $Howner $Ha_owner $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull]");
      eauto.
    { lia. }
    iNext.
    iIntros "(Hna & Ha_owner & HPC & Hcgp & Hcra & Hca2 & Hct0
      & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hres)".
    iEval (cbn) in "HPC".
    iExtractList "Hrmap" [cs0;cs1] as
      ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iDestruct "Hca2" as (wca2_ret) "Hca2".
    iDestruct "Hct0" as (wct0_ret) "Hct0".
    iDestruct "Hct1" as (wct1_ret) "Hct1".
    iDestruct "Hct2" as (wct2_ret) "Hct2".
    iDestruct "Hct3" as (wct3_ret) "Hct3".
    iDestruct "Hct4" as (wct4_ret) "Hct4".
    iDestruct "Hctp" as (wctp_ret) "Hctp".
    iInsertList "Hrmap" [ca2;ca3;ca4;ca5;ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    set (rmap_ret := <[cnull:=WInt 0]>
      (<[ctp:=wctp_ret]> (<[ct4:=wct4_ret]> (<[ct3:=wct3_ret]>
      (<[ct2:=wct2_ret]> (<[ct1:=wct1_ret]> (<[ct0:=wct0_ret]>
      (<[ca5:=WInt 0]> (<[ca4:=WInt 0]> (<[ca3:=WInt 0]>
      (<[ca2:=wca2_ret]> (delete cs1 (delete cs0 rmap'))))))))))))).
    assert (dom rmap_ret =
      all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]})
      as Hdom_ret.
    { subst rmap_ret. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmapdom /dom_arg_rmap /allocator_malloc_nargs /=.
      set_solver+. }
    iDestruct "Hres" as "[(Howner & Hca0 & Hca1) | Hres]".
    - iApply ("Hpost" $! (WInt ALLOC_NO_MEMORY) (WInt 0) rmap_ret
        (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit; first (iPureIntro; exact Hdom_ret).
      iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk".
      rewrite /hts_malloc_result. iFrame "Ha_owner".
      iLeft. iFrame "Howner". iPureIntro. auto.
    - iDestruct "Hres" as (b e)
        "(%Hbounds & Hca0 & Hca1 & Howner & Hright & #Hreceipt & Hzero)".
      iApply ("Hpost" $! (WCap true RW Global b e b) (WInt 0)
        rmap_ret (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit; first (iPureIntro; exact Hdom_ret).
      iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk".
      rewrite /hts_malloc_result. iFrame "Ha_owner".
      iRight. iExists b,e. iFrame "Howner Hright Hreceipt Hzero".
      iPureIntro. split; [exact Hbounds|done].
  Qed.

  Definition hts_free_result (b e : Addr) (id reserved : Z) (S : gset Addr)
    (a_owner : Addr) : Word -> Word -> iProp Σ :=
    λ w0 w1, (allocator_allocation b e (id, reserved) ∗
      allocator_reclaimed b e ∗
      allocator_owner_id id S ∗
      a_owner ↦ₐ WInt id ∗
      ⌜w0 = WInt ALLOC_OK ∧ w1 = WInt 0⌝)%I.

  Lemma hts_free_known_function
    (wcgp wcra wcs0 wcs1 : Word)
    (b_stk e_stk a_stk b e a : Addr) (arg_rmap : Reg) (cstk : CSTK)
    (p : Perm) (g : Locality) (reserved : Z) (ws : list Word)
    (g_owner : Locality) (a_owner : Addr) (id : Z) (S : gset Addr) :
    is_shadow_address a_owner = false ->
    withinBounds a_owner (a_owner ^+ 1)%a a_owner = true ->
    (heap_b < b /\ b < e /\ e <= heap_e)%a ->
    length ws = length (finz.seq_between b e) ->
    arg_rmap !! ca0 = Some (allocator_capability g_owner a_owner) ->
    arg_rmap !! ca1 = Some (WCap true p g b e a) ->
    allocator_service_ctx ⊢
    switcher_cc_specification_known_to_known_function
      (allocator_allocation b e (id, reserved) ∗
       [[b,e]] ↦ₐ [[ws]] ∗
       allocator_owner_id id S ∗
       a_owner ↦ₐ WInt id)
      (hts_free_result b e id reserved S a_owner) wcgp wcra wcs0 wcs1
      b_stk e_stk a_stk arg_rmap cstk allocator_free_nargs ⊤
      allocator_pcc_b allocator_pcc_e allocator_cgp_b allocator_cgp_e
      allocator_free_pcc_off%I.
  Proof.
    iIntros (Hshadow_owner Hbounds_owner Hbounds Hlen Harg Harg1) "#Hservice".
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros (arg_rmap' rmap')
      "#Halloc (%Hargdom & %Hrmapdom & Hna & HPC & Hcgp & Hcra & Hcsp
        & Hargs & Hrmap & Hstk & Hcstk & (Hreceipt & Hmem & Howner & Ha_owner) & Hpost)".
    iEval (cbn) in "HPC".
    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0] as
      ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
       "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
       "[Hct0 %Hwct0]"].
    iClear "Hargs".
    rewrite Harg in Hwca0. rewrite Harg1 in Hwca1. simplify_eq.
    iExtractList "Hrmap" [ct1;ct2;ct3;ct4;ctp;cnull] as
      ["Hct1";"Hct2";"Hct3";"Hct4";"Hctp";"Hcnull"].
    iDestruct "Hct1" as "[Hct1 %Hct1]".
    iDestruct "Hct2" as "[Hct2 %Hct2]".
    iDestruct "Hct3" as "[Hct3 %Hct3]".
    iDestruct "Hct4" as "[Hct4 %Hct4]".
    iDestruct "Hctp" as "[Hctp %Hctp]".
    iDestruct "Hcnull" as "[Hcnull %Hcnull]".
    simplify_eq.
    iApply (allocator_free_valid_correct ⊤ p g b e a reserved g_owner a_owner id S ws _ with
      "[- $Halloc $Hservice $Hna $Hreceipt $Howner $Ha_owner $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hct0 $Hct1 $Hct2 $Hct3 $Hct4 $Hctp $Hcnull $Hmem]");
      eauto.
    iNext.
    iIntros "(Hna & Hreceipt & Howner & _ & Ha_owner & HPC & Hcgp & Hcra & Hca0 & Hca1
      & Hca2 & Hct0 & Hct1 & Hct2 & Hct3 & Hct4 & Hctp & Hcnull & Hreclaimed & _)".
    iEval (cbn) in "HPC".
    iExtractList "Hrmap" [cs0;cs1] as
      ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]"].
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iDestruct "Hca2" as (wca2_ret) "Hca2".
    iDestruct "Hct0" as (wct0_ret) "Hct0".
    iDestruct "Hct1" as (wct1_ret) "Hct1".
    iDestruct "Hct2" as (wct2_ret) "Hct2".
    iDestruct "Hct3" as (wct3_ret) "Hct3".
    iDestruct "Hct4" as (wct4_ret) "Hct4".
    iDestruct "Hctp" as (wctp_ret) "Hctp".
    iInsertList "Hrmap" [ca2;ca3;ca4;ca5].
    iInsertList "Hrmap" [ct0;ct1;ct2;ct3;ct4;ctp;cnull].
    set (rmap_ret := <[cnull:=WInt 0]>
      (<[ctp:=wctp_ret]> (<[ct4:=wct4_ret]> (<[ct3:=wct3_ret]>
      (<[ct2:=wct2_ret]> (<[ct1:=wct1_ret]> (<[ct0:=wct0_ret]>
      (<[ca5:=WInt 0]> (<[ca4:=WInt 0]> (<[ca3:=WInt 0]>
      (<[ca2:=wca2_ret]> (delete cs1 (delete cs0 rmap'))))))))))))).
    assert (dom rmap_ret =
      all_registers_s ∖ {[PC; csp; cgp; cra; cs0; cs1; ca0; ca1]})
      as Hdom_ret.
    { subst rmap_ret. repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmapdom /dom_arg_rmap /allocator_free_nargs /=.
      set_solver+. }
    iApply ("Hpost" $! (WInt ALLOC_OK) (WInt 0) rmap_ret
      (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
    iSplit; first (iPureIntro; exact Hdom_ret).
    iFrame "Hna HPC Hcgp Hcra Hcs0 Hcs1 Hcsp Hca0 Hca1 Hrmap Hstk Hcstk".
    rewrite /hts_free_result. iFrame "Hreceipt Hreclaimed Howner Ha_owner".
    iPureIntro. auto.
  Qed.

  (** BLOCKED: allocation must extend the heap world and make the zeroed
      result safe to return to an arbitrary caller. *)
  Lemma hts_malloc_entry_spec W C :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_malloc_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_malloc_nargs W C.
  Proof.
  Abort.

  (** BLOCKED: free from an unknown caller needs the shared heap protocol to
      recover live addresses or handle already quarantined addresses, then reestablish
      the world while invalidating retained aliases. Do not assume exclusive
      points-to ownership merely because the argument is safe to share. *)
  Lemma hts_free_entry_spec W C :
    allocator_ctx ∗ allocator_service_ctx ⊢
    execute_entry_point
      (WCap true RX Global allocator_pcc_b allocator_pcc_e allocator_free_pcc_addr)
      (WCap true RW Global allocator_cgp_b allocator_cgp_e allocator_cgp_b)
      allocator_free_nargs W C.
  Proof.
  Abort.

End Heap_Temporal_Safety_Allocator.
