From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import
  switcher kvs kvs_preamble kvs_spec_check_uint16 kvs_spec_addOrUpdate.

Section KVS_spec_addOrUpdate_safe.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification from unknown *)
  Lemma KVS_addOrupdate_spec_safe
    (Wca W : WORLD) (C : CmptName)
    (wret wca0 wca1 wca2 : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->
    ↑Nkvs_otype ⊆ E ->

    related_sts_priv_world Wca W ->

    ( seal_pred KVS_OTYPE kvs_otype_propC ∗
      na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp Wca C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ interp Wca C wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      world_interp W C ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         (ca0 ↦ᵣ WInt ASM_TRUE ∨ ca0 ↦ᵣ WInt ASM_FALSE) ∗
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         world_interp W C

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hnkvs_E Hnkvs_otype_E Hrelated_Wca_W)
      "(#Hspred & #Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & #Hinterp_wca0
      & Hca1 & Hca2 & #Hinterp_wca2 & Hctp & Hct1 & Hct2 & Hcnull & Hworld & Hpost)".

    (* Destruct validity map key *)
    destruct (decide (word_is_uint16 wca1)) as [Hwca1_uint16|Hwca1_uint16]; cycle 1.
    { (* the map key argument is not a uint16 *)
      iApply KVS_addOrUpdate_spec_not_uint16_map_key; eauto; iFrame "∗#".
      iNext; iIntros "(Hna & HPC & Hcra & Hca0 & Hca1 & Hct1 & Hcnull)".
      iApply "Hpost"; iFrame.
    }
    destruct wca1 as [nkey| | | ]; cbn in Hwca1_uint16; try done.

    (* Destruct validity user key *)
    destruct ( is_sealed_with_o wca0 KVS_OTYPE ) eqn:Hwca0_sealed_with_kvs_ot; cycle 1.
    { (* the user key argument is not a valid sealed user key *)
      iApply KVS_addOrUpdate_spec_invalid_sealed_user_key; eauto; iFrame "∗#".
    }
    (* The inputs are valid. *)
    rewrite /is_sealed_with_o in Hwca0_sealed_with_kvs_ot.
    destruct wca0 as [ | | | ot wsb ]; try done.
    rewrite Z.eqb_eq in Hwca0_sealed_with_kvs_ot.
    assert (ot = KVS_OTYPE) by solve_addr+Hwca0_sealed_with_kvs_ot; simplify_eq.


    (* Open sealing predicate of sealed user key *)
    iDestruct (monotone.interp_monotone_sd with "[] Hinterp_wca0") as "Hinterp_wca0_W"; auto.
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_wca0".
    iAssert (sts_seals_std C KVS_OTYPE {[WSealable wsb]})%I as "#Hinterp_wca0'".
    { iApply sts_seals_std_weaken; last iFrame "Hinterp_wca0"; last set_solver+. }

    iDestruct (sopen_world_interp_singleton with "Hspred Hinterp_wca0' Hworld")
                as "(Hworld & Hres_open & HP)".
    rewrite /kvs_otype_propC /= /kvs_otype_prop //= /kvs_otype_inv.
    iDestruct "HP" as "(%ku & %a & %s' & >%Heq_sb & >%Hbounds & >Ha & Halloc & Hfkeys)".
    destruct wsb as [ p_user_key l_user_key | ] ; simplify_eq.

    (* Either the map key is already allocated, or it is not *)
    destruct (s' !! nkey)  as [ w | ] eqn:Hnkey.
    - iDestruct (big_sepM_delete with "Hfkeys")
        as "[ [ Hkvs_frag #Hinterp_w] Hfkeys]"
      ; eauto; iEval (cbn) in "Hkvs_frag".
      iApply KVS_update_spec; last iFrame "∗#"; eauto.
      iNext.
      iIntros "(%Hcan_store & Hna
                & HPC & Hgcp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                & Ha & Halloc & Hkvs_frag)".
      iDestruct ( big_sepM_insert_delete with "[$Hfkeys $Hkvs_frag Hinterp_wca2 ]") as "Hfkeys".
      { cbn ; iIntros (W' Hrelated_W_W').
        iApply (monotone.interp_monotone_nl with "[] [] [$Hinterp_wca2]"); iPureIntro.
        + eapply related_sts_priv_trans_world; eauto.
        + eapply (canStore_global_nonisWL RW); done.
      }
      iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key a)))))
        with "[Ha Halloc Hfkeys]"
        as "HP".
      { iFrame "∗%#". iPureIntro; auto. }
      iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

      iApply "Hpost"; iFrame.

    - iApply KVS_add_spec; last iFrame "∗#"; eauto.
      { by rewrite not_elem_of_dom. }
      iNext.
      iIntros "(Hna
                & HPC & Hgcp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                & Ha
                & Hrest)".

      iDestruct "Hrest" as
        "[ (%Hcan_store & Hca0 & Halloc & Hkvs_frag)
           | (Hca0 & Halloc)
         ]".
      + iDestruct ( big_sepM_insert with "[Hkvs_frag $Hfkeys]") as "Hfkeys";eauto.
        { iSplit; first iFrame.
          cbn; iIntros (W' Hrelated_W_W').
          iApply (monotone.interp_monotone_nl with "[] [] [$Hinterp_wca2]"); iPureIntro.
          + eapply related_sts_priv_trans_world; eauto.
          + eapply (canStore_global_nonisWL RW); done.
        }

        iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key a)))))
          with "[Ha Halloc Hfkeys]"
          as "HP".
        { iFrame "∗%"; iPureIntro; auto. }
        iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

        iApply "Hpost"; iFrame.

      + iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key a)))))
          with "[Ha Halloc Hfkeys]"
          as "HP".
        { iFrame "∗%"; iPureIntro; auto. }
        iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

        iApply "Hpost"; iFrame.
  Qed.


  (*** Safe entry point  *)
  Lemma kvs_addOrUpdate_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    (Nswitcher : namespace)
    :

    seal_pred KVS_OTYPE kvs_otype_propC ∗
    na_inv cerise_nais Nkvs kvs_inv ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
    inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
    inv (export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr)
        (kvs_addOrUpdate_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_addOrUpdate) ∗
    WSealed ot_switcher (SCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) ↦□ₑ kvs_addOrUpdate_nargs ∗
    WSealed ot_switcher (SCap RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) ↦□ₑ kvs_addOrUpdate_nargs
    -∗
    ot_switcher_prop W C (WCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
  Proof.
    iIntros
      "(#Hspred & #Hinv_kvs & #Hinv_switcher
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & #Hkvs_exp_addOrRead
      & #Hentry_KVS & #Hentry_KVS_borrow
      )".

    iExists g_kvs_exp_tbl, b_kvs_exp_tbl, e_kvs_exp_tbl, kvs_addOrUpdate_exp_tbl_addr,
    KVS_pcc_b, KVS_pcc_e, KVS_cgp_b, KVS_cgp_e, kvs_addOrUpdate_nargs, _, Nkvs_exp_tbl.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iFrame "#".
    iSplit; first done.
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off; solve_addr).
    iSplit; first (iPureIntro; rewrite /kvs_addOrUpdate_nargs; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hworld_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    (* Extract the registers that we will need *)
    assert ( is_Some (rmap !! ctp) ) as [wctp Hwctp] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! cnull) ) as [wcnull Hwcnull] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    iExtractList "Hrmap" [PC; cgp; cra ; csp ] as ["HPC"; "Hcgp"; "Hcra"; "Hcsp"].
    iExtractList "Hrmap" [ct1; ct2; ctp; cnull; ca0; ca1; ca2] as ["Hct1"; "Hct2"; "Hctp"; "Hcnull"; "Hca0"; "Hca1"; "Hca2"].

    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }
    iAssert (interp W0 C wca2) as "#Hinterp_wca2".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }

    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & #Hstack_revoked_W0 & _ & >[%stk_mem Hstk] & [Hrevoked_l _])".
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    iApply (KVS_addOrupdate_spec_safe W0 (revoke W0)); try solve_ndisj; iFrame "∗#".
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull & Hworld_C)".
    iAssert (∃ zca0, ca0 ↦ᵣ WInt zca0)%I with "[Hca0]" as "[%zca0 Hca0]".
    { iDestruct "Hca0" as "[$|$]". }


    iDestruct "Hca2" as "[% Hca2]"; iDestruct (big_sepM_insert _ _ ca2 with "[$Hrmap $Hca2]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hcnull" as "[% Hcnull]"; iDestruct (big_sepM_insert _ _ cnull with "[$Hrmap $Hcnull]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hct2" as "[% Hct2]"; iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    map_simpl "Hrmap".

    destruct Hl_unk as [ Hnodup Htemps ]; auto.
    iApply (switcher_ret_specification _ W0 (revoke W0)
             with
             "[ $Hstk $Hcstk $HK $Hworld_C $Hna $HPC $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ) ; eauto; last iFrame "∗#".
    { apply related_pub_revoke_close_list; eauto. }
    { apply regmap_full_dom in Hrmap_init.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_init. set_solver+. }
    { subst csp_b. destruct Hsync_csp as [Hsync_csp <-]; eauto. }
    { intros a Ha; apply Htemps; done. }
    { iSplit; iApply interp_int. }
  Qed.

End KVS_spec_addOrUpdate_safe.
