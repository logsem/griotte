From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base.
From griotte Require Import
  kvs kvs_preamble kvs_spec_check_uint16 kvs_spec_read.

Section KVS_spec_read_safe.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {seal_registryg : sealRegistryG LAddr Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
  .

  (*** Specification from unknown *)
  Lemma KVS_read_spec_safe
    (Wca0 W : WORLD) (C : CmptName)
    (wret wca0 wca1 : LWord)
    (F : coPset)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->
    ↑Nkvs_otype ⊆ F ->

    related_sts_priv_world Wca0 W ->
    jalr_target_ok cnull cra wret.(lw) = true ->

    ( KVS_OTYPE ↪ₒ{SealGlobal} kvs_otype_propC ∗
      kvs_otype_registry ∗
      kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] wca0 ∗ interp Wca0 C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to update *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)

      world_interp W C ∗

      ( ▷ (na_own (tpool th) F ∗
           PC ↦ₚ[th] lupdatePcPerm wret ∗
           cgp ↦ᵣ[th] - ∗
           cra ↦ᵣ[th] - ∗
           (ca0 ↦ᵣ[th] WInt ASM_TRUE ∨ ca0 ↦ᵣ[th] WInt ASM_FALSE) ∗
           ( (∃ w, ca1 ↦ᵣ[th] w ∗ interp W C w) ∨ ca1 ↦ᵣ[th] WInt 0 ) ∗
           ct1 ↦ᵣ[th] - ∗ (* scratch *)
           ct2 ↦ᵣ[th] - ∗ (* scratch *)
           ctp ↦ᵣ[th] - ∗ (* scratch *)

           world_interp W C

           -∗ safe[th]
        ) ∧
        (* The load after the failed unsealing of the user key faults *)
        ▷ ( ∀ a,
            na_own (tpool th) F ∗
            cgp ↦ᵣ[th] - ∗
            cra ↦ᵣ[th] - ∗
            ca0 ↦ᵣ[th] - ∗
            ca1 ↦ᵣ[th] - ∗
            ct1 ↦ᵣ[th] - ∗
            ct2 ↦ᵣ[th] - ∗
            ctp ↦ᵣ[th] - ∗
            world_interp W C -∗
            trap_safe (Cap RX Global KVS_pcc_b KVS_pcc_e a) ⊤
              (HO th) ) )
      ⊢ safe[th])%I.
  Proof.
    iIntros (Hunsealing_shadow Hnkvs_E Hnkvs_E' Hnkvs_otype_E Hrelated_Wca0_W Htgt)
      "(#Hspred & #Hreg & #Hkvs_static & #Hkvs_inv & #Hkvs_logical_inv & Hna & HPC & Hcgp & Hcra & Hca0 & #Hinterp_wca0
      & Hca1 & Hct1 & Hct2 & Hctp & Hworld & Hpost)".

    (* Destruct validity map key *)
    destruct (decide (word_is_uint16 wca1.(lw))) as [Hwca1_uint16|Hwca1_uint16]; cycle 1.
    { (* the map key argument is not a uint16 *)
      iDestruct "Hpost" as "[Hpost _]".
      iApply (KVS_read_spec_not_uint16_map_key with
               "[- $Hkvs_static $Hkvs_inv $Hna $HPC $Hcra $Hca0 $Hca1 $Hct1]");
        [exact Hnkvs_E | exact Hwca1_uint16 | exact Htgt |].
      iNext; iIntros "(Hna & HPC & Hcra & Hca0 & Hca1 & Hct1)".
      iApply "Hpost"; iFrame.
    }
    destruct wca1 as [ [nkey| | | ] πnkey]; cbn in Hwca1_uint16; try done.


    (* Untagged user keys fail at UnSeal, before opening seal resources. *)
    destruct (get_tag wca0.(lw)) eqn:Hwca0_tag; cycle 1.
    { iApply (KVS_read_spec_invalid_sealed_user_key
               with "[$Hkvs_static $Hna $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp
                      Hworld Hpost]");
        [exact Hunsealing_shadow | exact Hwca1_uint16
        | right; exact Hwca0_tag |].
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[$]"). }

    (* Destruct validity user key *)
    destruct ( is_sealed_with_o wca0.(lw) KVS_OTYPE ) eqn:Hwca0_sealed_with_kvs_ot; cycle 1.
    { (* the user key argument is not a valid sealed user key *)
      iApply (KVS_read_spec_invalid_sealed_user_key
               with "[$Hkvs_static $Hna $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp
                      Hworld Hpost]");
        [exact Hunsealing_shadow | exact Hwca1_uint16
        | left; exact Hwca0_sealed_with_kvs_ot |].
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[$]").
    }
    (* The inputs are valid. *)
    iDestruct "Hpost" as "[Hpost _]".
    (* Open the registry entry of the sealed user key *)
    iMod (kvs_otype_acc ⊤ F Wca0 C wca0 with "Hreg Hspred Hinterp_wca0 Hna")
      as (l_user_key a uk) "(%Heq_sb & %Hbounds & %Huser_key_shadow & Ha & HLUKVS & Hinterp & Hna & Hclose)";
      [done|solve_ndisj|done|done|].
    subst wca0.

    assert (nkey ∈ kvs_all_map_keys) as Hnkey_is_map_key by rewrite -is_uint16_in_kvs_all_map_keys //.
    iDestruct (big_sepS_delete with "Hinterp") as "[Hinterp_nkey Hinterp]"; eauto.

    (* Either the map key is already allocated, or it is not *)
    iDestruct "Hinterp_nkey" as "[ (%w & >Hney & #Hinterp_nkey) | >Hnkey ]".
    - iEval (rewrite world_interp_eq /world_interp_def) in "Hworld".
      iApply KVS_read_spec_in_world; last iFrame "∗#"; try solve_ndisj; eauto.
      iNext.
      iIntros "(Hregion & Hna & HPC & Hgcp & Hcra & Hca0 & [%actual [Hca1 %Hactual] ] & Hct1 & Hct2 & Hctp
                & Ha & HLUKVS & Hnkey)".

      iAssert (world_interp W C) with "[Hregion]" as "Hworld".
      { by rewrite world_interp_eq /world_interp_def. }

      iDestruct (big_sepS_delete with "[$Hinterp Hnkey Hinterp_nkey]") as "Hinterp"; eauto.
      { rewrite /safe_kvs_pointsto; eauto. }
      iMod ("Hclose" with "[$Ha $HLUKVS $Hinterp $Hna]") as "Hna".

      iApply "Hpost"; iFrame.
      iLeft; iFrame.
      iApply (interp_in_mem_load_result W C RWL w actual).
      { rewrite !lload_word_RWL.
        destruct Hactual as [-> | [_ ->] ].
        - right. reflexivity.
        - left. reflexivity. }
      iApply (monotone.interp_in_mem_monotone ∅ W with "Hinterp_nkey").
      apply related_sts_pub_world_empty.

    - iApply KVS_read_spec_notin; last iFrame "∗#"; try solve_ndisj; eauto.
      iNext.
      iIntros "(Hna & HPC & Hgcp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp
                & Ha & HLUKVS & Hnkey)".

      iDestruct (big_sepS_delete with "[$Hinterp $Hnkey]") as "Hinterp"; eauto.
      iMod ("Hclose" with "[$Ha $HLUKVS $Hinterp $Hna]") as "Hna".

      iApply "Hpost"; iFrame.
  Qed.


  (*** Safe entry point  *)
  Lemma kvs_read_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    :

    let a_kvs_exp_tbl_cgp := (b_kvs_exp_tbl ^+ ExportTable_offset_cgp) in
    KVS_pcc_b ≠ b_switcher ->
    cmpt_threads C ⊆ {[th]} ->
    KVS_OTYPE ↪ₒ{SealGlobal} kvs_otype_propC ∗
    kvs_otype_registry ∗
    kvs_static ∗
    na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
    na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
    na_inv (tpool th) Ntstack trusted_stack_inv ∗
    switcher_static ∗
    b_kvs_exp_tbl ↦ₐ□ Cap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b ∗
    a_kvs_exp_tbl_cgp ↦ₐ□ Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
    no_handler b_kvs_exp_tbl ∗
    kvs_read_exp_tbl_addr ↦ₐ□ kvs_exp_tbl_entry_read
    -∗
    ot_switcher_prop W C (Cap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
  Proof.
    intros a_kvs_exp_tbl_cgp Hpc_switcher Hpin.
    subst a_kvs_exp_tbl_cgp.
    iIntros
      "(#Hspred & #Hreg & #Hkvs_static & #Hinv_kvs & #Hinv_kvs_logical & #Hinv_switcher & #Hswitcher_static
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & [#Hkvs_exp_eh #Hkvs_exp_ehs]
      & #Hkvs_exp_addOrRead
      )".

    iExists g_kvs_exp_tbl, b_kvs_exp_tbl, e_kvs_exp_tbl, kvs_read_exp_tbl_addr,
    KVS_pcc_b, KVS_pcc_e, KVS_cgp_b, KVS_cgp_e, kvs_read_nargs, kvs_read_min_stack, _.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iFrame "#".
    iSplit; first done.
    iSplit; first (iPureIntro; exact kvs_exp_tbl_disjoint_from_shadow).
    iSplit; first by (iPureIntro; rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off /kvs_entry_read; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off /kvs_entry_read; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off /kvs_entry_read; solve_addr).
    iSplit; first (iPureIntro; rewrite /kvs_read_nargs; lia).
    iSplit; first (iPureIntro; rewrite /kvs_read_min_stack; lia).
    iSplit.
    { iPureIntro.
      pose proof KVS_size_imports as Himports.
      pose proof KVS_size_code as Hcode.
      rewrite /kvs_service_instrs !length_app in Hcode.
      rewrite kvs_read_pcc_off_eq; solve_addr.
    }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff.
        rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off /kvs_entry_read; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact kvs_exp_tbl_disjoint_from_shadow.
      - apply withinBounds_true_iff; solve_addr. }
    iSplit; first (iPureIntro; exact KVS_pcc_base_not_heap).
    iSplit; first (iPureIntro; exact KVS_cgp_base_not_heap).
    iIntros "!>" (t') "#Ht'".
    iDestruct (thread_in_elim with "Ht'") as %Ht'.
    assert (t' = th) as -> by set_solver.
    iIntros (W0) "!> %cstk %Ws %Cs %rmap %csp_b %csp_e".
    iIntros "(#Hthread & _ & HK & %Hframe_match & %Htop_tbl & HPC & Hregister_state & Hrmap
      & Hworld_C & _ & %Hsync_csp & _ & Hcstk & Hna)".
    iEval (rewrite world_resources_exclusive) in "Hworld_C".
    iAssert (no_handler (top_export_tbl cstk) ∗
             ⌜(top_tframe cstk).(tf_export_tbl) ≠ lword_of_word (WInt 0)⌝)%I as "#Hno_handler".
    { destruct Htop_tbl as (_ & -> & _ & Htbl_ok). iFrame "Hkvs_exp_eh Hkvs_exp_ehs".
      iPureIntro. by apply tf_export_tbl_ok_nonzero. }
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %Hcgp & [%mie_ret %Hcra] & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /stk_start_a in Hcsp |- *.
    rewrite /registers_pointsto.

    (* Extract the registers that we will need *)
    assert ( is_Some (rmap !! ctp) ) as [wctp Hwctp] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    iExtractList "Hrmap" [cgp; cra ; csp ] as ["Hcgp"; "Hcra"; "Hcsp"].
    iExtractList "Hrmap" [ct1; ct2; ctp; ca0; ca1] as ["Hct1"; "Hct2"; "Hctp"; "Hca0"; "Hca1"].

    (* General purpose registers *)
    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_read_nargs. }

    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! LNonHeap a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap_nonheap with "Hinterp_W0_csp"); eauto. }
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & #Hstack_revoked_W0 & _ & >[%stk_mem Hstk] & [Hrevoked_l _])".
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    assert (is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false)
      as Hunsealing_shadow.
    { eapply disjoint_from_shadow_not_in; first exact KVS_pcc_disjoint_from_shadow.
      apply withinBounds_true_iff.
      pose proof KVS_size_imports as Himports.
      pose proof KVS_size_code as Hcode_size.
      rewrite /length_kvs_imports in Himports.
      rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr+Himports Hcode_size. }
    (* The world fixed by the return through the switcher *)
    set (Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) (revoke W0))).
    destruct Hl_unk as [ Hnodup Htemps ]; auto.
    assert (related_sts_pub_world W0 Wfixed) as Hrelated_pub_W0_Wfixed.
    { subst Wfixed. apply related_pub_revoke_close_list; exact Htemps. }
    iDestruct (RevokedResources_mono_pub W0 Wfixed C l l
      Hrelated_pub_W0_Wfixed with "Hrevoked_l") as "Hrevoked_l".

    iApply (KVS_read_spec_safe W0 (revoke W0) C
              (Sentry (ret_kind mie_ret) XSRW_ Local b_switcher e_switcher a_switcher_return)
              wca0 wca1 ⊤ Hunsealing_shadow
             with "[$Hspred $Hreg $Hkvs_static $Hinv_kvs $Hinv_kvs_logical $Hna $HPC $Hcgp $Hcra
                    $Hca0 $Hinterp_wca0 $Hca1 $Hct1 $Hct2 $Hctp $Hworld_C
                    Hrmap Hcsp Hstk Hcstk HK Hrevoked_l]");
      [solve_ndisj | solve_ndisj | solve_ndisj | exact Hrelared_priv_W0_W1
      | apply jalr_target_ok_switcher_return_sentry |].
    iSplit.
    - iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hworld_C)".
      iAssert (∃ wca0', ca0 ↦ᵣ wca0' ∗ interp Wfixed C wca0')%I with "[Hca0]" as "(%wca0' & Hca0 & #Hinterp_wca0')".
      { iDestruct "Hca0" as "[$|$]"; iApply interp_int. }
      iAssert (∃ wca1', ca1 ↦ᵣ wca1' ∗ interp Wfixed C wca1')%I with "[Hca1]" as "(%wca1' & Hca1 & #Hinterp_wca1')".
      { iDestruct "Hca1" as "[(%&?&?)|$]"; [iExists _; iFrame|iApply interp_int].
        iApply (monotone.interp_monotone with "[] [$]"); eauto.
        iPureIntro; apply close_list_related_sts_pub ; eauto.
      }
      iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct2" as "[% Hct2]"; iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      map_simpl "Hrmap".
      iApply (switcher_ret_specification W0 (revoke W0)
               with
               "[ $Hstk $Hcstk $HK $Hworld_C $Hna $HPC $Hrevoked_l
               $Hrmap $Hca0 $Hca1 $Hcsp]"
             ); last iFrame "∗#".
      { exact Hrelated_pub_W0_Wfixed. }
      { apply lregmap_full_dom in Hrmap_init.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap_init. set_solver+. }
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hnodup. }
      { intros a Ha; apply Htemps; done. }
    - (* The invalid user key faults: return ECOMPARTMENTFAIL to the caller *)
      iNext; iIntros (a_fault) "(Hna & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hworld_C)".
      iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct2" as "[% Hct2]"; iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
      { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
      map_simpl "Hrmap".
      iApply (trap_safe_return W0 (revoke W0) C _ csp_e csp_b l stk_mem cstk Ws Cs _
               with "Hthread Hinv_switcher Hswitcher_static Hno_handler [-]");
        last (iModIntro; iFrame).
      { exact Hrelated_pub_W0_Wfixed. }
      { apply lregmap_full_dom in Hrmap_init.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap_init. set_solver+. }
      { exact Hframe_match. }
      { exact Hsync_csp. }
      { exact Hnodup. }
      { intros a Ha; apply Htemps; done. }
      { by apply trap_no_resume_cap. }
  Qed.

End KVS_spec_read_safe.
