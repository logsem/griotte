From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl register_tactics.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import switcher kvs kvs_preamble kvs_spec_initialise.

Section KVS_spec_initialise_safe.
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


  Lemma KVS_initialise_spec_safe
    (W : WORLD) (C : CmptName)
    (wret : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->
    ↑Nkvs_otype ⊆ E ->

    (* related_sts_priv_world Wca0 W -> *)

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_initialise_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ - ∗
      ct0 ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      world_interp W C ∗

      ▷ ( ∀ (W' : WORLD) ,
            ⌜ W' = W ∨ ∃ ws, W' = <o[KVS_OTYPE := ws]o>W ⌝ ∗
            na_own cerise_nais E ∗
            PC ↦ᵣ updatePcPerm wret ∗
            cgp ↦ᵣ - ∗
            cra ↦ᵣ - ∗
            (∃ w, ca0 ↦ᵣ w ∗ interp W' C w) ∗
            (∃ w, ca1 ↦ᵣ w ∗ interp W' C w) ∗
            ct0 ↦ᵣ - ∗ (* scratch *)
            ct1 ↦ᵣ - ∗ (* scratch *)
            ctp ↦ᵣ - ∗ (* scratch *)
            cnull ↦ᵣ - ∗

            world_interp W' C

            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hnkvs_E Hnkvs_otype_E)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0
      & Hca1 & Hct0 & Hct1 & Hctp & Hcnull & Hworld & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & %next_free_uk & >Himports & >Ha_next_uk & >Ha_uk_scap & >Hcode
            & HisKVS & >%Hwf_free_uk & Hfree_uk_alloc & #Hspred)
            & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e kvs_initialise_pcc_addr (kvs_initialise_pcc_addr ^+ length kvs_initialise_instrs)%a) as HSubBounds.
    { rewrite /kvs_initialise_pcc_addr; cbn in *; solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.
    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1)%a <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    iDestruct (region_pointsto_cons with "Himports") as "[Himports_sw Himports]"; eauto.
    iDestruct (region_pointsto_single with "Himports") as "(% & Ha_unsealing & %Heq)"; eauto; simplify_eq.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 3 "Hcode" as a_initialise Ha_initialise "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_initialise = kvs_initialise_pcc_addr)
      as -> by (rewrite /kvs_initialise_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_initialise).
    iApply (KVS_initialise_spec_pre with "[- $HPC]"); last iFrame "∗#"; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct0 & Hct1
              & Hcnull & Hcode & Ha_unsealing & Ha_next_uk & Ha_uk_scap & Hfree_uk_alloc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    destruct ((next_free_uk <? MAX_USER_KEY)%Z) eqn:Hnext_free.
    - iDestruct "Hfree_uk_alloc" as "[Hfree_uk_alloc Halloc]".
      assert (0 <= next_free_uk + 1 <= MAX_USER_KEY )%Z as Hnext_free' by (apply Z.ltb_lt in Hnext_free; lia).
      iMod ("Hkvs_inv_close" with "[$Hcode $Ha_next_uk $Ha_uk_scap Himports_sw Ha_unsealing $HisKVS $Hfree_uk_alloc $Hspred $Hna]") as "Hna" ; auto.
      { iNext.
        iSplit; last done.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }

      set ( kvs_uk_sb := (kvs_user_seal_key_scap Global next_free_uk)).
      set ( kvs_uk_sb' := borrow_sb kvs_uk_sb).
      set ( adversary_kvs_keys := ( {[ WSealable kvs_uk_sb ; WSealable kvs_uk_sb']} : gset Word)).
      set (W' := <o[ KVS_OTYPE := adversary_kvs_keys ]o> W).
      iAssert (kvs_otype_prop W' C (WSealable kvs_uk_sb)) with "[Halloc]" as "ot_kvs_uk".
      {
        iEval (rewrite /kvs_otype_prop /kvs_otype_inv /=).
        iFrame "Halloc".
        iExists ( 0 ^+ next_free_uk)%a.
        rewrite /MAX_USER_KEY in Hnext_free.
        repeat iSplit; auto; iPureIntro.
        + rewrite /kvs_uk_sb.
          replace (z_of (0 ^+ next_free_uk)%a) with next_free_uk; first done.
          apply Z.ltb_lt in Hnext_free.
          solve_addr+Hnext_free Hwf_free_uk.
        + solve_addr+Hnext_free Hwf_free_uk.
        + solve_addr+Hnext_free Hwf_free_uk.
        + rewrite /MAX_USER_KEY; solve_addr+Hnext_free Hwf_free_uk.
      }

      iMod
        (world_interp_sealing_update' W C kvs_otype_propC KVS_OTYPE adversary_kvs_keys
          with "[$Hspred] [ ] [ ot_kvs_uk ] [$Hworld]")
        as "(Hworld & Hseal_kvs_ku)".
      { iIntros (w); iApply mono_priv_ot_kvs. }
      { rewrite normalise_sealed_words_borrow.
        rewrite big_sepS_singleton; iFrame "ot_kvs_uk".
      }
      subst W' ; set (W' := <o[ _ := adversary_kvs_keys ]o> W).

      iAssert (interp W' C (WInt ASM_TRUE))%I as "#Hw_wca0".
      { iApply interp_int. }
      iAssert (interp W' C (kvs_user_seal_key Global next_free_uk))%I as "#Hw_wca1".
      { iEval (rewrite fixpoint_interp1_eq /= /interp_sb); cbn; auto. }
      iApply "Hpost"; iFrame "∗#".
      iPureIntro.
      subst W'.
      right; eexists; done.
    - iMod ("Hkvs_inv_close" with "[$Hcode $Ha_next_uk $Ha_uk_scap Himports_sw Ha_unsealing $HisKVS $Hfree_uk_alloc $Hspred $Hna]") as "Hna" ; auto.
      { iNext.
        iSplit; last done.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }
      iAssert (interp W C (WInt ASM_FALSE))%I as "#Hw_wca0".
      { iApply interp_int. }
      iAssert (interp W C (WInt 0))%I as "#Hw_wca1".
      { iApply interp_int. }
      iApply "Hpost"; iFrame "∗#".
      iPureIntro; by left.
  Qed.

  (*** Safe entry point  *)
  Lemma kvs_initialise_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    (Nswitcher : namespace)
    :

    na_inv cerise_nais Nkvs kvs_inv ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
    inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
    inv (export_table_entryN Nkvs_exp_tbl kvs_initialise_exp_tbl_addr)
        (kvs_initialise_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_initialise) ∗
    WSealed ot_switcher (SCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_initialise_exp_tbl_addr) ↦□ₑ kvs_initialise_nargs ∗
    WSealed ot_switcher (SCap RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_initialise_exp_tbl_addr) ↦□ₑ kvs_initialise_nargs
    -∗
    ot_switcher_prop W C (WCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_initialise_exp_tbl_addr).
  Proof.
    iIntros
      "(#Hinv_kvs & #Hinv_switcher
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & #Hkvs_exp_addOrInitialise
      & #Hentry_KVS & #Hentry_KVS_borrow
      )".

    iExists g_kvs_exp_tbl, b_kvs_exp_tbl, e_kvs_exp_tbl, kvs_initialise_exp_tbl_addr,
    KVS_pcc_b, KVS_pcc_e, KVS_cgp_b, KVS_cgp_e, kvs_initialise_nargs, _, Nkvs_exp_tbl.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iFrame "#".
    iSplit; first done.
    iSplit; first by (iPureIntro; rewrite /kvs_initialise_exp_tbl_addr /kvs_initialise_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_initialise_exp_tbl_addr /kvs_initialise_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_initialise_exp_tbl_addr /kvs_initialise_exp_tbl_off; solve_addr).
    iSplit; first (iPureIntro; rewrite /kvs_initialise_nargs; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hworld_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    (* Extract the registers that we will need *)
    assert ( is_Some (rmap !! ctp) ) as [wctp Hwctp] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct0) ) as [wct0 Hwct0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    assert ( is_Some (rmap !! cnull) ) as [wcnull Hwcnull] by ( apply Hrmap_init; rewrite Hrmap_dom ; done ).
    iExtractList "Hrmap" [PC; cgp; cra ; csp ] as ["HPC"; "Hcgp"; "Hcra"; "Hcsp"].
    iExtractList "Hrmap" [ct0; ct1; ctp; cnull; ca0; ca1] as ["Hct0"; "Hct1"; "Hctp"; "Hcnull"; "Hca0"; "Hca1"].

    (* General purpose registers *)
    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }
    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & #Hstack_revoked_W0 & _ & >[%stk_mem Hstk] & [Hrevoked_l _])".
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    iApply (KVS_initialise_spec_safe (revoke W0)); try solve_ndisj; iFrame "∗#".
    iNext; iIntros (W2) "(%Hrelated_W1_W2 & Hna & HPC & Hcgp & Hcra
    & (%wca0' & Hca0 & #Hinterp_wca0) & (%wca1' & Hca1 & #Hinterp_wca1)
    & Hct0 & Hct1 & Hctp & Hcnull & Hworld_C)".
    set (Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) W2)).
    iAssert (interp Wfixed C wca0')%I with "[Hca0]" as "#Hinterp_wca0'".
    { iApply monotone.interp_monotone; last iFrame "#".
      iPureIntro; apply close_list_related_sts_pub ; eauto.
    }
    iAssert (interp Wfixed C wca1')%I with "[Hca1]" as "#Hinterp_wca1'".
    { iApply monotone.interp_monotone; last iFrame "#".
      iPureIntro; apply close_list_related_sts_pub ; eauto.
    }


    iDestruct "Hcnull" as "[% Hcnull]"; iDestruct (big_sepM_insert _ _ cnull with "[$Hrmap $Hcnull]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hctp" as "[% Hctp]"; iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hct0" as "[% Hct0]"; iDestruct (big_sepM_insert _ _ ct0 with "[$Hrmap $Hct0]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hct1" as "[% Hct1]"; iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hcra" as "[% Hcra]"; iDestruct (big_sepM_insert _ _ cra with "[$Hrmap $Hcra]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    iDestruct "Hcgp" as "[% Hcgp]"; iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap $Hcgp]") as "Hrmap".
    { repeat (rewrite lookup_insert_ne; auto); apply not_elem_of_dom_1; set_solver+. }
    map_simpl "Hrmap".

    destruct Hl_unk as [ Hnodup Htemps ]; auto.
    iApply (switcher_ret_specification _ W0 W2
             with
             "[ $Hstk $Hcstk $HK $Hworld_C $Hna $HPC $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); last iFrame "∗#"; eauto.
    { destruct Hrelated_W1_W2 as [? | (ws & ?)]; simplify_eq.
      - apply related_pub_revoke_close_list ; eauto.
      - rewrite /close_list /=.
        destruct W0 as [ [W0_std W0_cus] W0_seals ]; cbn.
        split; [|split]; cbn; auto.
        + rewrite close_revoke_eq; auto; apply related_sts_std_pub_refl.
        + apply related_sts_pub_refl.
        + split.
          { rewrite dom_insert_L; set_solver+. }
          intros o' s s' Hs Hs'.
          destruct (decide (KVS_OTYPE = o')); simplify_map_eq; first set_solver+.
          rewrite Hs in Hs'; simplify_eq; set_solver+.
    }
    { apply regmap_full_dom in Hrmap_init.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_init. set_solver+. }
    { subst csp_b. destruct Hsync_csp as [Hsync_csp <-]; eauto. }
    { intros a Ha; apply Htemps; done. }
  Qed.

End KVS_spec_initialise_safe.
