From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.
From cap_machine Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From cap_machine Require Import switcher_preamble switcher_spec_return.
From cap_machine Require Import proofmode map_simpl.

Section KVS_spec_erase.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** KVS erase *)
  Lemma KVS_erase_spec_safe_pre
    (Wca0 W : WORLD) (C : CmptName)
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca0 wca1 : Word)
    (m : kvs_map) (s : kvs_alloc)
    ( E : coPset )
    :

    ↑Nkvs_otype ⊆ E ->

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    (cgp_b + length kvs_data)%a = Some cgp_e ->

    related_sts_priv_world Wca0 W ->

    ((* initial register file *)
      na_own cerise_nais E ∗
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp Wca0 C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to erase *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS (cgp_b ^+ 1)%a m s ∗
      ▷ seal_pred KVS_OTYPE kvs_otype_propC ∗

      world_interp W C ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         (ca0 ↦ᵣ WInt 0 ∨ ca0 ↦ᵣ WInt (-1)%Z) ∗
         ca1 ↦ᵣ WInt 0 ∗
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         codefrag pc_a kvs_erase_instrs ∗
         cgp_b ↦ₐ kvs_service_unsealing_key ∗

         (
           (∃ idx ku kn,
             isKVS (cgp_b ^+ 1)%a (<[ idx := (EMPTY_SLOT, WInt DEFAULT_VAL) ]> m) (kvs_alloc_delete s ku {[kn]}))
         ∨
             (isKVS (cgp_b ^+ 1)%a m s)
         ) ∗

         world_interp W C

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HN HsubBounds Hcgp_contiguous Hrelated_Wca0_W)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_wca0 & Hca1 & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Hcgp_b & HKVS & #Hspred & Hworld & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_erase_instrs /assembled_kvs_erase.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros (nkey) "(-> & HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct "Hct1" as "[ (Hct1 & %Hnkey_uint16) | (Hct1 & %Hnkey_uint16)]"; cycle 1.
    {
      (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jalr cnull cra; *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      destruct (decide (ca0 = cnull)) as [|_]; first done.
      iApply "Hpost"; iFrame.
    }
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_safe with
             "[- $HPC $Hcgp $Hca0 $Hinterp_wca0 $Hca1 $Hct1 $Hcgp_b $Hcode $Hspred $Hworld]")
    ; eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros (l_user_key user_key)
      "([%Huser_key_C ->] & HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode & #Hseal_ku & Hworld)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iDestruct (sopen_world_interp_singleton with "Hspred Hseal_ku Hworld")
                as "(Hworld & Hres_open & HP)".
    iDestruct "HP" as "(%ku & %a & %s' & >%Heq & >%Hku_C & >%Hku & Hot_res)".
    iDestruct (lc_fupd_elim_later with "[$] [$Hot_res]") as ">[Halloc Hkvs_frags]".
    pose proof (kvs_users_seals_bounds C user_key Huser_key_C) as Huser_key_bound.
    assert ( wf_kvs_full_key user_key nkey) as Hwk_fkey by (split; auto; lia).
    cbn in Heq, Hku_C; simplify_eq.

    destruct ( decide ( nkey ∈ s' ) ) as [Hfkey_in_s|Hfkey_notin_s].
    (* The key has already been allocated *)
    -
      iDestruct (big_sepS_delete with "Hkvs_frags")
        as "[ [%w [ [%idx Hkvs_frag] Hinterp_w] ] Hkvs_frags]"
      ; eauto; iEval (cbn) in "Hkvs_frag".
      iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      { apply kvs_full_key_not_empty; auto. }
      iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val  & Hfkey & %Hcgp_idx & Hkvs_frag & Hcode)".
      iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
      iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
      { by apply elem_of_dom_2 in Hm_idx. }
      iEval (cbn) in "Hfkey".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".


      focus_block 5 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
      (* Sub ct1 ct1 (-1) *)
      iInstr "Hcode".
      (* Jnz 5 ct1 *)
      iInstr "Hcode".
      { injection; intros; lia. }
      (* Store cgp (-1) *)
      iInstr "Hcode".
      { solve_addr+Hcgp_idx. }
      (* Lea cgp 1 *)
      iInstr "Hcode".
      { transitivity ( Some ((cgp_b ^+ (2 + 2 * idx))%a) ); solve_addr+Hcgp_idx Hidx. }
      (* Store cgp (inr ca2) *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Store.wp_store_success_z with "[$HPC $Hi $Hcgp $Hcgp_val]"); try solve_pure.
      iNext; iIntros "(HPC & Hi & Hcgp & Hcgp_val)".
      wp_pure.
      iInstr_close "Hcode".

      (* Mov ca0 0 *)
      iInstr "Hcode".
      (* Mov ca1 0 *)
      iInstr "Hcode".
      (* Jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iMod (isKVS_open_delete _ _ _ _ idx user_key nkey _ with "HKVS Halloc Hkvs_frag") as
        "(HKVS & Halloc & Hkvs_frag)"; auto.

      iDestruct (close_isKVS with "[$HKVS Hcgp_key Hcgp_val Hkvs_frag]") as "HKVS";eauto.
      { by simplify_map_eq. }
      {
        replace (cgp_b ^+ (1 + 2 * idx))%a with ((cgp_b ^+ 1) ^+ 2 * idx)%a by solve_addr+Hidx.
        replace (cgp_b ^+ (2 + 2 * idx))%a  with ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a by solve_addr+Hidx.
        iFrame.
      }

      iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key user_key))))) with "[Halloc Hkvs_frags]"
        as "HP".
      { iExists user_key, a, (s' ∖ {[nkey]}); iFrame "∗ %".
        by replace (z_of a) with user_key by solve_addr+Hku.
      }
      iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".
      iApply "Hpost"; iFrame.

    - iApply (KVS_search_spec_notin with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Halloc $Hcode]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Halloc & Hcode)".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      focus_block 5 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
      (* Sub ct1 ct1 (-1) *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* Jnz 5 ct1 *)
      iInstr "Hcode".
      (* Jmp 4 *)
      iInstr "Hcode".
      (* Mov ca0 0 *)
      iInstr "Hcode".
      (* Mov ca1 0 *)
      iInstr "Hcode".
      (* Jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key user_key))))) with "[Halloc Hkvs_frags]"
        as "HP".
      { iExists user_key, a, s'; iFrame "∗ %".
        by replace (z_of a) with user_key by solve_addr+Hku.
      }
      iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".
      iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_erase_spec_safe
    (Wca0 W : WORLD) (C : CmptName)
    (wret wca0 wca1 : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->
    ↑Nkvs_otype ⊆ E ->

    related_sts_priv_world Wca0 W ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp Wca0 C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to update *)
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
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         world_interp W C

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hnkvs_E Hnkvs_otype_E Hrelated_Wca0_W)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_ca0
      & Hca1 & Hct1 & Hct2 & Hcnull & Hworld & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & >Himports & >Hcode & >Hcgp_b & HisKVS & #Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr (kvs_erase_pcc_addr ^+ length kvs_erase_instrs)%a) as HSubBounds.
    { rewrite /kvs_erase_pcc_addr; cbn in *; solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 2 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_erase = kvs_erase_pcc_addr)
      as -> by (rewrite /kvs_erase_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_erase).
    iApply (KVS_erase_spec_safe_pre with "[- $HPC]"); last iFrame "∗#"; eauto.
    { pose proof Nkvs_namespaces_disjoint as (?&?&?); solve_ndisj. }
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hcnull
     & Hcode & Hcgp_b & HKVS & Hworld)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iDestruct "HKVS" as "[ (%idx & %ku & %kn & HKVS) | HKVS ]".
    all: iMod ("Hkvs_inv_close" with "[$Hna $Himports $Hcode $Hcgp_b $HKVS $Hspred]") as "Hna".
    all: iApply "Hpost"; iFrame.
  Qed.


  (*** Safe entry point  *)
  Lemma kvs_erase_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    (Nswitcher : namespace)
    :

    na_inv cerise_nais Nkvs kvs_inv ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
    inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
    inv (export_table_entryN Nkvs_exp_tbl kvs_erase_exp_tbl_addr)
        (kvs_erase_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_erase) ∗
    WSealed ot_switcher (SCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr) ↦□ₑ kvs_erase_nargs ∗
    WSealed ot_switcher (SCap RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr) ↦□ₑ kvs_erase_nargs
    -∗
    ot_switcher_prop W C (WCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
  Proof.
    iIntros
      "(#Hinv_kvs & #Hinv_switcher
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & #Hkvs_exp_addOrErase
      & #Hentry_KVS & #Hentry_KVS_borrow
      )".

    iExists g_kvs_exp_tbl, b_kvs_exp_tbl, e_kvs_exp_tbl, kvs_erase_exp_tbl_addr,
    KVS_pcc_b, KVS_pcc_e, KVS_cgp_b, KVS_cgp_e, kvs_erase_nargs, _, Nkvs_exp_tbl.
    pose proof kvs_exp_tbl_size as Hkvs_exp_tbl_size.
    rewrite /length_kvs_exports_tbl /kvs_nb_exports in Hkvs_exp_tbl_size.
    iFrame "#".
    iSplit; first done.
    iSplit; first by (iPureIntro; rewrite /kvs_erase_exp_tbl_addr /kvs_erase_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_erase_exp_tbl_addr /kvs_erase_exp_tbl_off; solve_addr).
    iSplit; first by (iPureIntro; rewrite /kvs_erase_exp_tbl_addr /kvs_erase_exp_tbl_off; solve_addr).
    iSplit; first (iPureIntro; rewrite /kvs_erase_nargs; lia).
    iIntros "!> %W0 %Hpriv_W_W0 !> %cstk %Ws %Cs %rmap %csp_b' %csp_e".
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hworld_C & %Hsync_csp & Hcstk & Hna)".
    iDestruct "Hregister_state" as
      "(%Hrmap_init & %HPC & %Hcgp & %Hcra & %Hcsp & #Hinterp_W0_csp & Hinterp_rmap & Hzeroed_rmap)".
    rewrite /interp_conf.
    rewrite /registers_pointsto.

    (* Extract the registers that we will need *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    (* General purpose registers *)
    assert ( is_Some (rmap !! ct1) ) as [wct1 Hwct1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ct2) ) as [wct2 Hwct2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! cnull) ) as [wcnull Hwcnull].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first by simplify_map_eq.
    (* Argument registers *)
    assert ( is_Some (rmap !! ca0) ) as [wca0 Hwca0].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert ( is_Some (rmap !! ca1) ) as [wca1 Hwca1].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.

    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_erase_nargs. }

    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜std W0 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }

    iMod (world_interp_revoke_stack with "[$Hinterp_W0_csp $Hworld_C]")
        as (l) "(%Hl_unk & Hworld_C & #Hstack_revoked_W0 & _ & >[%stk_mem Hstk] & [Hrevoked_l _])".
    set (W1 := revoke W0).
    assert (related_sts_priv_world W0 W1) as Hrelared_priv_W0_W1 by eapply revoke_related_sts_priv_world.

    iApply (KVS_erase_spec_safe W0 (revoke W0)); try solve_ndisj; iFrame "#∗".
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hcnull & Hworld_C)".
    set (Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) (revoke W0))).
    iAssert (∃ wca0', ca0 ↦ᵣ wca0' ∗ interp Wfixed C wca0')%I with "[Hca0]" as "(%wca0' & Hca0 & #Hinterp_wca0')".
    { iDestruct "Hca0" as "[$|$]"; iApply interp_int. }
    iAssert (∃ wca1', ca1 ↦ᵣ wca1' ∗ interp Wfixed C wca1')%I with "[Hca1]" as "(%wca1' & Hca1 & #Hinterp_wca1')".
    { iFrame "Hca1"; iApply interp_int. }


    iDestruct "Hcnull" as "[% Hcnull]"; iDestruct (big_sepM_insert _ _ cnull with "[$Hrmap $Hcnull]") as "Hrmap".
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

    destruct Hl_unk as [ Hnodup Htemps ]; auto.
    iApply (switcher_ret_specification _ W0 (revoke W0)
             with
             "[ $Hstk $Hcstk $HK $Hworld_C $Hna $HPC $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ); last iFrame "∗#"; eauto.
    { apply related_pub_revoke_close_list; eauto. }
    { apply regmap_full_dom in Hrmap_init.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_init. set_solver+. }
    { subst csp_b. destruct Hsync_csp as [Hsync_csp <-]; eauto. }
    { intros a Ha; apply Htemps; done. }
  Qed.

End KVS_spec_erase.
