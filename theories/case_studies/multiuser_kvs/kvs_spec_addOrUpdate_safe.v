From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import proofmode map_simpl register_tactics.

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
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification from unknown *)
  Lemma KVS_addOrupdate_spec_safe_pre
    (Wca W : WORLD) (C : CmptName)
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca0 wca1 wca2 : Word)
    (m : kvs_map) (s : kvs_alloc)
    ( E : coPset )
    :

    ↑Nkvs_otype ⊆ E ->

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    (cgp_b + length kvs_data)%a = Some cgp_e ->

    related_sts_priv_world Wca W ->

    ( (* initial register file *)
      na_own cerise_nais E ∗
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp Wca C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ interp Wca C wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS cgp_b m s ∗
      ▷ seal_pred KVS_OTYPE kvs_otype_propC ∗

      world_interp W C ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         codefrag pc_a kvs_addOrUpdate_instrs ∗
         (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (∃ idx (k : Z*Z) w,
               (ca0 ↦ᵣ WInt ASM_TRUE ∗ isKVS cgp_b (<[idx := Some (kvs_full_key k.1 k.2, w)]> m) s))
           ∨
             (* THERE IS AN EMPTY SLOT AVAILABLE *)
             (∃ idx (k : Z*Z) w,
                 ca0 ↦ᵣ WInt ASM_TRUE ∗
                 isKVS cgp_b (<[ idx := Some (kvs_full_key k.1 k.2, w)]> m) (kvs_alloc_insert s k.1 {[k.2]} ) )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE *)
             (ca0 ↦ᵣ WInt ASM_FALSE ∗ isKVS cgp_b m s)
         ) ∗

         world_interp W C

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HN HsubBounds Hcgp_contiguous Hrelated_Wca_W)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_wca0 & Hca1 & Hca2 & #Hinterp_wca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Ha_unsealing & HKVS & #Hspred & Hworld & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
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
      iRight;iRight;iFrame.
    }
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.

    iApply (KVS_getFullKey_spec_safe with
             "[- $HPC $Hctp $Hca0 $Hinterp_wca0 $Hca1 $Hct1 $Hct2 $Ha_unsealing $Hcode $Hspred $Hworld]")
    ; eauto; iNext.
    iIntros (l_user_key user_key)
      "([%Huser_key_C ->] & HPC & Hctp & Hca0 & Hca1 & Hct1 & Hct2 & Ha_unsealing & Hcode & #Hseal_ku & Hworld)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode" with "Hlc".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iDestruct (sopen_world_interp_singleton with "Hspred Hseal_ku Hworld")
                as "(Hworld & Hres_open & HP)".
    iDestruct "HP" as "(%ku & %a & %s' & >%Heq & >%Hku_C & >%Hku & Hot_res)".
    iDestruct (lc_fupd_elim_later with "[$] [$Hot_res]") as ">[Halloc Hkvs_frags]".
    pose proof (kvs_users_seals_bounds C user_key Huser_key_C) as Huser_key_bound.
    assert ( wf_kvs_full_key user_key nkey) as Hwk_fkey by (split; auto; lia).
    cbn in Heq, Hku_C; simplify_eq.

    destruct ( decide ( nkey ∈ s' ) ) as [Hfkey_in_s|Hfkey_notin_s].
    (* The key has already been allocated *)
    - iDestruct (big_sepS_elem_of_acc with "Hkvs_frags")
        as "[ [%w [ [%idx Hkvs_frag] Hinterp_w] ] Hkvs_frags]"
      ; eauto; iEval (cbn) in "Hkvs_frag".
      iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HKVS & Hcgp_opt & Hcgp_key & Hcgp_val & Hkvs_frag & %Hcgp_idx & Hcode)".
      iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
      iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
      { by apply elem_of_dom_2 in Hm_idx. }
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
      (* Sub ctp ct1 (-1) *)
      iInstr "Hcode".
      (* Jnz 5 ctp *)
      iInstr "Hcode".
      { injection; intros; lia. }
      (* Lea cgp 2 *)
      iInstr "Hcode".
      { transitivity ( Some ((cgp_b ^+ (3 * idx + 2))%a) ); solve_addr+Hcgp_idx Hidx. }
      (* Store cgp (inr ca2) *)
      destruct (canStore RW wca2) eqn:HcanStore_wca2; cycle 1.
      {
       iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (rules_Store.wp_store_fail_reg_perm with "[$HPC $Hi $Hca2 $Hcgp]"); try solve_pure.
        iNext; iIntros "_".
        wp_pure; wp_end; iIntros "%Hcontr";done.
      }
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca2 $Hcgp $Hcgp_val]"); try solve_pure.
      iNext; iIntros "(HPC & Hi & Hca2 & Hcgp & Hcgp_val)".
      wp_pure.
      iInstr_close "Hcode".

      (* Mov ca0 0 *)
      iInstr "Hcode".
      (* Mov ca1 0 *)
      iInstr "Hcode".
      (* Jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iMod (isKVS_open_update _ _ _ idx (kvs_full_key user_key nkey) _ wca2 with "HKVS Hkvs_frag") as "[HKVS Hkvs_frag]".

      iDestruct (close_isKVS with "[$HKVS Hcgp_opt Hcgp_key Hcgp_val]") as "HKVS";eauto.
      { by simplify_map_eq. }
      { iFrame. }

      iDestruct ("Hkvs_frags" with "[$Hkvs_frag]") as "Hkvs_frags"; eauto.
      { cbn ; iIntros (W' Hrelated_W_W').
        iApply (monotone.interp_monotone_nl with "[] [] [$Hinterp_wca2]"); iPureIntro.
        + eapply related_sts_priv_trans_world; eauto.
        + eapply (canStore_global_nonisWL RW); done.
      }

      iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key user_key))))) with "[Halloc Hkvs_frags]"
        as "HP".
      { iExists user_key, a, s'; iFrame "∗ %".
        by replace (z_of a) with user_key by solve_addr+Hku.
      }
      iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

      iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Ha_unsealing Hworld".
      iLeft; iExists idx, (user_key, nkey), wca2; iFrame.

    (* The key has never been allocated *)
    - iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Halloc $Hcode]"); eauto.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "[
      (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Halloc & HKVS
      & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & Hfkey & %Hcgp_bounds & %Hidx_empty & Hcode)
      | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Halloc & HKVS & Hcode) ]".
      all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
      + (* An empty slot was found *)

        focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
        (* sub ctp ctp (-1)%Z; *)
        iInstr "Hcode".
        replace (-1 - -1)%Z with 0%Z by lia.
        (* jnz (".addOrUpdate_key_found")%asm ctp; *)
        iInstr "Hcode".
        (* sub ctp ct1 (-1)%Z; *)
        iInstr "Hcode".
        (* jnz (".addOrUpdate_empty_slot_found")%asm ctp; *)
        iInstr "Hcode".
        { intro; simplify_eq; lia. }
        (* mul ct1 ct1 3 *)
        iInstr "Hcode".
        (* lea cgp ct1; *)
        iInstr "Hcode".
        { transitivity (Some (cgp_b ^+ 3 * idx_empty)%a); solve_addr+ Hidx_empty Hcgp_bounds. }
        (* store cgp ASM_SOME; *)
        iInstr "Hcode".
        { solve_addr+Hcgp_bounds. }
        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some (cgp_b ^+ (3 * idx_empty + 1))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
        (* store cgp ca0; *)
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca0 $Hcgp $Hcgp_key]"); try solve_pure.
        { solve_addr+Hcgp_bounds. }
        { done. }
        iNext; iIntros "(HPC & Hi & Hca0 & Hcgp & Hcgp_key)".
        wp_pure.
        iInstr_close "Hcode".
        (* lea cgp 1; *)
        iInstr "Hcode".
        { transitivity (Some (cgp_b ^+ (3 * idx_empty + 2))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
        (* store cgp ca2; *)
        destruct (canStore RW wca2) eqn:HcanStore_wca2; cycle 1.
        {
          iInstr_lookup "Hcode" as "Hi" "Hcode".
          wp_instr.
          iApply (rules_Store.wp_store_fail_reg_perm with "[$HPC $Hi $Hca2 $Hcgp]"); try solve_pure.
          iNext; iIntros "_".
          wp_pure; wp_end; iIntros "%Hcontr";done.
        }
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca2 $Hcgp $Hcgp_val]"); try solve_pure.
        iNext; iIntros "(HPC & Hi & Hca2 & Hcgp & Hcgp_val)".
        wp_pure.
        iInstr_close "Hcode".
        (* mov ca0 ASM_TRUE; *)
        iInstr "Hcode".
        (* mov ca1 0; *)
        iInstr "Hcode".
        (* jalr cnull cra; *)
        iInstr "Hcode".
        subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

        iMod (isKVS_open_insert _ _ _ _ _ _ _ wca2 with "HKVS Halloc Hfkey") as "(HKVS & Halloc & Hfkey)"; eauto.
        iDestruct (close_isKVS with "[$HKVS Hcgp_opt Hcgp_key Hcgp_val]") as "HKVS";eauto.
        { by simplify_map_eq. }
        { iFrame. }

        iDestruct ( big_sepS_insert with "[$Hkvs_frags Hfkey]") as "Hkvs_frags";eauto.
        { iExists wca2; iFrame.
          cbn; iIntros (W' Hrelated_W_W').
          iApply (monotone.interp_monotone_nl with "[] [] [$Hinterp_wca2]"); iPureIntro.
          + eapply related_sts_priv_trans_world; eauto.
          + eapply (canStore_global_nonisWL RW); done.
        }

        iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key user_key))))) with "[Halloc Hkvs_frags]"
          as "HP".
        { iExists user_key, a, ({[nkey]} ∪ s'); iFrame "∗ %".
          by replace (z_of a) with user_key by solve_addr+Hku.
        }
        iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

        iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Ha_unsealing Hworld".
        iRight; iLeft; iExists idx_empty, (user_key, nkey), wca2; iFrame.

      + (* No empty slot found *)
        focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
        (* sub ct1 ct1 (-1)%Z; *)
        iInstr "Hcode".
        replace (-1 - -1)%Z with 0%Z by lia.
        (* jnz (".addOrUpdate_key_found")%asm ctp; *)
        iInstr "Hcode".
        (* sub ct1 ct1 (-1)%Z; *)
        iInstr "Hcode".
        replace (-1 - -1)%Z with 0%Z by lia.
        (* jnz (".addOrUpdate_empty_slot_found")%asm ct1; *)
        iInstr "Hcode".
        (* mov ca0 ASM_FALSE; *)
        iInstr "Hcode".
        (* mov ca1 0; *)
        iInstr "Hcode".
        (* jalr cnull cra; *)
        iInstr "Hcode".
        subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

        iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap l_user_key user_key))))) with "[Halloc Hkvs_frags]"
          as "HP".
        { iExists user_key, a, s'; iFrame "∗ %".
          by replace (z_of a) with user_key by solve_addr+Hku.
        }
        iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

        iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Ha_unsealing Hworld".
        iRight; iRight; iFrame.
  Qed.

  Lemma KVS_addOrupdate_spec_safe
    (Wca W : WORLD) (C : CmptName)
    (wret wca0 wca1 wca2 : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->
    ↑Nkvs_otype ⊆ E ->

    related_sts_priv_world Wca W ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
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
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_ca0
      & Hca1 & Hca2 & Hinterp_ca2 & Hctp & Hct1 & Hct2 & Hcnull & Hworld & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & >Himports & >Hcode & HisKVS & #Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.
    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1)%a <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    iDestruct (region_pointsto_cons with "Himports") as "[Himports_sw Himports]"; eauto.
    iDestruct (region_pointsto_single with "Himports") as "(% & Ha_unsealing & %Heq)"; eauto; simplify_eq.

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    iApply (KVS_addOrupdate_spec_safe_pre _ _ _ _ _ _ _ _ _ wca0 with "[- $HPC]"); last iFrame "∗#"; eauto.
    { pose proof Nkvs_namespaces_disjoint as (?&?&?); solve_ndisj. }

    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & Hcode & Ha_unsealing & HKVS & Hworld)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iDestruct "HKVS" as
      "[ (%idx & %k & %w & Hca0 & HKVS) | [ (%idx & %k & %w & Hca0 & HKVS) | (Hca0 & HKVS) ] ]".
    all: iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HKVS $Hspred]") as "Hna"
    ; auto; last ( iApply "Hpost"; iFrame ; try (iLeft; iFrame; done) ; try (iRight; iFrame; done)).
    all: iNext.
    all: iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
    all: iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
    all: rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
  Qed.


  (*** Safe entry point  *)
  Lemma kvs_addOrUpdate_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    (Nswitcher : namespace)
    :

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
      "(#Hinv_kvs & #Hinv_switcher
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
