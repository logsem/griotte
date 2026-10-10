From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return switcher_spec_KtK register_tactics.
From griotte Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.

Section KVS_spec_addOrUpdate.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_namespaces : kvs_namespaces}
  .

  (*** KVS INSERT: Key in the KVS *)
  Lemma KVS_update_spec_layer_0
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (idx : kvs_idx_t) ( wnkey : Word )
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr (kvs_addOrUpdate_pcc_addr ^+ length kvs_addOrUpdate_instrs)%a ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    pkvs !! idx = Some (Some (kvs_full_key user_key nkey, wnkey)) ->

    ((* initial register file *)

      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ▷ (
          ⌜ canStore RW wca2 = true ⌝ ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          codefrag kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
          (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗

          is_physical_kvs KVS_cgp_b (<[idx := Some (fkey, wca2)]> pkvs)

          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hbounds_pcc Hbounds_cgp Hbounds_a_user_key His_uint16_nkey Hpkvs_idx)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
        & Hcode & Ha_unsealing & Ha_user_key
        & HPKVS & Hpost)".

    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Hct1 $Hct2 $Ha_unsealing $Ha_user_key $Hcode]") ; eauto; iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & Hct1 & Hct2 & Ha_unsealing & Ha_user_key & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Hcgp_opt & Hcgp_key & Hcgp_val
                    & HPKVS & %Hcgp_idx & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ctp ct1 (-1) *)
    iInstr "Hcode".
    (* Jnz 5 ctp *)
    iInstr "Hcode".
    { injection; intros; lia. }
    (* Lea cgp 2 *)
    iInstr "Hcode".
    { transitivity ( Some ((KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2))%a) ); last done; solve_addr+Hcgp_idx. }
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

    iDestruct (is_physical_kvs_open_wf with "HPKVS") as "[%_ %Hnodup_pkvs_keys]".
    iDestruct (kvs_physical_map_close_update with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
      as "HPKVS"; eauto.
    { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }

    iApply "Hpost"; iFrame "∗%"; done.
  Qed.

  Lemma KVS_update_spec_layer_1
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (E : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    is_Some (m !! nkey) ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)

      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ (
          ⌜ canStore RW wca2 = true ⌝ ∗
          na_own cerise_nais E ∗

          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          user_key_addr ↦ₐ WInt user_key ∗

          ↪●LKVS (<<[ (user_key, nkey):= wca2 ]>> lkvs) ∗
          is_logical_kvs (<<[ (user_key, nkey):= wca2 ]>> lkvs) ∗
          user_key ↦(LKVS) (<[ nkey := wca2 ]> m)

          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hbounds_a_user_key His_uint16_nkey [wnkey Hm_nkey])
      "(#Hkvs_inv & Hna
        & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
        & Ha_user_key
        & >Hlkvs_auth & (%pkvs & >%Hsync & >Hpkvs_frag) & >Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & (%pkvs' & HPKVS & >Hpkvs_frag')) & Hna & Hkvs_inv_close)"; eauto.

    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    pose proof (Hcgp_continuous := KVS_size_data).
    assert ((KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e) as Hbounds_cgp.
    { by rewrite /length_kvs_data in Hcgp_continuous. }

    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1)%a <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    iDestruct (region_pointsto_cons with "Himports") as "[Himports_sw Himports]"; eauto.
    iDestruct (region_pointsto_single with "Himports") as "(% & Ha_unsealing & %Heq)"; eauto; simplify_eq.
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b') as Heq_addr
       by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    rewrite -Heq_addr in H3; rewrite -Heq_addr.

    iDestruct ( kvs_physical_kvs_valid with "Hpkvs_frag Hpkvs_frag'") as "<-".

    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_Some _ _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as (idx & Hpkvs_idx).

    iDestruct (is_physical_kvs_wf with "HPKVS") as "#[_ Hnodup_pkvs]".


    iApply (KVS_update_spec_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); eauto.
    iNext; iIntros "(%Hcan_store & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                     & Hcode & Ha_unsealing & Ha_user_key
                     & HPKVS )".
    rewrite Heq_addr.
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod (kvs_physical_kvs_update (<[idx:=Some (kvs_full_key user_key nkey, wca2)]> pkvs) with
           "Hpkvs_frag Hpkvs_frag'") as "[Hpkvs_frag Hpkvs_frag']".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HPKVS $Hpkvs_frag']") as "Hna" ; auto.
    { iNext.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }

    iDestruct "Hnodup_pkvs" as "%Hnodup_pkvs".
    iMod ( kvs_logical_kvs_update user_key _ _ (<[nkey := wca2]> m) with "Hlkvs_auth Hm" ) as "[Hlkvs_auth Hm]".
    replace ( <[user_key:=<[nkey:=wca2]> m]> lkvs ) with ( <<[ (user_key, nkey):= wca2 ]>> lkvs ).
    2: { rewrite /kvs_logical_kvs_insert Hlkvs_user_key //. }
    eapply (kvs_synced_logical_kvs_update _ _ _ _ _ wca2) in Hsync; eauto.

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_update_spec_layer_2
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    is_Some (m !! nkey) ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_key ↦(LKVS) m ∗

      ▷ ( ⌜ canStore RW wca2 = true ⌝ ∗
          na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗
          user_key_addr ↦ₐ WInt user_key ∗

          user_key ↦(LKVS) (<[nkey := wca2]> m)

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_update_spec_layer_1 with
             "[- $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }

    iNext; iIntros "(%Hcan_store & Hna
                     & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & Hlkvs_auth & HLKVS & Hm)".

    iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
    iApply "Hpost"; iFrame; done.
  Qed.


  Lemma KVS_update_spec
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_kvs_inv user_key ∗
      ▷ (user_key, nkey) ↦(KVS) - ∗

      ▷ ( ⌜ canStore RW wca2 = true ⌝ ∗
          na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗
          user_key_addr ↦ₐ WInt user_key ∗

          user_kvs_inv user_key ∗
          (user_key, nkey) ↦(KVS) wca2

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & [%wk >Hk] & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_Some _ _ _ _ _ Hk) as Hm_kvs; eauto.

    iApply (KVS_update_spec_layer_2
             with "[- $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
                    $Ha_user_key
                    $Hm]"); eauto.
    iNext; iIntros "(%Hcan_store & Hna
                     & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & Hm)".

    iMod ( kvs_user_kvs_update _ _ _ _ (Some wca2) with "Hukvs_auth Hk" ) as "[Hukvs_auth Hk]".
    apply (kvs_synced_logical_user_kvs_insert _ _ nkey wca2) in Hsync.
    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_add_spec_layer_0
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr (kvs_addOrUpdate_pcc_addr ^+ length kvs_addOrUpdate_instrs)%a ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    fkey ∉ kvs_keys pkvs ->

    ((* initial register file *)

      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ▷ (
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          codefrag kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
          (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗

          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            ( ∃ idx_empty,

              ⌜ pkvs !! idx_empty = Some None ⌝ ∗
              ⌜ canStore RW wca2 = true ⌝ ∗
              ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)

              is_physical_kvs KVS_cgp_b (<[idx_empty := Some (fkey, wca2)]> pkvs)
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                is_physical_kvs KVS_cgp_b pkvs
              )
          )
           -∗
           WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hbounds_pcc Hbounds_cgp Hbounds_a_user_key His_uint16_nkey Hpkvs_idx)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
        & Hcode & Ha_unsealing & Ha_user_key
        & HPKVS & Hpost)".

    codefrag_facts "Hcode"; rename H into Hpc_contiguous; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Hct1 $Hct2 $Ha_unsealing $Ha_user_key $Hcode]") ; eauto; iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & Hct1 & Hct2 & Ha_unsealing & Ha_user_key & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "[
    (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS
    & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & %Hcgp_bounds
    & %Hidx_empty & %Hpkvs_idx_empty & Hcode)
    | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS & Hcode) ]".
    all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    - (* An empty slot was found *)
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
      (* mul ct1 ct1 ASM_SIZEOF_KVS_ENTRY *)
      iInstr "Hcode".
      (* lea cgp ct1; *)
      iInstr "Hcode".
      { transitivity (Some (KVS_cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * idx_empty)%a); solve_addr+ Hidx_empty Hcgp_bounds. }
      (* store cgp ASM_SOME; *)
      iInstr "Hcode".
      { solve_addr+Hcgp_bounds. }
      (* lea cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 1))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
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
      { transitivity (Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 2))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
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

      iDestruct (is_physical_kvs_open_wf with "HPKVS") as "[%_ %Hnodup_pkvs_keys]".
      iDestruct (kvs_physical_map_close_insert with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
        as "HPKVS"; eauto.
      { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }


      iApply "Hpost"; iFrame "∗%".
      iLeft ; iFrame; done.


    - (* No empty slot found *)


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

      iApply "Hpost"; iFrame "∗%".
      iRight ; iFrame.
  Qed.


  (*** KVS INSERT: Key not in the KVS *)
  Lemma KVS_add_spec_layer_1
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (E : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    m !! nkey = None ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ ( na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca1 ↦ᵣ WInt 0 ∗
          ca2 ↦ᵣ - ∗
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          user_key_addr ↦ₐ WInt user_key ∗

          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            ( ⌜ canStore RW wca2 = true ⌝ ∗
              ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)

              ↪●LKVS (<<[ ( user_key, nkey ) := wca2 ]>> lkvs) ∗
              is_logical_kvs (<<[ ( user_key, nkey ) := wca2 ]>> lkvs) ∗
              user_key ↦(LKVS) (<[ nkey := wca2 ]> m)
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                ↪●LKVS lkvs ∗
                is_logical_kvs lkvs ∗
                user_key ↦(LKVS) m
              )
          )
          -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hbounds_a_user_key His_uint16_nkey Hm_nkey)
      "( #Hkvs_inv & Hna
        & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
        & Ha_user_key
        & >Hlkvs_auth & (%pkvs & >%Hsync & >Hpkvs_frag) & >Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & (%pkvs' & HPKVS & >Hpkvs_frag')) & Hna & Hkvs_inv_close)"; eauto.

    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    pose proof (Hcgp_continuous := KVS_size_data).
    assert ((KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e) as Hbounds_cgp.
    { by rewrite /length_kvs_data in Hcgp_continuous. }

    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1)%a <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    iDestruct (region_pointsto_cons with "Himports") as "[Himports_sw Himports]"; eauto.
    iDestruct (region_pointsto_single with "Himports") as "(% & Ha_unsealing & %Heq)"; eauto; simplify_eq.
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b') as Heq_addr
       by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    rewrite -Heq_addr in H3; rewrite -Heq_addr.


    iDestruct ( kvs_physical_kvs_valid with "Hpkvs_frag Hpkvs_frag'") as "<-".
    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_None _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as Hpkvs_idx.


    iApply (KVS_add_spec_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                     & Hcode & Ha_unsealing & Ha_user_key
                     & [ (%idx_empty & %Hidx_empty & %Hcan_store & Hca0 & HPKVS)
                         | (Hca0 & HPKVS)
                       ] )".
    all: rewrite Heq_addr; subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
    - iMod (kvs_physical_kvs_update (<[idx_empty:=Some (kvs_full_key user_key nkey, wca2)]> pkvs) with
             "Hpkvs_frag Hpkvs_frag'") as "[Hpkvs_frag Hpkvs_frag']".
      iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HPKVS $Hpkvs_frag']") as "Hna" ; auto.
      { iNext.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }

      iMod ( kvs_logical_kvs_update user_key _ _ (<[nkey := wca2]> m) with "Hlkvs_auth Hm" ) as "[Hlkvs_auth Hm]".
      replace ( <[user_key:=<[nkey:=wca2]> m]> lkvs ) with ( <<[ (user_key, nkey):= wca2 ]>> lkvs ).
      2: { rewrite /kvs_logical_kvs_insert Hlkvs_user_key //. }
      eapply (kvs_synced_logical_kvs_insert _ _ _ _ _ wca2) in Hsync; eauto.


      iApply "Hpost"; iFrame "∗%".
      iLeft ; iFrame; done.

    - iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HPKVS $Hpkvs_frag']") as "Hna" ; auto.
      { iNext.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }

      iApply "Hpost"; iFrame "∗%".
      iRight ; iFrame.
  Qed.

  Lemma KVS_add_spec_layer_2
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    m !! nkey = None ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_key ↦(LKVS) m ∗

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
         user_key_addr ↦ₐ WInt user_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (
             ⌜ canStore RW wca2 = true ⌝ ∗
             ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
             user_key ↦(LKVS) (<[ nkey := wca2 ]> m)
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               user_key ↦(LKVS) m
             )
         )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_add_spec_layer_1 with
             "[- $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }
    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & [ (%Hcan_store & Hca0 & Hlkvs_auth & HLKVS & Hm)
                     | (Hca0 & Hlkvs_auth & HLKVS & Hm)
                     ])".
    - iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
      iApply "Hpost"; iFrame "∗%".
      iLeft ; iFrame; done.
    - iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
      iApply "Hpost"; iFrame "∗%".
      iRight ; iFrame; done.
  Qed.

  Lemma KVS_add_spec
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_kvs_inv user_key ∗
      ▷ (user_key, nkey) ↦(KVS) ⊥ ∗

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
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (
             ⌜ canStore RW wca2 = true ⌝ ∗
             ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
             (user_key, nkey) ↦(KVS) wca2
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               (user_key, nkey) ↦(KVS) ⊥
             )
         )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & >Hk & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_None _ _ _ _ Hk) as Hm_kvs; eauto.


    iApply (KVS_add_spec_layer_2
             with "[- $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
                    $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
              & Ha_user_key
              & [ (%Hcan_store & Hca0 & Hm) | (Hca0 & Hm) ] )".

    - iMod ( kvs_user_kvs_update _ _ _ _ (Some wca2) with "Hukvs_auth Hk" ) as "[Hukvs_auth Hk]".
      apply (kvs_synced_logical_user_kvs_insert _ _ nkey wca2) in Hsync.
      iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.
      iApply "Hpost"; iFrame; iLeft; iFrame; done.

    - iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.
      iApply "Hpost"; iFrame; iRight; iFrame; done.
  Qed.


  (*** KVS INSERT: Ill-formed inputs *)

  Lemma KVS_addOrUpdate_spec_not_uint16_map_key_pre
    (pc_b pc_e pc_a : Addr)
    (wret : Word)
    (wca1 : Word)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    ¬ word_is_uint16 wca1 ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         codefrag pc_a kvs_addOrUpdate_instrs
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HsubBounds Hnkey_is_uint16)
      "(HPC & Hcra & [%wca0 Hca0] & Hca1 & Hct1 & [%wcnull Hcnull] & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_not_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* mov ca0 ASM_FALSE; *)
    iInstr "Hcode".
    (* mov ca1 0; *)
    iInstr "Hcode".
    (* jalr cnull cra; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_addOrUpdate_spec_not_uint16_map_key
    (wret : Word)
    (wca1 : Word)
    (E : coPset)
    :

    ↑(Nkvs.@"physical") ⊆ E ->

    ¬ word_is_uint16 wca1 ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ -
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HE Hnkey_is_uint16)
      "(#Hkvs_inv & Hna & HPC & Hcra & Hca0 & Hca1 & Hct1 & Hcnull & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & HKVS) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    iApply ( KVS_addOrUpdate_spec_not_uint16_map_key_pre ); eauto; iFrame.
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct1 & Hcnull & Hcode)".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Himports $HKVS]") as "Hna".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_addOrUpdate_spec_invalid_sealed_user_key_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    is_uint16 nkey ->
    is_sealed_with_o wca0 KVS_OTYPE = false ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HsubBounds Hnkey_is_uint16 Hwca0 Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp
      & [%wcnull Hcnull] & Hcode & Ha_unsealing)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_invalid_sealed_user_key with "[- $HPC $Hctp $Hca0 $Hct1 $Hct2 $Ha_unsealing $Hcode]") ; eauto; iNext.
  Qed.

  Lemma KVS_addOrUpdate_spec_invalid_sealed_user_key
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    (E : coPset)
    :

    ↑(Nkvs.@"physical") ⊆ E ->

    is_uint16 nkey ->
    is_sealed_with_o wca0 KVS_OTYPE = false ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ -

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HE Hnkey_is_uint16 Hwca0)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hcnull)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & HKVS) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

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
    iApply ( KVS_addOrUpdate_spec_invalid_sealed_user_key_pre ); eauto; iFrame.
  Qed.

  Lemma KVS_add_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : Reg) (cstk : CSTK) (E : coPset)
    (user_key : user_key_t) (nkey : map_key_t)
    (l_user_key : Locality) (user_key_addr : Addr) (wnew : Word) :
    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->
    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    arg_rmap !! ca0 = Some (kvs_user_seal_key l_user_key user_key_addr) ->
    arg_rmap !! ca1 = Some (WInt nkey) ->
    arg_rmap !! ca2 = Some wnew ->
    na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
    na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv
    ⊢
    switcher_cc_specification_known_to_known_function
      (user_key_addr ↦ₐ WInt user_key ∗
       user_kvs_inv user_key ∗
       (user_key, nkey) ↦(KVS) ⊥)
      (λ wca0 wca1,
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         ⌜ wca1 = WInt 0 ⌝ ∗
         ((⌜ canStore RW wnew = true ⌝ ∗
           ⌜ wca0 = WInt ASM_TRUE ⌝ ∗
           (user_key, nkey) ↦(KVS) wnew)
          ∨
          (⌜ wca0 = WInt ASM_FALSE ⌝ ∗
           (user_key, nkey) ↦(KVS) ⊥)))
      wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk arg_rmap cstk kvs_addOrUpdate_nargs E
      KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e kvs_addOrUpdate_pcc_off.
  Proof.
    iIntros (Hphysical Hlogical Hnkey Huser_key Hca0_arg Hca1_arg Hca2_arg).
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros "[ #Hkvs #Hkvs_logical ]" (arg_rmap' rmap')
       "(%Harg_rmap' & %Hrmap' & Hna & HPC & Hcgp & Hcra & Hcsp
       & Hargs & Hrmap & Hstk & Hcstk
       & (Huser_key & Huser_kvs & Hkey)
       & Hpost)".
    iEval (cbn) in "HPC".

    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
          "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
          "[Hct0 %Hwct0]"]
    ; iClear "Hargs".
    destruct (decide (ca0 ∈ dom_arg_rmap kvs_addOrUpdate_nargs)) as [_|]; last done.
    destruct (decide (ca1 ∈ dom_arg_rmap kvs_addOrUpdate_nargs)) as [_|]; last done.
    destruct (decide (ca2 ∈ dom_arg_rmap kvs_addOrUpdate_nargs)) as [_|]; last done.
    destruct (decide (ca3 ∈ dom_arg_rmap kvs_addOrUpdate_nargs)) as [|_]; first done.
    simplify_eq.

    assert (is_Some (rmap' !! ctp)) as [wctp Hwctp].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! ct1)) as [wct1 Hwct1].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! ct2)) as [wct2 Hwct2].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    assert (is_Some (rmap' !! cnull)) as [wcnull Hwcnull].
    { apply elem_of_dom. rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    iExtractList "Hrmap" [cs0;cs1;ctp;ct1;ct2;cnull]
      as ["[Hcs0 %Hcs0]";"[Hcs1 %Hcs1]";"[Hctp %Hctp]";
          "[Hct1 %Hct1]";"[Hct2 %Hct2]";"[Hcnull %Hcnull]"]
    ; simplify_eq.

    iApply (KVS_add_spec with
      "[- $Hkvs $Hkvs_logical $Hna $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2 $Hcnull
       $Huser_key $Huser_kvs $Hkey]"); auto.
    iNext.
    iIntros "(Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & Hca1
              & [%wca2 Hca2] & [%wctp Hctp] & [%wct1 Hct1]
              & [%wct2 Hct2] & [%wcnull Hcnull]
              & Huser_key & Huser_kvs & Hres)".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].
    set (rmap_ret0 := delete cs1 (delete cs0 rmap')).
    set (rmap_ret1 := <[ctp := wctp]> rmap_ret0).
    set (rmap_ret2 := <[ct1 := wct1]> rmap_ret1).
    set (rmap_ret3 := <[ct2 := wct2]> rmap_ret2).
    set (rmap_ret4 := <[cnull := wcnull]> rmap_ret3).
    set (rmap_ret5 := <[ca2 := wca2]> rmap_ret4).
    set (rmap_ret6 := <[ca3 := WInt 0]> rmap_ret5).
    set (rmap_ret7 := <[ca4 := WInt 0]> rmap_ret6).
    set (rmap_ret8 := <[ca5 := WInt 0]> rmap_ret7).
    set (rmap_ret := <[ct0 := WInt 0]> rmap_ret8).
    iEval (cbn) in "HPC".

    iDestruct "Hres" as "[(%Hcan_store & Hca0 & Hkey) | (Hca0 & Hkey)]".
    - iApply ("Hpost" $! (WInt ASM_TRUE) (WInt 0) rmap_ret
                (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit.
      { iPureIntro.
        rewrite /rmap_ret /rmap_ret8 /rmap_ret7 /rmap_ret6 /rmap_ret5
          /rmap_ret4 /rmap_ret3 /rmap_ret2 /rmap_ret1 /rmap_ret0.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
      iFrame.
      iFrame. iSplit; first done. iLeft.
      iSplit; first done. iSplit; first done. iFrame.
    - iApply ("Hpost" $! (WInt ASM_FALSE) (WInt 0) rmap_ret
                (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
      iSplit.
      { iPureIntro.
        rewrite /rmap_ret /rmap_ret8 /rmap_ret7 /rmap_ret6 /rmap_ret5
          /rmap_ret4 /rmap_ret3 /rmap_ret2 /rmap_ret1 /rmap_ret0.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
      iFrame.
      iFrame. iSplit; first done. iRight.
      iSplit; first done. iFrame.
  Qed.

End KVS_spec_addOrUpdate.
