From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl.
From griotte Require Import logrel rules.
From griotte Require Import world_interp_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_base switcher_base_ktk register_tactics.
From griotte Require Import
  kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.

Section KVS_spec_addOrUpdate.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf}
  .

  (*** KVS INSERT: Key in the KVS *)
  Lemma KVS_update_spec_layer_0
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (idx : kvs_idx_t) ( wnkey : LWord )
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    SubBounds KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr (kvs_addOrUpdate_pcc_addr ^+ length kvs_addOrUpdate_instrs) ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    is_uint16 nkey ->

    pkvs !! idx = Some (Some (kvs_full_key user_key nkey, wnkey)) ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ((* initial register file *)

      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ( ▷ (
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)

          codefrag_pers kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
          (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗

          is_physical_kvs KVS_cgp_b (<[idx := Some (fkey, lstore_word RW wca2)]> pkvs)

          -∗ safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hbounds_pcc Hbounds_cgp Hbounds_a_user_key His_uint16_nkey Hpkvs_idx Htgt)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
        & #Hcode_main & #Ha_unsealing & Ha_user_key
        & HPKVS & Hpost)".

    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_addOrUpdate_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    (* jnez (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 2 "Hcode_main" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcode_main" as hcode
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Ha_unsealing $Ha_user_key $Hcode]") ; eauto.
    { kvs_getFullKey_offset. }
    iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & _ & Ha_user_key & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 3 "Hcode_main" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcode_main" as hcode ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 4 "Hcode_main" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_lea.
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto using KVS_cgp_disjoint_from_shadow.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Hcgp_opt & Hcgp_key & Hcgp_val
                    & HPKVS & %Hcgp_idx & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 5 "Hcode_main" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_search.
    (* Sub ctp ct1 (-1) *)
    iInstr "Hcode".
    (* Jne 5 ctp 0 *)
    iInstr "Hcode".
    { apply nonZero_WInt; injection; intros; lia. }
    (* Lea cgp cgp 2 *)
    iInstr "Hcode".
    { transitivity ( Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2)) ); last done; solve_addr+Hcgp_idx. }
    iPoseProof deref_res_none as "-#Hdw".
    (* Store cgp (inr ca2) 0 *)
    iInstrApply "Hcode" rules_Store.wp_store_success_reg_store_word
      with "[$HPC $Hca2 $Hcgp $Hcgp_val $Hdw]"
      as "(HPC & Hca2 & Hcgp & Hcgp_val & _)".
    { eapply disjoint_from_shadow_not_in; first exact KVS_cgp_disjoint_from_shadow.
      solve_addr+Hcgp_idx. }

    (* Mov ca0 0 *)
    iInstr "Hcode".
    (* Mov ca1 0 *)
    iInstr "Hcode".
    iDestruct (is_physical_kvs_open_wf with "HPKVS") as "[%_ %Hnodup_pkvs_keys]".
    iDestruct (kvs_physical_map_close_update with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
      as "HPKVS"; eauto.
    { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }
    (* Jalr cnull cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    iApply "Hpost"; iFrame "∗% Hcode_main Ha_unsealing"; done.
  Qed.

  Lemma KVS_update_spec_layer_1
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (F : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->

    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    is_uint16 nkey ->

    is_Some (m !! nkey) ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)

      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ (
          na_own (tpool th) F ∗

          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)

          user_key_addr ↦ₐ WInt user_key ∗

          ↪●LKVS (<<[ (user_key, nkey):= lstore_word RW wca2 ]>> lkvs) ∗
          is_logical_kvs (<<[ (user_key, nkey):= lstore_word RW wca2 ]>> lkvs) ∗
          user_key ↦(LKVS) (<[ nkey := lstore_word RW wca2 ]> m)

          -∗ safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hbounds_a_user_key His_uint16_nkey [wnkey Hm_nkey] Htgt)
      "(#Hkvs_static & #Hkvs_inv & Hna
        & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
        & Ha_user_key
        & >Hlkvs_auth & (%pkvs & >%Hsync & >Hpkvs_frag) & >Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%pkvs' & HPKVS & >Hpkvs_frag') & Hna & Hkvs_inv_close)"; eauto.
    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct "Hkvs_static" as "[_ #Hcode_main]".

    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    pose proof (Hcgp_continuous := KVS_size_data).
    assert ((KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e) as Hbounds_cgp.
    { by rewrite /length_kvs_data in Hcgp_continuous. }

    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1) <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b') as Heq_addr
       by (rewrite /kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_pcc_off_eq; solve_addr+HKVS_pcc_b').
    rewrite -Heq_addr in H3; rewrite -Heq_addr.

    iDestruct ( kvs_physical_kvs_valid with "Hpkvs_frag Hpkvs_frag'") as "<-".

    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_Some _ _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as (idx & Hpkvs_idx).

    iDestruct (is_physical_kvs_wf with "HPKVS") as "#[_ Hnodup_pkvs]".


    iApply (KVS_update_spec_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
                     & _ & _ & Ha_user_key
                     & HPKVS )".
    rewrite Heq_addr.
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    iMod (kvs_physical_kvs_update (<[idx:=Some (kvs_full_key user_key nkey, lstore_word RW wca2)]> pkvs) with
           "Hpkvs_frag Hpkvs_frag'") as "[Hpkvs_frag Hpkvs_frag']".

    iMod ("Hkvs_inv_close" with "[$Hna $HPKVS $Hpkvs_frag']") as "Hna" ; auto.

    iDestruct "Hnodup_pkvs" as "%Hnodup_pkvs".
    iMod ( kvs_logical_kvs_update user_key _ _ (<[nkey := lstore_word RW wca2]> m) with "Hlkvs_auth Hm" ) as "[Hlkvs_auth Hm]".
    replace ( <[user_key:=<[nkey:=lstore_word RW wca2]> m]> lkvs ) with ( <<[ (user_key, nkey):= lstore_word RW wca2 ]>> lkvs ).
    2: { rewrite /kvs_logical_kvs_insert Hlkvs_user_key //. }
    eapply (kvs_synced_logical_kvs_update _ _ _ _ _ (lstore_word RW wca2)) in Hsync; eauto.

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_update_spec_layer_2
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (F : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->

    is_Some (m !! nkey) ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_key ↦(LKVS) m ∗

      ▷ ( na_own (tpool th) F ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)
          user_key_addr ↦ₐ WInt user_key ∗

          user_key ↦(LKVS) (<[nkey := lstore_word RW wca2]> m)

         -∗ safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey Htgt)
      "(#Hkvs_static & #Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_update_spec_layer_1 with
             "[- $Hkvs_static $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }

    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
                     & Ha_user_key
                     & Hlkvs_auth & HLKVS & Hm)".

    iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
    iApply "Hpost"; iFrame; done.
  Qed.


  Lemma KVS_update_spec
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (F : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_kvs_inv user_key ∗
      ▷ (user_key, nkey) ↦(KVS) - ∗

      ▷ ( na_own (tpool th) F ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)
          user_key_addr ↦ₐ WInt user_key ∗

          user_kvs_inv user_key ∗
          (user_key, nkey) ↦(KVS) (lstore_word RW wca2)

         -∗ safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Htgt)
      "(#Hkvs_static & #Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
      & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & [%wk >Hk] & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_Some _ _ _ _ _ Hk) as Hm_kvs; eauto.

    iApply (KVS_update_spec_layer_2
             with "[- $Hkvs_static $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
                    $Ha_user_key
                    $Hm]"); eauto.
    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
                     & Ha_user_key
                     & Hm)".

    iMod ( kvs_user_kvs_update _ _ _ _ (Some (lstore_word RW wca2)) with "Hukvs_auth Hk" ) as "[Hukvs_auth Hk]".
    apply (kvs_synced_logical_user_kvs_insert _ _ nkey (lstore_word RW wca2)) in Hsync.
    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_add_spec_layer_0
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    SubBounds KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr (kvs_addOrUpdate_pcc_addr ^+ length kvs_addOrUpdate_instrs) ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    is_uint16 nkey ->

    fkey ∉ kvs_keys pkvs ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ((* initial register file *)

      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ( ▷ (
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)

          codefrag_pers kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_instrs ∗
          (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗

          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            ( ∃ idx_empty,

              ⌜ pkvs !! idx_empty = Some None ⌝ ∗
              ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)

              is_physical_kvs KVS_cgp_b (<[idx_empty := Some (fkey, lstore_word RW wca2)]> pkvs)
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                is_physical_kvs KVS_cgp_b pkvs
              )
          )
           -∗
           safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hbounds_pcc Hbounds_cgp Hbounds_a_user_key His_uint16_nkey Hpkvs_idx Htgt)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
        & #Hcode_main & #Ha_unsealing & Ha_user_key
        & HPKVS & Hpost)".

    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_addOrUpdate_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    (* jnez (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 2 "Hcode_main" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcode_main" as hcode
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Ha_unsealing $Ha_user_key $Hcode]") ; eauto.
    { kvs_getFullKey_offset. }
    iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & _ & Ha_user_key & _)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 3 "Hcode_main" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcode_main" as hcode ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 4 "Hcode_main" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_lea.
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto using KVS_cgp_disjoint_from_shadow.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "[
    (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS
    & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & %Hcgp_bounds
    & %Hidx_empty & %Hpkvs_idx_empty & _)
    | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS & _) ]".
    all: unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    - (* An empty slot was found *)
      focus_block 5 "Hcode_main" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_search.
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnez (".addOrUpdate_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* sub ctp ct1 (-1)%Z; *)
      iInstr "Hcode".
      (* jnez (".addOrUpdate_empty_slot_found")%asm ctp; *)
      iInstr "Hcode".
      { apply nonZero_WInt; intros Hcontra; inversion Hcontra; lia. }
      (* mul ct1 ct1 ASM_SIZEOF_KVS_ENTRY *)
      iInstr "Hcode".
      (* lea cgp cgp ct1; *)
      iInstr "Hcode".
      { transitivity (Some (KVS_cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * idx_empty)%a); solve_addr+ Hidx_empty Hcgp_bounds. }
      (* store cgp ASM_SOME; *)
      iInstr "Hcode".
      { eapply disjoint_from_shadow_not_in; first exact KVS_cgp_disjoint_from_shadow.
        solve_addr+Hcgp_bounds. }
      { solve_addr+Hcgp_bounds. }
      (* lea cgp cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 1))); solve_addr+ Hidx_empty Hcgp_bounds. }
      iPoseProof deref_res_none as "-#Hdw".
      (* store cgp ca0; *)
      iInstrApply "Hcode" rules_Store.wp_store_success_reg
        with "[$HPC $Hca0 $Hcgp $Hcgp_key $Hdw]"
        as "(HPC & Hca0 & Hcgp & Hcgp_key & _)".
      { eapply disjoint_from_shadow_not_in; first exact KVS_cgp_disjoint_from_shadow.
        solve_addr+Hcgp_bounds. }
      { solve_addr+Hcgp_bounds. }
      (* lea cgp cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some (KVS_cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 2))); solve_addr+ Hidx_empty Hcgp_bounds. }
      iPoseProof deref_res_none as "-#Hdw".
      (* store cgp ca2; *)
      iInstrApply "Hcode" rules_Store.wp_store_success_reg_store_word
        with "[$HPC $Hca2 $Hcgp $Hcgp_val $Hdw]"
        as "(HPC & Hca2 & Hcgp & Hcgp_val & _)".
      { eapply disjoint_from_shadow_not_in; first exact KVS_cgp_disjoint_from_shadow.
        exact Hcgp_bounds. }
      (* mov ca0 ASM_TRUE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      iDestruct (is_physical_kvs_open_wf with "HPKVS") as "[%_ %Hnodup_pkvs_keys]".
      iDestruct (kvs_physical_map_close_insert with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
        as "HPKVS"; eauto.
      { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }
      (* jalr cnull cra; *)
      iInstr "Hcode".
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iApply "Hpost"; iFrame "∗% Hcode_main Ha_unsealing".
      iLeft ; iFrame; done.


    - (* No empty slot found *)


      focus_block 5 "Hcode_main" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcode_main" as hcode; clear dependent Ha_search.
      (* sub ct1 ct1 (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnez (".addOrUpdate_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* sub ct1 ct1 (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnez (".addOrUpdate_empty_slot_found")%asm ct1; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jalr cnull cra; *)
      iInstr "Hcode".
      unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
      iApply "Hpost"; iFrame "∗% Hcode_main Ha_unsealing".
      iRight ; iFrame.
  Qed.


  (*** KVS INSERT: Key not in the KVS *)
  Lemma KVS_add_spec_layer_1
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (F : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->

    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    is_uint16 nkey ->

    m !! nkey = None ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ ( na_own (tpool th) F ∗
          PC ↦ₚ[th] lupdatePcPerm wret ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] WInt 0 ∗
          ca2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - ∗ (* scratch *)
          ct1 ↦ᵣ[th] - ∗ (* scratch *)
          ct2 ↦ᵣ[th] - ∗ (* scratch *)

          user_key_addr ↦ₐ WInt user_key ∗

          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            ( ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)

              ↪●LKVS (<<[ ( user_key, nkey ) := lstore_word RW wca2 ]>> lkvs) ∗
              is_logical_kvs (<<[ ( user_key, nkey ) := lstore_word RW wca2 ]>> lkvs) ∗
              user_key ↦(LKVS) (<[ nkey := lstore_word RW wca2 ]> m)
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                ↪●LKVS lkvs ∗
                is_logical_kvs lkvs ∗
                user_key ↦(LKVS) m
              )
          )
          -∗
          safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hbounds_a_user_key His_uint16_nkey Hm_nkey Htgt)
      "( #Hkvs_static & #Hkvs_inv & Hna
        & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
        & Ha_user_key
        & >Hlkvs_auth & (%pkvs & >%Hsync & >Hpkvs_frag) & >Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%pkvs' & HPKVS & >Hpkvs_frag') & Hna & Hkvs_inv_close)"; eauto.
    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct "Hkvs_static" as "[_ #Hcode_main]".

    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    pose proof (Hcgp_continuous := KVS_size_data).
    assert ((KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e) as Hbounds_cgp.
    { by rewrite /length_kvs_data in Hcgp_continuous. }

    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1) <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b') as Heq_addr
       by (rewrite /kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_pcc_off_eq; solve_addr+HKVS_pcc_b').
    rewrite -Heq_addr in H3; rewrite -Heq_addr.


    iDestruct ( kvs_physical_kvs_valid with "Hpkvs_frag Hpkvs_frag'") as "<-".
    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_None _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as Hpkvs_idx.


    iApply (KVS_add_spec_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
                     & _ & _ & Ha_user_key
                     & [ (%idx_empty & %Hidx_empty & Hca0 & HPKVS)
                         | (Hca0 & HPKVS)
                       ] )".
    all: rewrite Heq_addr; unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.
    - iMod (kvs_physical_kvs_update (<[idx_empty:=Some (kvs_full_key user_key nkey, lstore_word RW wca2)]> pkvs) with
             "Hpkvs_frag Hpkvs_frag'") as "[Hpkvs_frag Hpkvs_frag']".
      iMod ("Hkvs_inv_close" with "[$Hna $HPKVS $Hpkvs_frag']") as "Hna" ; auto.

      iMod ( kvs_logical_kvs_update user_key _ _ (<[nkey := lstore_word RW wca2]> m) with "Hlkvs_auth Hm" ) as "[Hlkvs_auth Hm]".
      replace ( <[user_key:=<[nkey:=lstore_word RW wca2]> m]> lkvs ) with ( <<[ (user_key, nkey):= lstore_word RW wca2 ]>> lkvs ).
      2: { rewrite /kvs_logical_kvs_insert Hlkvs_user_key //. }
      eapply (kvs_synced_logical_kvs_insert _ _ _ _ _ (lstore_word RW wca2)) in Hsync; eauto.


      iApply "Hpost"; iFrame "∗%".
      iLeft ; iFrame; done.

    - iMod ("Hkvs_inv_close" with "[$Hna $HPKVS $Hpkvs_frag']") as "Hna" ; auto.

      iApply "Hpost"; iFrame "∗%".
      iRight ; iFrame.
  Qed.

  Lemma KVS_add_spec_layer_2
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (F : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->

    m !! nkey = None ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_key ↦(LKVS) m ∗

      ▷ (na_own (tpool th) F ∗
         PC ↦ₚ[th] lupdatePcPerm wret ∗
         cgp ↦ᵣ[th] - ∗
         cra ↦ᵣ[th] - ∗
         ca1 ↦ᵣ[th] WInt 0 ∗
         ca2 ↦ᵣ[th] - ∗
         ctp ↦ᵣ[th] - ∗ (* scratch *)
         ct1 ↦ᵣ[th] - ∗ (* scratch *)
         ct2 ↦ᵣ[th] - ∗ (* scratch *)
         user_key_addr ↦ₐ WInt user_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (
             ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
             user_key ↦(LKVS) (<[ nkey := lstore_word RW wca2 ]> m)
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               user_key ↦(LKVS) m
             )
         )
         -∗ safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey Htgt)
      "(#Hkvs_static & #Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_add_spec_layer_1 with
             "[- $Hkvs_static $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }
    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
                     & Ha_user_key
                     & [ (Hca0 & Hlkvs_auth & HLKVS & Hm)
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
    (wret wca2 : LWord)
    (user_key : user_key_t) (nkey : map_key_t) (πnkey : option AId) (l_user_key : Locality) (user_key_addr : Addr)
    (F : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to update *)
      ca2 ↦ᵣ[th] wca2 ∗ (* New value *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_kvs_inv user_key ∗
      ▷ (user_key, nkey) ↦(KVS) ⊥ ∗

      ▷ (na_own (tpool th) F ∗
         PC ↦ₚ[th] lupdatePcPerm wret ∗
         cgp ↦ᵣ[th] - ∗
         cra ↦ᵣ[th] - ∗
         ca1 ↦ᵣ[th] WInt 0 ∗
         ca2 ↦ᵣ[th] - ∗
         ctp ↦ᵣ[th] - ∗ (* scratch *)
         ct1 ↦ᵣ[th] - ∗ (* scratch *)
         ct2 ↦ᵣ[th] - ∗ (* scratch *)
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (
             ca0 ↦ᵣ[th] WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
             (user_key, nkey) ↦(KVS) (lstore_word RW wca2)
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               (user_key, nkey) ↦(KVS) ⊥
             )
         )
         -∗ safe[th]
        )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Htgt)
      "(#Hkvs_static & #Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
      & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & >Hk & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_None _ _ _ _ Hk) as Hm_kvs; eauto.


    iApply (KVS_add_spec_layer_2
             with "[- $Hkvs_static $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
                    $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Ha_user_key
              & [ (Hca0 & Hm) | (Hca0 & Hm) ] )".

    - iMod ( kvs_user_kvs_update _ _ _ _ (Some (lstore_word RW wca2)) with "Hukvs_auth Hk" ) as "[Hukvs_auth Hk]".
      apply (kvs_synced_logical_user_kvs_insert _ _ nkey (lstore_word RW wca2)) in Hsync.
      iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.
      iApply "Hpost"; iFrame; iLeft; iFrame; done.

    - iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.
      iApply "Hpost"; iFrame; iRight; iFrame; done.
  Qed.


  (*** KVS INSERT: Ill-formed inputs *)

  Lemma KVS_addOrUpdate_spec_not_uint16_map_key_pre
    (pc_b pc_e pc_a : Addr)
    (wret : LWord)
    (wca1 : LWord)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs) ->
    ¬ word_is_uint16 wca1.(lw) ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    (
      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] - ∗
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers pc_a kvs_addOrUpdate_instrs ∗

      ( ▷ (PC ↦ₚ[th] lupdatePcPerm wret ∗
         cra ↦ᵣ[th] - ∗
         ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ[th] WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ[th] - ∗ (* scratch *)
         codefrag_pers pc_a kvs_addOrUpdate_instrs
         -∗ safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (HsubBounds Hnkey_is_uint16 Htgt)
      "(HPC & Hcra & [%wca0 Hca0] & Hca1 & Hct1 & #Hcode_main & Hpost)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_addOrUpdate_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_not_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcode_main" as hcode.
    (* jnez (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* mov ca0 ASM_FALSE; *)
    iInstr "Hcode".
    (* mov ca1 0; *)
    iInstr "Hcode".
    (* jalr cnull cra; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    iApply "Hpost"; iFrame "∗ Hcode_main".
  Qed.

  Lemma KVS_addOrUpdate_spec_not_uint16_map_key
    (wret : LWord)
    (wca1 : LWord)
    (F : coPset)
    :

    ↑(Nkvs.@"physical") ⊆ F ->

    ¬ word_is_uint16 wca1.(lw) ->

    jalr_target_ok cnull cra wret.(lw) = true ->

    ( kvs_static ∗
      na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] - ∗
      ca1 ↦ᵣ[th] wca1 ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)

      ( ▷ (na_own (tpool th) F ∗
         PC ↦ₚ[th] lupdatePcPerm wret ∗
         cra ↦ᵣ[th] - ∗
         ca0 ↦ᵣ[th] WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ[th] WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ[th] - (* scratch *)
         -∗ safe[th]
        ) )
      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (HE Hnkey_is_uint16 Htgt)
      "(#Hkvs_static & #Hkvs_inv & Hna & HPC & Hcra & Hca0 & Hca1 & Hct1 & Hpost)".
    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct "Hkvs_static" as "[_ #Hcode_main]".
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_pcc_off_eq; solve_addr+HKVS_pcc_b').
    iApply (KVS_addOrUpdate_spec_not_uint16_map_key_pre with
              "[$HPC $Hcra $Hca0 $Hca1 $Hct1 $Hcode Hna Hpost]"); eauto.
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct1 & _)".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_addOrUpdate_spec_invalid_sealed_user_key_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : LWord)
    (wca0 : LWord)
    (nkey : Z) (πnkey : option AId)
    :

    is_shadow_address (pc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs) ->
    (pc_b + kvs_addOrUpdate_pcc_off)%a = Some pc_a ->
    is_uint16 nkey ->
    (is_sealed_with_o wca0.(lw) KVS_OTYPE = false \/ get_tag wca0.(lw) = false) ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    ((* initial register file *)
      PC ↦ₚ[th] Cap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ[th] Cap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)

      (* initial memory layout *)
      codefrag_pers pc_a kvs_addOrUpdate_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET) ↦ₐ□ kvs_service_unsealing_key ∗

      (* The load after the failed unsealing of the user key faults *)
      ▷ ( ∀ a,
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - -∗
          trap_safe (Cap RX Global pc_b pc_e a) ⊤
            (HO th) )

      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow HsubBounds Hpc_a Hnkey_is_uint16 Hwca0 Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp
      & #Hcode_main & #Ha_unsealing & Hfailed)".
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    iEval (rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate) in "Hcode_main".
    iEval (rewrite -/(kvs_getFullKey kvs_addOrUpdate_getFullKey_off ctp ca0 ca1) -/(kvs_search ca0 ctp ct1 ct2)
      -/(kvs_check_uint16 ca1 ct1)) in "Hcode_main".
    iEval (cbn [fmap list_fmap]) in "Hcode_main".
    iEval (cbn [concat]) in "Hcode_main".

    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & _ & Hct1)".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 1 "Hcode_main" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcode_main" as hcode.
    (* jnez (".addOrUpdate_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".addOrUpdate_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode_main"; subst hcode.

    focus_block 2 "Hcode_main" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcode_main" as hcode
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_invalid_sealed_user_key with "[- $HPC $Hctp $Hca0 $Ha_unsealing $Hcode]") ; eauto.
    { kvs_getFullKey_offset. }
    iIntros "[Hctp Hca0]".
    iApply ("Hfailed" with "[$Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp]").
  Qed.

  Lemma KVS_addOrUpdate_spec_invalid_sealed_user_key
    (wret : LWord)
    (wca0 : LWord)
    (nkey : Z) (πnkey : option AId)
    (F : coPset)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->

    is_uint16 nkey ->
    (is_sealed_with_o wca0.(lw) KVS_OTYPE = false \/ get_tag wca0.(lw) = false) ->

    ( kvs_static ∗
      na_own (tpool th) F ∗

      (* initial register file *)
      PC ↦ₚ[th] Cap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ[th] Cap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ[th] wret ∗
      ca0 ↦ᵣ[th] wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ[th] WInt nkey @@? πnkey ∗ (* Key to addOrUpdate *)
      ct1 ↦ᵣ[th] - ∗ (* scratch *)
      ct2 ↦ᵣ[th] - ∗ (* scratch *)
      ctp ↦ᵣ[th] - ∗ (* scratch *)

      (* The load after the failed unsealing of the user key faults *)
      ▷ ( ∀ a,
          na_own (tpool th) F ∗
          cgp ↦ᵣ[th] - ∗
          cra ↦ᵣ[th] - ∗
          ca0 ↦ᵣ[th] - ∗
          ca1 ↦ᵣ[th] - ∗
          ct1 ↦ᵣ[th] - ∗
          ct2 ↦ᵣ[th] - ∗
          ctp ↦ᵣ[th] - -∗
          trap_safe (Cap RX Global KVS_pcc_b KVS_pcc_e a) ⊤
            (HO th) )

      ⊢ safe[th])%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Hnkey_is_uint16 Hwca0)
      "(#Hkvs_static & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hfailed)".
    iDestruct (kvs_static_unsealing_key with "Hkvs_static") as "#Ha_unsealing".
    iDestruct "Hkvs_static" as "[_ #Hcode_main]".
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode_main"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1) <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode_main" as "Hcode" "Hcont"; iHide "Hcode_main" as hcode.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr kvs_addOrUpdate_pcc_off_eq; solve_addr+HKVS_pcc_b').
    iApply (KVS_addOrUpdate_spec_invalid_sealed_user_key_pre
             with "[$HPC $Hcgp $Hcra $Hca0 $Hca1 $Hct1 $Hct2 $Hctp $Hcode $Ha_unsealing Hna Hfailed]");
      eauto.
    iNext; iIntros (a_fault) "Hregs".
    iApply ("Hfailed" with "[$Hna $Hregs]").
  Qed.

  Lemma KVS_add_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : LWord)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : LReg) (cstk : CSTK) (F : coPset)
    (user_key : user_key_t) (nkey : map_key_t)
    (l_user_key : Locality) (user_key_addr : Addr) (wnew : LWord) :
    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET) = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ F ->
    ↑(Nkvs.@"logical") ⊆ F ->
    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1) user_key_addr = true ->
    arg_rmap !! ca0 = Some (lword_of_word (kvs_user_seal_key l_user_key user_key_addr)) ->
    arg_rmap !! ca1 = Some (lword_of_word (WInt nkey)) ->
    arg_rmap !! ca2 = Some wnew ->
    kvs_static ∗
    na_inv (tpool th) (Nkvs.@"physical") kvs_inv ∗
    na_inv (tpool th) (Nkvs.@"logical") logical_kvs_inv
    ⊢
    switcher_cc_specification_known_to_known_function false
      (user_key_addr ↦ₐ WInt user_key ∗
       user_kvs_inv user_key ∗
       (user_key, nkey) ↦(KVS) ⊥)
      (λ wca0 wca1,
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         ⌜ wca1 = WInt 0 ⌝ ∗
         ((⌜ wca0 = WInt ASM_TRUE ⌝ ∗
           (user_key, nkey) ↦(KVS) (lstore_word RW wnew))
          ∨
          (⌜ wca0 = WInt ASM_FALSE ⌝ ∗
           (user_key, nkey) ↦(KVS) ⊥)))
      wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk arg_rmap cstk kvs_addOrUpdate_nargs kvs_addOrUpdate_min_stack F
      KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e kvs_addOrUpdate_pcc_off
      (Cap RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Huser_key_shadow Hphysical Hlogical Hnkey Huser_key Hca0_arg Hca1_arg Hca2_arg).
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros "(#Hkvs_static & #Hkvs & #Hkvs_logical)" (mie arg_rmap' rmap')
       "(_ & %Harg_rmap' & %Hrmap' & Hna & HPC & Hcgp & Hcra & Hcsp
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
      "[- $Hkvs_static $Hkvs $Hkvs_logical $Hna $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hca2 $Hctp $Hct1 $Hct2
       $Huser_key $Huser_kvs $Hkey]"); auto.
    { apply jalr_target_ok_switcher_return_sentry. }
    iNext.
    iIntros "(Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra] & Hca1
              & [%wca2 Hca2] & [%wctp Hctp] & [%wct1 Hct1]
              & [%wct2 Hct2]
              & Huser_key & Huser_kvs & Hres)".
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].
    set (rmap_ret0 := delete cs1 (delete cs0 rmap')).
    set (rmap_ret1 := <[ctp := wctp]> rmap_ret0).
    set (rmap_ret2 := <[ct1 := wct1]> rmap_ret1).
    set (rmap_ret3 := <[ct2 := wct2]> rmap_ret2).
    set (rmap_ret4 := <[cnull := lword_of_word (WInt 0)]> rmap_ret3).
    set (rmap_ret5 := <[ca2 := wca2]> rmap_ret4).
    set (rmap_ret6 := <[ca3 := lword_of_word (WInt 0)]> rmap_ret5).
    set (rmap_ret7 := <[ca4 := lword_of_word (WInt 0)]> rmap_ret6).
    set (rmap_ret8 := <[ca5 := lword_of_word (WInt 0)]> rmap_ret7).
    set (rmap_ret := <[ct0 := lword_of_word (WInt 0)]> rmap_ret8).
    iEval (cbn) in "HPC".

    iDestruct "Hres" as "[(Hca0 & Hkey) | (Hca0 & Hkey)]".
    - iApply ("Hpost" $! 0%Z (WInt ASM_TRUE) (WInt 0) rmap_ret
                (region_addrs_zeroes (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk))).
      iSplit.
      { iPureIntro.
        rewrite /rmap_ret /rmap_ret8 /rmap_ret7 /rmap_ret6 /rmap_ret5
          /rmap_ret4 /rmap_ret3 /rmap_ret2 /rmap_ret1 /rmap_ret0.
        repeat (rewrite dom_insert_L).
        repeat (rewrite dom_delete_L).
        rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
      iFrame.
      iFrame. iSplit; first done. iLeft.
      iSplit; first done. iFrame.
    - iApply ("Hpost" $! 0%Z (WInt ASM_FALSE) (WInt 0) rmap_ret
                (region_addrs_zeroes (stk_callee_b b_stk a_stk) (stk_callee_e e_stk a_stk))).
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
