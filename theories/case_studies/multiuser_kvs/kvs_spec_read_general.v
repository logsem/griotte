From griotte Require Import checkints.
From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import
  switcher switcher_spec_KtK kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16
  map_simpl register_tactics.

Section KVS_spec_read.
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

  (*** KVS READ: Read key in the KVS *)
  Lemma KVS_read_spec_in_general_layer_0
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (idx : kvs_idx_t) ( w : Word )
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    SubBounds KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr (kvs_read_pcc_addr ^+ length kvs_read_instrs)%a ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    pkvs !! idx = Some (Some (kvs_full_key user_key nkey, w)) ->

    ((* initial register file *)

      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap true RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag kvs_read_pcc_addr kvs_read_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ▷ (
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
           (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜actual = w ∨ (is_heap_cap w = true ∧ actual = clear_tag w)⌝) ∗ (* result of the read *)
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          codefrag kvs_read_pcc_addr kvs_read_instrs ∗
          (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗

          is_physical_kvs KVS_cgp_b pkvs

          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hbounds_pcc Hbounds_cgp Hbounds_a_user_key His_uint16_nkey Hpkvs_idx)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
        & Hcode & Ha_unsealing & Ha_user_key
        & HPKVS & Hpost)".

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_erase_instrs /assembled_kvs_erase.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
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
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto using KVS_cgp_disjoint_from_shadow.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Hcgp_opt & Hcgp_key & Hcgp_val
                    & HPKVS & %Hcgp_idx & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ct1 ct1 (-1) *)
    iInstr "Hcode".
    (* Jnz 5 ct1 *)
    iInstr "Hcode".
    (* Lea cgp 1 *)
    iInstr "Hcode".
    (* Load ca1 cgp: the heap shadow can clear the returned tag. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_load_preserve_or_clear _ _ _ _ _ _ (a_read ^+ 7)%a with "[$HPC $Hi $Hca1 $Hcgp $Hcgp_val]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (ret)
      "[-> | (%actual & -> & %Hactual & HPC & Hi & Hca1 & Hcgp & Hcgp_val)]".
    { wp_pure; wp_end; iIntros "%Hcontr"; done. }
    wp_pure. iSpecialize ("Hcode" with "[$]").
    (* Mov ca1 0 *)
    iInstr "Hcode".
    (* Jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iDestruct (kvs_physical_map_close with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]") as "HKVS";eauto.
    { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }
    iApply "Hpost"; iFrame "∗%".
  Qed.

  Lemma KVS_read_spec_in_general_layer_1
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (w : Word)
    (E : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ E ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    m !! nkey = Some w ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap true RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
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
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
           (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜actual = w ∨ (is_heap_cap w = true ∧ actual = clear_tag w)⌝) ∗ (* result of the read *)
          ctp ↦ᵣ - ∗ (* scratch *)
          ct1 ↦ᵣ - ∗ (* scratch *)
          ct2 ↦ᵣ - ∗ (* scratch *)
          cnull ↦ᵣ - ∗

          user_key_addr ↦ₐ WInt user_key ∗

          ↪●LKVS lkvs ∗
          is_logical_kvs lkvs ∗
          user_key ↦(LKVS) m

          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hbounds_a_user_key His_uint16_nkey Hm_nkey)
      "(#Hkvs_inv & Hna
        & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
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

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 1 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).

    iDestruct ( kvs_physical_kvs_valid with "Hpkvs_frag Hpkvs_frag'") as "<-".

    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_Some _ _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as (idx & Hpkvs_idx).

    iDestruct (is_physical_kvs_wf with "HPKVS") as "#[_ Hnodup_pkvs]".


    iApply (KVS_read_spec_in_general_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                     & Hcode & Ha_unsealing & Ha_user_key
                     & HPKVS )".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HPKVS $Hpkvs_frag']") as "Hna" ; auto.
    { iNext.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_read_spec_in_general_layer_2
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (w : Word)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    m !! nkey = Some w ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap true RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
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
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
          (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜actual = w ∨ (is_heap_cap w = true ∧ actual = clear_tag w)⌝) ∗ (* result of the read *)
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         user_key_addr ↦ₐ WInt user_key ∗

         user_key ↦(LKVS) m

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_read_spec_in_general_layer_1 with
             "[- $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }

    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & Hlkvs_auth & HLKVS & Hm)".

    iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
    iApply "Hpost"; iFrame; done.
  Qed.


  Lemma KVS_read_spec_in_general
    (wret wca2 : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (w : Word)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap true RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      user_key_addr ↦ₐ WInt user_key ∗

      ▷ user_kvs_inv user_key ∗
      ▷ (user_key, nkey) ↦(KVS) w ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
          (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜actual = w ∨ (is_heap_cap w = true ∧ actual = clear_tag w)⌝) ∗ (* result of the read *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         ctp ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         user_key_addr ↦ₐ WInt user_key ∗

         user_kvs_inv user_key ∗
         (user_key, nkey) ↦(KVS) w

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    intros fkey.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
       & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & >Hk & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_Some _ _ _ _ _ Hk) as Hm_kvs; eauto.

    iApply (KVS_read_spec_in_general_layer_2
             with "[- $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                    $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hna
                    & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                    & Ha_user_key & Hm)".

    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.

End KVS_spec_read.
