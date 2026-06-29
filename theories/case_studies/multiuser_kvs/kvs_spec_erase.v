From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.

Section KVS_spec_erase.
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

  (*** KVS ERASE: Key in the KVS *)

  Lemma KVS_erase_spec_in_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    is_Some (m !! nkey) ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs cgp_b lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt 0 ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         codefrag pc_a kvs_erase_instrs ∗
         (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
         user_key_addr ↦ₐ WInt user_key ∗

         ↪●LKVS ( lkvs <∖> (user_key, nkey) ) ∗
         is_logical_kvs cgp_b ( lkvs <∖> (user_key, nkey) ) ∗
         user_key ↦(LKVS) (delete nkey m)


         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_user_key His_uint16_nkey Hcgp_contiguous [wnkey Hm_nkey])
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Ha_unsealing & Ha_user_key
        & Hlkvs_auth & (%pkvs & >%Hsync & HKVS) & Hm & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

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

    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_Some _ _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as (idx & Hpkvs_idx).

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Hcgp_opt & Hcgp_key & Hcgp_val
                    & HKVS & %Hcgp_idx & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* sub ctp ctp (-1)%Z; *)
    iInstr "Hcode".
    (* jnz (".erase_key_found")%asm ctp; *)
    iInstr "Hcode".
    { injection; intros; lia. }
    (* store cgp ASM_NONE; *)
    iInstr "Hcode".
    { solve_addr+Hcgp_idx. }
    (* mov ca0 0; *)
    iInstr "Hcode".
    (* mov ca1 0; *)
    iInstr "Hcode".
    (* jalr cnull cra *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iAssert (  ⌜ wf_kvs_physical_map pkvs ⌝ )%I as "[%_ %Hnodup_pkvs_keys]"
    ; first ( iDestruct "HKVS" as "[$ _]" ).
    iDestruct (kvs_physical_map_close_delete with "[$HKVS] [Hcgp_opt Hcgp_key Hcgp_val]")
      as "HKVS"; eauto.
    { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }

    iMod ( kvs_logical_kvs_update user_key _ _ (delete nkey m) with "Hlkvs_auth Hm" ) as "[Hlkvs_auth Hm]".
    replace ( <[user_key:= (delete nkey m)]> lkvs ) with ( lkvs <∖> (user_key, nkey) ).
    2: { rewrite /kvs_logical_kvs_delete Hlkvs_user_key //. }
    eapply kvs_synced_logical_kvs_delete in Hsync; eauto.

    iApply "Hpost"; iFrame "∗%"; done.
  Qed.

  Lemma KVS_erase_spec_in
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    is_Some (m !! nkey) ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
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
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt 0 ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         user_key_addr ↦ₐ WInt user_key ∗

         user_key ↦(LKVS) (delete nkey m)

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & (%lkvs & Hlkvs_auth & HKVS) & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    focus_block_nochangePC 2 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_erase = kvs_erase_pcc_addr) as -> by (rewrite /kvs_erase_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_erase).
    iApply (KVS_erase_spec_in_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
                    & Hcode & Ha_unsealing & Ha_user_key
                    & Hlkvs_auth & HKVS & Hm)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $Hlkvs_auth $HKVS $Hspred]") as "Hna" ; auto.
    { iNext.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_erase_spec_notin_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    m !! nkey = None  ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ ↪●LKVS lkvs ∗
      ▷ is_logical_kvs cgp_b lkvs ∗
      ▷ user_key ↦(LKVS) m ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt 0 ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         codefrag pc_a kvs_erase_instrs ∗
         (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
         user_key_addr ↦ₐ WInt user_key ∗


         ↪●LKVS lkvs ∗
         is_logical_kvs cgp_b lkvs ∗
         user_key ↦(LKVS) m

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HsubBounds Hbounds_a_user_key His_uint16_nkey Hcgp_contiguous Hm_nkey)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
       & Hcode & Ha_unsealing & Ha_user_key
       & Hlkvs_auth & (%pkvs & >%Hsync & HKVS) & Hm & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

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

    iDestruct ( kvs_logical_kvs_valid with "Hlkvs_auth Hm" ) as "%Hlkvs_user_key".
    pose proof (kvs_synced_logical_lookup_None _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as Hpkvs_idx.

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "[
    (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HKVS
    & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & %Hcgp_bounds
    & %Hidx_empty & %Hpkvs_idx_empty & Hcode)
    | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HKVS & Hcode) ]".
    all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    + (* No empty found *)

      focus_block 5 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnz (".read_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jmp (".read_key_ret")%asm; *)
      iInstr "Hcode".
      (* jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iDestruct (kvs_physical_map_close with "[$HKVS] [Hcgp_opt Hcgp_key Hcgp_val]") as "HKVS";eauto.
      { iApply destruct_physical_kvs_entry; first solve_addr; iFrame. }
      iApply "Hpost"; iFrame "∗%"; done.

    + (* Empty found, but it does not matter here *)
      focus_block 5 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
      (* sub ctp ctp (-1)%Z; *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* jnz (".read_key_found")%asm ctp; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* jmp (".read_key_ret")%asm; *)
      iInstr "Hcode".
      (* jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iApply "Hpost"; iFrame "∗%"; done.
  Qed.

  Lemma KVS_erase_spec_notin
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    m !! nkey = None ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
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
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt 0 ∗
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
    iIntros (Hnkvs_E His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
        & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & (%lkvs & Hlkvs_auth & HKVS) & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    focus_block_nochangePC 2 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_erase = kvs_erase_pcc_addr) as -> by (rewrite /kvs_erase_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_erase).
    iApply (KVS_erase_spec_notin_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
                    & Hcode & Ha_unsealing & Ha_user_key
                    & Hlkvs_auth & HKVS & Hm)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $Hlkvs_auth $HKVS $Hspred]") as "Hna" ; auto.
    { iNext.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }
    iApply "Hpost"; iFrame.
  Qed.

  (*** KVS ERASE: Ill-formed inputs *)

  Lemma KVS_erase_spec_not_uint16_map_key_pre
    (pc_b pc_e pc_a : Addr)
    (wret : Word)
    (wca1 : Word)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    ¬ word_is_uint16 wca1 ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to erase *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         codefrag pc_a kvs_erase_instrs
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
    rewrite /kvs_erase_instrs /assembled_kvs_erase.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_not_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".erase_not_uint16")%asm ct1; *)
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

  Lemma KVS_erase_spec_not_uint16_map_key
    (wret : Word)
    (wca1 : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->

    ¬ word_is_uint16 wca1 ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to erase *)
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
      as "( (>Himports & >Hcode & HKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 2 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_erase = kvs_erase_pcc_addr) as -> by (rewrite /kvs_erase_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_erase).
    iApply ( KVS_erase_spec_not_uint16_map_key_pre ); eauto; iFrame.
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct1 & Hcnull & Hcode)".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Himports $HKVS $Hspred]") as "Hna".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_erase_spec_invalid_sealed_user_key_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    is_uint16 nkey ->
    is_sealed_with_o wca0 KVS_OTYPE = false ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗
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
    rewrite /kvs_erase_instrs /assembled_kvs_erase.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".erase_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".erase_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_invalid_sealed_user_key with "[- $HPC $Hctp $Hca0 $Hct1 $Hct2 $Ha_unsealing $Hcode]") ; eauto; iNext.
  Qed.

  Lemma KVS_erase_spec_invalid_sealed_user_key
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    is_sealed_with_o wca0 KVS_OTYPE = false ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ -

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (HE Hnkey_is_uint16 Hwca0)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp & Hcnull)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (>Himports & >Hcode & HKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    focus_block_nochangePC 2 "Hcode" as a_erase Ha_erase "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_erase = kvs_erase_pcc_addr) as -> by (rewrite /kvs_erase_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_erase).
    iApply ( KVS_erase_spec_invalid_sealed_user_key_pre ); eauto; iFrame.
  Qed.

End KVS_spec_erase.
