From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
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

  Transparent kvs_user_map_auth.
  Transparent kvs_user_map_frag.
  (*** KVS INSERT: Key in the KVS *)
  Lemma KVS_update_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca2 : Word)
    (user_key nkey : Z) (l_user_key : Locality) (user_key_addr : Addr)
    (mkvs : kvs_map) (lm : kvs_logical_map) (m : kvs_user_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ isKVS cgp_b mkvs lm ∗
      ▷ ◯↪KVS[ user_key ] m ∗
      ▷ nkey ↦(KVS)[user_key] - ∗

      ▷ ( ∀ (idx : nat),
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
          isKVS cgp_b (<[ idx := Some (fkey, wca2) ]> mkvs) (kvs_logical_kvs_insert lm user_key nkey wca2) ∗
          ◯↪KVS[ user_key ] ( <[nkey:=wca2]> m ) ∗
          nkey ↦(KVS)[user_key] wca2 ∗
          codefrag pc_a kvs_addOrUpdate_instrs ∗
          (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key

          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_a_user_key His_uint16_nkey Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
        & Hcode & Ha_unsealing & Ha_user_key & HKVS & Halloc & [%fkey_w Hkvs_frag] & Hpost)".
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

    iEval (rewrite /kvs_user_map_frag) in "Hkvs_frag".
    iDestruct "Hkvs_frag" as "[%idx Hkvs_frag]".
    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
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
    { transitivity ( Some ((cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx + 2))%a) ); last done; solve_addr+Hcgp_idx Hidx. }
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

    iMod (isKVS_open_update _ _ _ _ _ _ _  _ wca2 with "HKVS Hkvs_frag Halloc")
      as "(HKVS & Hkvs_frag & Halloc)"; first ( split; auto ).

    iDestruct (close_isKVS with "[$HKVS Hcgp_opt Hcgp_key Hcgp_val]") as "HKVS";eauto.
    { by simplify_map_eq. }
    { iApply destruct_isKVS_entry; first solve_addr; iFrame. }

    iApply "Hpost"; iFrame "∗%"; done.
  Qed.

  Lemma KVS_update_spec
    (wret wca2 : Word)
    (user_key nkey : Z) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
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

      ▷ ◯↪KVS[ user_key ] m ∗
      ▷ nkey ↦(KVS)[user_key] - ∗

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

          ◯↪KVS[ user_key ] (<[nkey := wca2]> m) ∗
          nkey ↦(KVS)[user_key] wca2

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E His_uint16_nkey Hbounds_a_user_key)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Halloc & [ %wfkey Hfkey ] & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%mkvs & %s & >Himports & >Hcode & HisKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    iApply (KVS_update_spec_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(%Hcan_store & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & HKVS & Halloc & Hfkey & Hcode & Ha_unsealing & Ha_user_key)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HKVS $Hspred]") as "Hna" ; auto.
    { iNext.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }
    iApply "Hpost"; iFrame; done.
  Qed.

  (*** KVS INSERT: Key not in the KVS *)
  Lemma KVS_add_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca2 : Word)
    (user_key nkey : Z) (l_user_key : Locality) (user_key_addr : Addr)
    (mkvs : kvs_map) (lm : kvs_logical_map) (m : kvs_user_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    nkey ∉ dom m ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ isKVS cgp_b mkvs lm ∗
      ▷ ◯↪KVS[ user_key ] m ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
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
          user_key_addr ↦ₐ WInt user_key ∗
          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            (∃ idx,
                ⌜ canStore RW wca2 = true ⌝ ∗
                ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
                isKVS cgp_b (<[ idx := Some (fkey, wca2) ]> mkvs) ( kvs_logical_kvs_insert lm user_key nkey wca2) ∗
                ◯↪KVS[ user_key ] ( <[nkey := wca2]> m ) ∗
                nkey ↦(KVS)[user_key] wca2
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                isKVS cgp_b mkvs lm ∗
                ◯↪KVS[ user_key ] m
              )
          )
          -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_a_user_key His_uint16_nkey Hcgp_contiguous Hs')
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & [%wctp Hctp] & Hct1 & Hct2 & [%wcnull Hcnull]
        & Hcode & Ha_unsealing & Ha_user_key & HKVS & Halloc & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).

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
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Halloc $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "[
    (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & Halloc & HKVS
    & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & Hfkey & %Hcgp_bounds & %Hidx_empty & Hcode)
    | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HKVS & Halloc & Hcode) ]".
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
      { transitivity (Some (cgp_b ^+ ASM_SIZEOF_KVS_ENTRY * idx_empty)%a); solve_addr+ Hidx_empty Hcgp_bounds. }
      (* store cgp ASM_SOME; *)
      iInstr "Hcode".
      { solve_addr+Hcgp_bounds. }
      (* lea cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 1))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
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
      { transitivity (Some (cgp_b ^+ (ASM_SIZEOF_KVS_ENTRY * idx_empty + 2))%a); solve_addr+ Hidx_empty Hcgp_bounds. }
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
      { iApply destruct_isKVS_entry; first solve_addr; iFrame. }

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

  Lemma KVS_add_spec
    (wret wca2 : Word)
    (user_key nkey : Z) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    nkey ∉ dom m ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
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

      ▷ ◯↪KVS[ user_key ] m ∗

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
             ◯↪KVS[ user_key ] ( <[nkey := wca2 ]> m) ∗
             nkey ↦(KVS)[user_key] wca2
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               ◯↪KVS[ user_key ] m
             )
         )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E His_uint16_nkey Hbounds_a_user_key Hs')
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Halloc & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%mkvs & %s & >Himports & >Hcode & HisKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    iApply (KVS_add_spec_pre with "[- $HPC]"); last iFrame "∗#%"; eauto.
    iNext ; iIntros "(HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & Hcode & Ha_unsealing & Ha_user_key &
              [ (%idx & % & Hca0 & HKVS & Halloc & Hfkey) | (Hca0 & HKVS & Halloc) ]
              )".

    all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
    all: iMod ("Hkvs_inv_close" with "[$Hna $Hcode Himports_sw Ha_unsealing $HKVS $Hspred]") as "Hna"
    ; auto; last ( iApply "Hpost"; iFrame ; try (iLeft; iFrame; done) ; try (iRight; iFrame; done)).
    all: iNext.
    all: iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
    all: iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
    all: rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
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

    ↑Nkvs ⊆ E ->

    ¬ word_is_uint16 wca1 ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
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
      as "( (%mkvs & %s & >Himports & >Hcode & HKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Himports $HKVS $Hspred]") as "Hna".
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

    ↑Nkvs ⊆ E ->

    is_uint16 nkey ->
    is_sealed_with_o wca0 KVS_OTYPE = false ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
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
      as "( (%mkvs & %s & >Himports & >Hcode & HKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
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

End KVS_spec_addOrUpdate.
