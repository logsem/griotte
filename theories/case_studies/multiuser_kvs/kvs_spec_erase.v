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

  (*** KVS erase *)
  Lemma KVS_erase_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (user_key nkey : Z) (l_user_key : Locality)
    (idx : nat)
    (m : kvs_map) (s : kvs_alloc) (s' : gset Z)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_erase_instrs)%a ->
    (0 <= user_key < MemNum)%Z ->
    is_uint16 nkey ->

    (cgp_b + length_kvs_data)%a = Some cgp_e ->

    nkey ∈ s' ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_erase_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS cgp_b m s ∗
      ◯(ALLOC)[user_key] s' ∗
      fkey ⤇(KVS)[ idx ] - ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt 0 ∗
         ca1 ↦ᵣ WInt 0 ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         isKVS cgp_b (<[ idx := None ]> m) (kvs_alloc_delete s user_key {[nkey]}) ∗
         ◯(ALLOC)[user_key] ( s' ∖ {[ nkey ]} ) ∗

         codefrag pc_a kvs_erase_instrs ∗
         (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_user_key His_uint16_nkey Hcgp_contiguous Hs')
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Ha_unsealing & HKVS & Halloc & [%fkey_w Hkvs_frag] & Hpost)".
    rewrite /length_kvs_data /= in Hcgp_contiguous.
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_erase_instrs /assembled_kvs_erase.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_known with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
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
    iApply (KVS_getFullKey_spec with "[- $HPC $Hctp $Hca0 $Hca1 $Hct1 $Hct2 $Ha_unsealing $Hcode]") ; eauto; iNext.
    iIntros "(HPC & Hctp & Hca0 & Hca1 & Hct1 & Hct2 & Ha_unsealing & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HKVS & Hcgp_opt & Hcgp_key & Hcgp_val & Hkvs_frag & %Hcgp_idx & Hcode)".
    iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
    iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
    { by apply elem_of_dom_2 in Hm_idx. }
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

    iMod (isKVS_open_delete _ _ _ _ idx user_key nkey _ with "HKVS Halloc Hkvs_frag") as
      "(HKVS & Halloc & Hkvs_frag)"; auto.
    { rewrite /wf_kvs_full_key; split; auto; lia. }

    iDestruct (close_isKVS with "[$HKVS Hcgp_opt Hcgp_key Hcgp_val Hkvs_frag]") as "HKVS";eauto.
    { by simplify_map_eq. }
    { iFrame. }

    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_erase_spec
    (wret : Word)
    (user_key nkey : Z) (l_user_key : Locality)
    (s' : gset Z)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->
    nkey ∈ s' ->

    (0 <= user_key < MemNum)%Z ->
    is_uint16 nkey ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_erase_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key l_user_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to erase *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      ◯(ALLOC)[user_key] s' ∗
      fkey ⤇(KVS) - ∗

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
         ◯(ALLOC)[user_key] ( s' ∖ {[ nkey ]} )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hs' Hbounds_user_key His_uint16_nkey)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
        & Halloc & [ %wfkey [%idx Hfkey] ] & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & %next_free_uk & >Himports & >Hcgp_e & >Hcode
            & HisKVS & >%Hwf_free_uk & Hfree_uk_alloc & #Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    iApply (KVS_erase_spec_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2
              & Hcnull & HKVS & Halloc & Hcode & Ha_unsealing)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hcode $Hcgp_e Himports_sw Ha_unsealing $HKVS $Hfree_uk_alloc $Hspred $Hna]") as "Hna" ; auto.
    { iNext.
      iSplit; last done.
      iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
      iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
      rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
    }
    iApply "Hpost"; iFrame.
  Qed.

End KVS_spec_erase.
