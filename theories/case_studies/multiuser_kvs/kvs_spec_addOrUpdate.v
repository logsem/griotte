From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.
From cap_machine Require Import region_invariants_revocation wp_rules_interp logrel_extra interp_weakening.
From cap_machine Require Import switcher_preamble switcher_spec_return.
From cap_machine Require Import proofmode map_simpl.

Section KVS_spec_addOrUpdate.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** KVS update *)
  Lemma KVS_update_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca2 : Word)
    (user_key nkey : Z)
    (idx : nat)
    (m : kvs_map) (s : kvs_alloc)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    canStore RW wca2 = true ->

    ((* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS (cgp_b ^+ 1)%a m s ∗
      fkey ⤇(KVS)[ idx ] - ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map and is updated *)
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         isKVS (cgp_b ^+ 1)%a (<[ idx := (fkey, wca2) ]> m) s ∗
         fkey ⤇(KVS)[idx] wca2 ∗
         codefrag pc_a kvs_addOrUpdate_instrs ∗
         cgp_b ↦ₐ kvs_service_unsealing_key

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_user_key His_uint16_nkey Hcgp_contiguous HcanStore_wca2)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Hcgp_b & HKVS & [%fkey_w Hkvs_frag] & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).
    rewrite -/(kvs_search ctp ct1 ct2).
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
    iApply (KVS_getFullKey_spec with "[- $HPC $Hcgp $Hca0 $Hca1 $Hct1 $Hcgp_b $Hcode]"); eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros "(HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iApply (KVS_search_spec_in with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Hkvs_frag $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    { apply kvs_full_key_not_empty; split; auto; lia. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val  & Hfkey & %Hcgp_idx & Hkvs_frag & Hcode)".
    iDestruct (isKVS_open_valid with "HKVS Hkvs_frag") as "%Hm_idx".
    iDestruct (isKVS_open_indom_idx with "HKVS") as "%Hidx".
    { by apply elem_of_dom_2 in Hm_idx. }
    iEval (cbn) in "Hfkey".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ct1 ct1 (-1) *)
    iInstr "Hcode".
    (* Jnz 5 ct1 *)
    iInstr "Hcode".
    { injection; intros; lia. }
    (* Lea cgp 1 *)
    iInstr "Hcode".
    { transitivity ( Some ((cgp_b ^+ (2 + 2 * idx))%a) ); solve_addr+Hcgp_idx Hidx. }
    (* Store cgp (inr ca2) *)
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
    iDestruct (kvs_frag_kvs_empty_not_empty_slot with "Hkvs_frag Hfkey") as "%Hk".

    iDestruct (close_isKVS with "[$HKVS Hcgp_key Hcgp_val]") as "HKVS";eauto.
    { by simplify_map_eq. }
    {
      replace (cgp_b ^+ (1 + 2 * idx))%a with ((cgp_b ^+ 1) ^+ 2 * idx)%a by solve_addr+Hidx.
      replace (cgp_b ^+ (2 + 2 * idx))%a  with ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a by solve_addr+Hidx.
      iFrame.
      rewrite /isKVS_entry_empty /=.
      destruct (decide (kvs_full_key user_key nkey = EMPTY_SLOT)); done.
    }

    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_update_spec
    (wret wca2 : Word)
    (user_key nkey : Z)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->

    canStore RW wca2 = true ->

    ( na_inv logrel_nais Nkvs kvs_inv ∗
      na_own logrel_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      fkey ⤇(KVS) - ∗

      ▷ (na_own logrel_nais E ∗
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
         fkey ⤇(KVS) wca2
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hbounds_user_key His_uint16_nkey HcanStore_wca2)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & [ %wfkey [%idx Hfkey] ] & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & >Himports & >Hcode & >Hcgp_b & HisKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    iApply (KVS_update_spec_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & HKVS & Hfkey & Hcode & Hcgp_b)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Hcgp_b $Himports $HKVS $Hspred]") as "Hna" ; auto.
    iApply "Hpost"; iFrame.
  Qed.

  (*** KVS add *)
  Lemma KVS_add_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca2 : Word)
    (user_key nkey : Z)
    (m : kvs_map) (s : kvs_alloc) (s' : gset Z)
    :

    let fkey := (kvs_full_key user_key nkey) in

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    canStore RW wca2 = true ->
    nkey ∉ s' ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS (cgp_b ^+ 1)%a m s ∗
      ◯(ALLOC)[user_key] s' ∗

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
          codefrag pc_a kvs_addOrUpdate_instrs ∗
          cgp_b ↦ₐ kvs_service_unsealing_key ∗
          (
            (* THERE IS AN EMPTY SLOT AVAILABLE*)
            (∃ idx,
                ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
                isKVS (cgp_b ^+ 1)%a (<[ idx := (fkey, wca2) ]> m) ( kvs_alloc_insert s user_key {[nkey]}) ∗
                ◯(ALLOC)[user_key] ( {[ nkey ]} ∪ s') ∗
                fkey ⤇(KVS)[ idx ] wca2
            )
            ∨
              (* THERE IS NO EMPTY SLOT AVAILABLE*)
              (
                ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
                isKVS (cgp_b ^+ 1)%a m s ∗
                ◯(ALLOC)[user_key] s'
              )
          )
          -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (HsubBounds Hbounds_user_key His_uint16_nkey Hcgp_contiguous HcanStore_wca2 Hs')
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & [%wctp Hctp] & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Hcgp_b & HKVS & Halloc & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_addOrUpdate_instrs /assembled_kvs_addOrUpdate.
    rewrite -/(kvs_getFullKey ca0 ca0 ca1 ct1).
    rewrite -/(kvs_search ca0 ct1 ct2).
    rewrite -/(kvs_search ctp ct1 ct2).

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
    iApply (KVS_getFullKey_spec with "[- $HPC $Hcgp $Hca0 $Hca1 $Hct1 $Hcgp_b $Hcode]"); eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros "(HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode)".
    assert ( wf_kvs_full_key user_key nkey ) as Hwf_fullkey.
    { split; auto; lia. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iApply (KVS_search_spec_notin with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Halloc $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hcgp & Hca0 & Hct1 & Hct2 & HKVS & Halloc & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 5 "Hcode" as a_addOrUpdate Ha_addOrUpdate "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search.
    (* Sub ct1 ct1 (-1) *)
    iInstr "Hcode".
    replace (-1 - -1)%Z with 0%Z by lia.
    (* Jnz 5 ct1 *)
    iInstr "Hcode".
    (* Mov ctp (-1) *)
    iInstr "Hcode".
    destruct (decide (ctp = cnull)); first done.
    (* Jmp 6 *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 6 "Hcode" as a_search' Ha_search' "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_addOrUpdate.
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hctp $Hct1 $Hct2 $HKVS $Hcode]"); eauto.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros
             "[ (%idx & HPC & Hcgp & Hctp & Hct1 & Hct2 & HKVS & Hcgp_key & Hcgp_val & Hfkey & %Hcgp_idx & %Hidx & Hcode)
               | (HPC & Hcgp & Hctp & Hct1 & Hct2 & HKVS & Hcode)
               ]".
    all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    all: focus_block 7 "Hcode" as a_add Ha_add "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_search'.
    - (* an empty slot was found *)
      (* Sub ct1 ct1 (-1) *)
      iInstr "Hcode".
      (* Jnz 4 ct1 *)
      iInstr "Hcode".
      { injection ; lia. }
      (* Store cgp ca0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca0 $Hcgp $Hcgp_key]"); try solve_pure.
      { rewrite /withinBounds ; solve_addr. }
      { done. }
      iNext; iIntros "(HPC & Hi & Hca0 & Hcgp & Hcgp_key)".
      wp_pure.
      iInstr_close "Hcode".
      (* Lea cgp 1 *)
      iInstr "Hcode".
      { transitivity ( Some ((cgp_b ^+ (2 + 2 * idx))%a) ); solve_addr+Hcgp_idx Hidx. }
      (* Store cgp ca2 *)
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

      iMod (isKVS_open_insert _ _ _ _ _ _ _ wca2 with "HKVS Halloc Hfkey") as "(HKVS & Halloc & Hfkey)"; eauto.
      iDestruct (close_isKVS with "[$HKVS Hcgp_key Hcgp_val]") as "HKVS";eauto.
      { by simplify_map_eq. }
      {
        replace (cgp_b ^+ (1 + 2 * idx))%a with ((cgp_b ^+ 1) ^+ 2 * idx)%a by solve_addr+Hidx.
        replace (cgp_b ^+ (2 + 2 * idx))%a  with ((cgp_b ^+ 1) ^+ (2 * idx + 1))%a by solve_addr+Hidx.
        iFrame.
        rewrite /isKVS_entry_empty /=.
        destruct (decide (kvs_full_key user_key nkey = EMPTY_SLOT)); try done.
        exfalso.
        apply (kvs_full_key_not_empty user_key nkey); auto.
      }

      iApply "Hpost"; iFrame; iLeft ; iFrame.

    - (* no empty slot found *)
      (* Sub ct1 ct1 (-1) *)
      iInstr "Hcode".
      replace (-1 - -1)%Z with 0%Z by lia.
      (* Jnz 4 ct1 *)
      iInstr "Hcode".
      (* Mov ca0 (-1) *)
      iInstr "Hcode".
      destruct (decide (ca0 = cnull)); first done.
      (* Mov ca1 0 *)
      iInstr "Hcode".
      (* Jalr cnull cra *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iApply "Hpost"; iFrame; iRight ; iFrame.
  Qed.


  Lemma KVS_add_spec
    (wret wca2 : Word)
    (user_key nkey : Z) (s : gset Z)
    (E : coPset)
    :
    let fkey := (kvs_full_key user_key nkey) in

    ↑Nkvs ⊆ E ->

    (0 <= user_key < top)%Z ->
    is_uint16 nkey ->
    nkey ∉ s ->

    canStore RW wca2 = true ->

    ( na_inv logrel_nais Nkvs kvs_inv ∗
      na_own logrel_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ kvs_user_seal_key user_key ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      ◯(ALLOC)[user_key] s ∗

      ▷ (na_own logrel_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (
             ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: an empty slot is available and is updated *)
             ◯(ALLOC)[user_key] ( {[ nkey ]} ∪ s) ∗
             fkey ⤇(KVS) wca2
           )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE*)
             (
               ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: no empty slot available *)
               ◯(ALLOC)[user_key] s
             )
         )
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros fkey.
    iIntros (Hnkvs_E Hbounds_user_key His_uint16_nkey HcanStore_wca2 Hs)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull
      & Halloc & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s' & >Himports & >Hcode & >Hcgp_b & HisKVS & Hspred) & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e KVS_pcc_b' (KVS_pcc_b' ^+ length kvs_service_instrs)%a) as HSubBounds.
    { solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.

    rewrite /kvs_service_instrs.
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (kvs_addOrUpdate_pcc_addr = KVS_pcc_b')
      as -> by (rewrite /kvs_addOrUpdate_pcc_addr /kvs_addOrUpdate_pcc_off; solve_addr+HKVS_pcc_b').
    iApply (KVS_add_spec_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & Hcode & Hcgp_b &
              [ (%idx & Hca0 & HKVS & Halloc & Hfkey) | (Hca0 & HKVS & Halloc) ]
              )".
    all: subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".
    all: iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Hcgp_b $Himports $HKVS $Hspred]") as "Hna" ; auto.
    all: iApply "Hpost"; iFrame ; try (iLeft; iFrame; done) ; try (iRight; iFrame; done).
  Qed.

End KVS_spec_addOrUpdate.
