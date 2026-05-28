From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import
  switcher kvs kvs_preamble kvs_spec_getFullKey kvs_spec_search kvs_spec_check_uint16.
From cap_machine Require Import region_invariants_revocation wp_rules_interp logrel_extra interp_weakening.
From cap_machine Require Import switcher_preamble switcher_spec_return.
From cap_machine Require Import proofmode map_simpl.

Section KVS_spec_addOrUpdate_safe.
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
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification from unknown *)
  Lemma KVS_addOrupdate_spec_safe_pre
    (W : WORLD) (C : CmptName)
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret wca0 wca1 wca2 : Word)
    (m : kvs_map) (s : kvs_alloc)
    ( E : coPset )
    :

    ↑Nkvs_otype ⊆ E ->

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_addOrUpdate_instrs)%a ->
    (cgp_b + length kvs_data)%a = Some cgp_e ->

    ( (* initial register file *)
      na_own logrel_nais E ∗
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp W C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ interp W C wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_addOrUpdate_instrs ∗
      cgp_b ↦ₐ kvs_service_unsealing_key ∗

      ▷ isKVS (cgp_b ^+ 1)%a m s ∗
      ▷ seal_pred KVS_OTYPE kvs_otype_propC ∗
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

         codefrag pc_a kvs_addOrUpdate_instrs ∗
         cgp_b ↦ₐ kvs_service_unsealing_key ∗
         (
           (* THERE IS AN EMPTY SLOT AVAILABLE*)
           (∃ idx (k : Z*Z) w,
               (ca0 ↦ᵣ WInt ASM_TRUE ∗ isKVS (cgp_b ^+ 1)%a (<[idx := (kvs_full_key k.1 k.2, w)]> m) s))
           ∨
             (* THERE IS AN EMPTY SLOT AVAILABLE *)
             (∃ idx (k : Z*Z) w,
                 ca0 ↦ᵣ WInt ASM_TRUE ∗
                 isKVS (cgp_b ^+ 1)%a (<[ idx := (kvs_full_key k.1 k.2, w)]> m) (kvs_alloc_insert s k.1 {[k.2]} ) )
           ∨
             (* THERE IS NO EMPTY SLOT AVAILABLE *)
             (ca0 ↦ᵣ WInt ASM_FALSE ∗ isKVS (cgp_b ^+ 1)%a m s)
         )

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    iIntros (HN HsubBounds Hcgp_contiguous)
      "(Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_wca0 & Hca1 & Hca2 & #Hinterp_wca2 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull] &
        Hcode & Hcgp_b & HKVS & Hspred & Hpost)".
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
             "[- $Hna $HPC $Hcgp $Hca0 $Hinterp_wca0 $Hca1 $Hct1 $Hcgp_b $Hcode $Hspred]"); eauto; [|iNext].
    { rewrite /withinBounds; solve_addr. }
    iIntros (user_key) "([%Huser_key_C ->] & #Hinv_kvs_ot & Hna & HPC & Hcgp & Hca0 & Hca1 & Hct1 & Hcgp_b & Hcode)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 3 "Hcode" as a_lea Ha_lea "Hcode" "Hcont"; iHide "Hcont" as hcont ; clear dependent Ha_get_full_key.
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (cgp_b ^+ 1)%a); [solve_addr|done]. }
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 4 "Hcode" as a_search Ha_search "Hcode" "Hcont"; iHide "Hcont" as hcont; clear dependent Ha_lea.
    iEval (replace (cgp_b ^+ 1)%a with (cgp_b ^+ (1+2*0))%a) in "Hcgp".
    iMod (na_inv_acc with "Hinv_kvs_ot Hna")
      as "( (%ku & %a & %s' & >%Heq & >%Hku_C & >%Hku & Hot_res) & Hna & HP_close)"
    ; eauto; simplify_eq; first solve_ndisj.
    iDestruct (lc_fupd_elim_later with "[$] [$Hot_res]") as ">[Halloc Hkvs_frags]".
    pose proof (kvs_users_seals_bounds C user_key Huser_key_C) as Huser_key_bound.
    assert ( wf_kvs_full_key user_key nkey) as Hwk_fkey by (split; auto; lia).

    destruct ( decide ( nkey ∈ s' ) ) as [Hfkey_in_s|Hfkey_notin_s].
    (* The key has already been allocated *)
    - iDestruct (big_sepS_elem_of_acc with "Hkvs_frags")
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

      iDestruct ("Hkvs_frags" with "[$Hkvs_frag]") as "Hkvs_frags".
      { iIntros (W' Hpriv_W_W').
        iApply monotone.interp_monotone_nl; eauto.
        destruct_word wca2; cbn; [done| | | | destruct sb]; destruct g; done.
      }
      iMod ("HP_close" with "[$Hna $Halloc $Hkvs_frags]") as "Hna"; eauto.
      {
        iNext; iPureIntro; exists a; split; auto.
        by replace (z_of a) with user_key by solve_addr+Hku.
      }

      iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Hcgp_b".
      iLeft; iExists idx, (user_key, nkey), wca2; iFrame.

    (* The key has never been allocated *)
    - iApply (KVS_search_spec_notin with "[- $HPC $Hcgp $Hca0 $Hct1 $Hct2 $HKVS $Halloc $Hcode]"); eauto.
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
      iDestruct "Hctp" as "[%wctp Hctp]".
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
    + (* an empty slot was found *)
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

      iDestruct ( big_sepS_insert with "[$Hkvs_frags Hfkey]") as "Hkvs_frags";eauto.
      { iExists wca2; iFrame.
        iIntros (W' Hpriv_W_W').
        iApply monotone.interp_monotone_nl; eauto.
        destruct_word wca2; cbn; [done| | | | destruct sb]; destruct g; done.
      }
      iMod ("HP_close" with "[$Hna $Halloc $Hkvs_frags]") as "Hna"; eauto.
      {
        iNext; iPureIntro; exists a; (repeat split); auto.
        by replace (z_of a) with user_key by solve_addr+Hku.
      }

      iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Hcgp_b".
      iRight; iLeft; iExists idx, (user_key, nkey), wca2; iFrame.
    + (* no empty slot found *)
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

      iMod ("HP_close" with "[$Hna $Halloc $Hkvs_frags]") as "Hna"; eauto.
      {
        iNext; iPureIntro; exists a; (repeat split); auto.
        by replace (z_of a) with user_key by solve_addr+Hku.
      }

      iApply "Hpost"; iFrame "Hna HPC Hcgp Hcra Hctp Hct1 Hct2 Hca1 Hca2 Hcnull Hcode Hcgp_b".
      iRight; iRight; iFrame.
  Qed.

  Lemma KVS_addOrupdate_spec_safe
    (W : WORLD) (C : CmptName)
    (wret wca0 wca1 wca2 : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->
    ↑Nkvs_otype ⊆ E ->

    ( na_inv logrel_nais Nkvs kvs_inv ∗
      na_own logrel_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_addOrUpdate_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ interp W C wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ wca1 ∗ (* Key to update *)
      ca2 ↦ᵣ wca2 ∗ interp W C wca2 ∗ (* New value *)
      ctp ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      ▷ (na_own logrel_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         (ca0 ↦ᵣ WInt ASM_TRUE ∨ ca0 ↦ᵣ WInt ASM_FALSE) ∗
         ca1 ↦ᵣ WInt 0 ∗
         ca2 ↦ᵣ - ∗
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ -
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    iIntros (Hnkvs_E Hnkvs_otype_E)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hinterp_ca0
      & Hca1 & Hca2 & Hinterp_ca2 & Hctp & Hct1 & Hct2 & Hcnull & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & >Himports & >Hcode & >Hcgp_b & HisKVS & #Hspred) & Hna & Hkvs_inv_close)"; eauto.
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
    iApply (KVS_addOrupdate_spec_safe_pre _ _ _ _ _ _ _ _ wca0 with "[- $HPC]"); last iFrame "∗#"; eauto.
    { pose proof Nkvs_namespaces_disjoint as (?&?&?); solve_ndisj. }

    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca1 & Hca2 & Hctp & Hct1 & Hct2
              & Hcnull & Hcode & Hcgp_b & HKVS)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iDestruct "HKVS" as
      "[ (%idx & %k & %w & Hca0 & HKVS) | [ (%idx & %k & %w & Hca0 & HKVS) | (Hca0 & HKVS) ] ]".
    all: iMod ("Hkvs_inv_close" with "[$Hna $Himports $Hcode $Hcgp_b $HKVS $Hspred]") as "Hna".
    all: iApply "Hpost"; iFrame.
  Qed.


  (*** Safe entry point  *)
  Lemma kvs_addOrUpdate_entry_point_spec
    (g_kvs_exp_tbl : Locality)

    (W : WORLD)
    (C : CmptName)

    (Nswitcher : namespace)
    :

    na_inv logrel_nais Nkvs kvs_inv ∗
    na_inv logrel_nais Nswitcher switcher_inv ∗
    inv (export_table_PCCN Nkvs_exp_tbl) (b_kvs_exp_tbl ↦ₐ WCap RX Global KVS_pcc_b KVS_pcc_e KVS_pcc_b) ∗
    inv (export_table_CGPN Nkvs_exp_tbl) ((b_kvs_exp_tbl ^+ 1)%a ↦ₐ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b) ∗
    inv (export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr)
        (kvs_addOrUpdate_exp_tbl_addr ↦ₐ kvs_exp_tbl_entry_addOrUpdate) ∗
    WSealed ot_switcher (SCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) ↦□ₑ kvs_addOrUpdate_nargs
    -∗
    ot_switcher_prop W C (WCap RO g_kvs_exp_tbl b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
  Proof.
    iIntros
      "(#Hinv_kvs & #Hinv_switcher
      & #Hkvs_exp_PCC
      & #Hkvs_exp_CGP
      & #Hkvs_exp_addOrRead
      & #Hentry_KVS
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
    iIntros "(HK & %Hframe_match & Hregister_state & Hrmap & Hr_C & Hsts_C & %Hsync_csp & Hcstk & Hna)".
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
    assert ( is_Some (rmap !! ctp) ) as [wctp Hwctp].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
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
    assert ( is_Some (rmap !! ca2) ) as [wca2 Hwca2].
    { apply Hrmap_init; rewrite Hrmap_dom ; done. }
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.

    iAssert (interp W0 C wca0) as "#Hinterp_wca0".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }
    iAssert (interp W0 C wca2) as "#Hinterp_wca2".
    { iApply "Hinterp_rmap"; eauto; by rewrite /kvs_addOrUpdate_nargs. }

    set ( csp_b := (csp_b' ^+ 4)%a ).
    set (stk_frame_addrs := finz.seq_between csp_b csp_e).
    iAssert ([∗ list] a ∈ stk_frame_addrs, ⌜W0.1 !! a = Some Temporary⌝)%I as "Hstk_frm_tmp_W0".
    { iApply (writeLocalAllowed_valid_cap_implies_full_cap with "Hinterp_W0_csp"); eauto. }
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W0_csp $Hsts_C $Hr_C]")
        as (l
           ) "(%Hl_unk & Hsts_C & Hr_C & #Hfrm_close_W0 & >%Hfrm_close_W0 & >[%stk_mem Hstk] & [Hrevoked_l %Hrevoked_l])".
    destruct Hl_unk as [Hl_unk Htemps].
    iAssert (▷ close_list_resources C W0 l false)%I with "[Hrevoked_l]" as "Hrevoked_l".
    { rewrite /close_list_resources /close_addr_resources /if_later_P; iNext; iFrame. }

    iApply KVS_addOrupdate_spec_safe; try solve_ndisj; iFrame "∗#".

    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hca2 & Hctp & Hct1 & Hct2 & Hcnull)".
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

    iApply (switcher_ret_specification _ W0 (revoke W0)
             with
             "[ $Hstk $Hcstk $HK $Hsts_C $Hna $HPC $Hr_C $Hrevoked_l
             $Hrmap $Hca0 $Hca1 $Hcsp]"
           ) ; eauto; last iFrame "∗#".
    { apply related_pub_revoke_close_list; eauto. }
    { apply regmap_full_dom in Hrmap_init.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap_init. set_solver+. }
    { subst csp_b. destruct Hsync_csp as [Hsync_csp <-]; eauto. }
    { iSplit; iApply interp_int. }
  Qed.

End KVS_spec_addOrUpdate_safe.
