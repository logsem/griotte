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
    {cstackg : CSTACKG Σ} {allocatorg : allocatorG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_namespaces : kvs_namespaces}
  .

  Lemma kvs_shadow_read_retained W C raw actual alloc_map :
    dom alloc_map = heap_addresses →
    load_memory_shadow_observation (shadow_status <$> alloc_map) RW raw actual →
    region W C -∗
    ([∗ map] a↦s ∈ alloc_map, allocator_entry a s) -∗
    ⌜filter_heap W actual = actual⌝ ∗
    region W C ∗
    ([∗ map] a↦s ∈ alloc_map, allocator_entry a s).
  Proof.
    iIntros (Hdom Hobs) "Hregion Hentries".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase; cycle 1.
    { rewrite /load_memory_shadow_observation Hbase in Hobs. subst actual.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      iFrame. iPureIntro. by apply filter_heap_nonheap. }
    assert (is_heap_address base = true) as Hheap.
    { unfold heap_cap_base in Hbase.
      destruct (memory_cap_base raw) as [b|] eqn:Hmemory; last discriminate.
      destruct (is_heap_address b) eqn:Hheap; last discriminate.
      by simplify_eq. }
    assert (is_Some (alloc_map !! base)) as [s Hlookup].
    { apply elem_of_dom. rewrite Hdom elem_of_heap_addresses. exact Hheap. }
    rewrite /load_memory_shadow_observation Hbase in Hobs.
    specialize (Hobs (shadow_status s)).
    assert ((shadow_status <$> alloc_map) !! base = Some (shadow_status s))
      as Hshadow_lookup by (rewrite lookup_fmap Hlookup; reflexivity).
    specialize (Hobs Hshadow_lookup).
    destruct s.
    - simpl in Hobs. subst actual.
      destruct (heap_authority_base raw) as [b|] eqn:Hauth; last first.
      { iFrame. iPureIntro. by apply filter_heap_nonheap. }
      pose proof (heap_authority_base_heap_cap_base raw b Hauth) as Hcap.
      rewrite Hbase in Hcap. inversion Hcap; subst b.
      destruct (heap_lookup_addr (heap_std W) base) as [bo|] eqn:Hheaplookup;
        last (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup).
      destruct bo as [bb obj]. destruct (alloc_object_status obj) eqn:Hstatus.
      { iFrame. iPureIntro. by rewrite /filter_heap Hauth Hheaplookup /= Hstatus. }
      assert (heap_cell_status (heap_std W) base = Some AllocObjectQuarantined)
        as Hqstatus by (rewrite /heap_cell_status Hheap Hheaplookup /= Hstatus; reflexivity).
      iEval (rewrite region_open_nil) in "Hregion".
      iDestruct (open_region_many_quarantined_token W C [] base with "Hregion")
        as "[Htoken Hrestore]"; [set_solver|exact Hqstatus|].
      iDestruct (big_sepM_lookup with "Hentries") as "Hentry"; first exact Hlookup.
      iDestruct (allocator_entry_token_quarantined with "Hentry Htoken")
        as %Himpossible. discriminate Himpossible.
    - simpl in Hobs. subst actual.
      destruct (heap_authority_base raw) as [b|] eqn:Hauth; last first.
      { iFrame. iPureIntro. by apply filter_heap_nonheap. }
      pose proof (heap_authority_base_heap_cap_base raw b Hauth) as Hcap.
      rewrite Hbase in Hcap. inversion Hcap; subst b.
      destruct (heap_lookup_addr (heap_std W) base) as [bo|] eqn:Hheaplookup;
        last (iFrame; iPureIntro; by rewrite /filter_heap Hauth Hheaplookup).
      destruct bo as [bb obj]. destruct (alloc_object_status obj) eqn:Hstatus.
      { iFrame. iPureIntro. by rewrite /filter_heap Hauth Hheaplookup /= Hstatus. }
      assert (heap_cell_status (heap_std W) base = Some AllocObjectQuarantined)
        as Hqstatus by (rewrite /heap_cell_status Hheap Hheaplookup /= Hstatus; reflexivity).
      iEval (rewrite region_open_nil) in "Hregion".
      iDestruct (open_region_many_quarantined_token W C [] base with "Hregion")
        as "[Htoken Hrestore]"; [set_solver|exact Hqstatus|].
      iDestruct (big_sepM_lookup with "Hentries") as "Hentry"; first exact Hlookup.
      iDestruct (allocator_entry_token_quarantined with "Hentry Htoken")
        as %Himpossible. discriminate Himpossible.
    - simpl in Hobs. subst actual.
      iFrame. iPureIntro. apply filter_heap_untagged, get_tag_clear_tag.
  Qed.

  Lemma kvs_load_read_retained E W C
    pc_p pc_g pc_b pc_e pc_a pc_a' dst src wi wd b e a raw :
    ↑Nallocator ⊆ E →
    is_shadow_address a = false →
    decodeInstrW wi = machine_instructions.Load dst src 0 →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull → src ≠ cnull →
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ wd ∗ src ↦ᵣ WCap true RW Global b e a ∗ a ↦ₐ raw ∗
        region W C ∗ allocator_ctx }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_heap raw actual ∧ filter_heap W actual = actual⌝ ∗
        PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' ∗ pc_a ↦ₐ wi ∗
        dst ↦ᵣ actual ∗ src ↦ᵣ WCap true RW Global b e a ∗
        a ↦ₐ raw ∗ region W C }}}.
  Proof.
    iIntros (HE Hshadow Hinstr Hvpc Hbounds Hpc Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hregion & #Halloc) HΦ".
    destruct (heap_cap_base raw) as [base|] eqn:Hbase.
    - iInv Nallocator as ">Halloc_body" "Halloc_close".
      iDestruct "Halloc_body" as (alloc_map Halloc_dom) "Halloc_entries".
      assert (is_Some (alloc_map !! base)) as [status Hlookup].
      { apply elem_of_dom. rewrite Halloc_dom elem_of_heap_addresses.
        unfold heap_cap_base in Hbase.
        destruct (memory_cap_base raw) as [base'|] eqn:Hmemory; last discriminate.
        destruct (is_heap_address base') eqn:Hheap; inversion Hbase; subst; done. }
      iDestruct (big_sepM_delete with "Halloc_entries") as "[Hentry Halloc_entries]";
        first exact Hlookup.
      iDestruct "Hentry" as "[Hstatus Hstatus_res]".
      destruct (shadow_status status) eqn:Hstatus_eq.
      + iApply (wp_load_success_heap_word with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (kvs_shadow_read_retained W C raw raw alloc_map
          with "Hregion Halloc_entries")
          as "(%Hretained & Hregion & Halloc_entries)";
          [exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; first by left. exact Hretained.
      + iApply (wp_load_success_heap_word_revoked with
          "[$HPC $Hi $Hdst $Hsrc $Ha $Hstatus]"); eauto.
        iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha & Hstatus)".
        iAssert ([∗ map] x↦s ∈ alloc_map, allocator_entry x s)%I
          with "[Hstatus Hstatus_res Halloc_entries]" as "Halloc_entries".
        { iApply big_sepM_delete; first exact Hlookup.
          iFrame. rewrite /allocator_entry Hstatus_eq. iFrame. }
        iDestruct (kvs_shadow_read_retained W C raw
          (clear_tag raw) alloc_map with "Hregion Halloc_entries")
          as "(%Hretained & Hregion & Halloc_entries)";
          [exact Halloc_dom| |].
        { unfold load_memory_shadow_observation. rewrite Hbase.
          intros observed Hobserved. rewrite lookup_fmap Hlookup in Hobserved.
          inversion Hobserved; subst. by rewrite Hstatus_eq. }
        iMod ("Halloc_close" with "[Halloc_entries]") as "_".
        { iNext. iExists alloc_map. iFrame. iPureIntro. exact Halloc_dom. }
        iModIntro. iApply "HΦ". iFrame.
        iPureIntro. split; last exact Hretained.
        right. split; last done. unfold is_heap_cap. by rewrite Hbase.
    - iApply (wp_load_success_notinstr with "[$HPC $Hi $Hdst $Hsrc $Ha]"); eauto.
      { unfold is_heap_cap. by rewrite Hbase. }
      iNext. iIntros "(HPC & Hdst & Hi & Hsrc & Ha)".
      iApply "HΦ". iFrame.
      iPureIntro. split; first by left.
      assert (heap_authority_base raw = None) as Hauth.
      { destruct (heap_authority_base raw) as [base'|] eqn:Hauth; last done.
        apply heap_authority_base_heap_cap_base in Hauth.
        rewrite Hbase in Hauth. discriminate. }
      by apply filter_heap_nonheap.
  Qed.

  (*** KVS READ: Read key in the KVS *)
  (** A successful read returns the stored word or, for a heap capability,
      its tag-cleared form. The physical and logical KVS entries keep the
      original word. Nonheap values are therefore returned unchanged.
   **)
  Lemma KVS_read_spec_in_layer_0
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
    (* Load ca1 cgp 0: the heap shadow can clear the returned tag. *)
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

  Lemma KVS_read_spec_in_layer_1
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


    iApply (KVS_read_spec_in_layer_0 with
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

  Lemma KVS_read_spec_in_layer_2
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

    iApply (KVS_read_spec_in_layer_1 with
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


  Lemma KVS_read_spec_in
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

    iApply (KVS_read_spec_in_layer_2
             with "[- $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                    $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hna
                    & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                    & Ha_user_key & Hm)".

    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.



  (** Read layers retaining the observed heap shadow status. *)
  Lemma KVS_read_spec_in_layer_0_world
    (W : WORLD) (C : CmptName)
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

    ( allocator_ctx ∗
      region W C ∗
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
      codefrag kvs_read_pcc_addr kvs_read_instrs ∗
      (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      ▷ is_physical_kvs KVS_cgp_b pkvs ∗

      ▷ (
          region W C ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
           (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜load_heap w actual ∧ filter_heap W actual = actual⌝) ∗ (* result of the read *)
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
      "(#Halloc & Hregion & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & [%wcnull Hcnull]
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
    (* Load ca1 cgp 0: the heap shadow can clear the returned tag. *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (kvs_load_read_retained _ W C with
      "[$HPC $Hi $Hca1 $Hcgp $Hcgp_val $Hregion $Halloc]");
      try solve_pure; try solve_addr.
    { eapply disjoint_from_shadow_not_in; first exact Hcgp_shadow.
      rewrite /withinBounds; solve_addr. }
    iIntros "!>" (actual)
      "(%Hactual & HPC & Hi & Hca1 & Hcgp & Hcgp_val & Hregion)".
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

  Lemma KVS_read_spec_in_layer_1_world
    (W : WORLD) (C : CmptName)
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

    ( allocator_ctx ∗
      region W C ∗
      na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
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

      ▷ ( region W C ∗
          na_own cerise_nais E ∗
          PC ↦ᵣ updatePcPerm wret ∗
          cgp ↦ᵣ - ∗
          cra ↦ᵣ - ∗
          ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
           (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜load_heap w actual ∧ filter_heap W actual = actual⌝) ∗ (* result of the read *)
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
      "(#Halloc & Hregion & #Hkvs_inv & Hna
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


    iApply (KVS_read_spec_in_layer_0_world W C with
             "[- $Halloc $Hregion $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); last iFrame; eauto.
    iNext; iIntros "(Hregion & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
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

  Lemma KVS_read_spec_in_layer_2_world
    (W : WORLD) (C : CmptName)
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

    ( allocator_ctx ∗
      region W C ∗
      na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
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

      ▷ (region W C ∗
         na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
          (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜load_heap w actual ∧ filter_heap W actual = actual⌝) ∗ (* result of the read *)
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
      "(#Halloc & Hregion & #Hkvs_inv & #Hkvs_logical_inv & Hna
      & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_read_spec_in_layer_1_world W C with
             "[- $Halloc $Hregion $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }

    iNext; iIntros "(Hregion & Hna
                     & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & Hlkvs_auth & HLKVS & Hm)".

    iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_read_spec_in_world
    (W : WORLD) (C : CmptName)
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

    ( allocator_ctx ∗
      region W C ∗
      na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
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

      ▷ (region W C ∗
         na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_TRUE ∗ (* TRUE: the key exists in the map *)
          (∃ actual, ca1 ↦ᵣ actual ∗
             ⌜load_heap w actual ∧ filter_heap W actual = actual⌝) ∗ (* result of the read *)
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
      "(#Halloc & Hregion & #Hkvs_inv & #Hkvs_logical_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
       & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & >Hk & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_Some _ _ _ _ _ Hk) as Hm_kvs; eauto.

    iApply (KVS_read_spec_in_layer_2_world W C
             with "[- $Halloc $Hregion $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                    $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hregion & Hna
                    & HPC & Hcgp & Hcra & Hca0 & [%actual [Hca1 %Hactual]] & Hctp & Hct1 & Hct2 & Hcnull
                    & Ha_user_key & Hm)".

    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_read_spec_notin_layer_0
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (pkvs : kvs_physical_map)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    SubBounds KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr (kvs_read_pcc_addr ^+ length kvs_read_instrs)%a ->
    (KVS_cgp_b + length kvs_data)%a = Some KVS_cgp_e ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    fkey ∉ kvs_keys pkvs ->

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
          ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: the key does not exist in the map *)
          ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
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

    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".read_uint16_check_pass")%asm; *)
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
    iApply (KVS_search_spec_empty_slot with "[- $HPC $Hcgp $Hca0 $Hctp $Hct1 $Hct2 $HPKVS $Hcode]"); eauto using KVS_cgp_disjoint_from_shadow.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "[
    (%idx_empty & HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS
    & Hcgp_opt & [%wkey Hcgp_key] & [%wval Hcgp_val] & %Hcgp_bounds
    & %Hidx_empty & %Hpkvs_idx_empty & Hcode)
    | (HPC & Hcgp & Hca0 & Hctp & Hct1 & Hct2 & HPKVS & Hcode) ]".
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

        iDestruct (kvs_physical_map_close with "[$HPKVS] [Hcgp_opt Hcgp_key Hcgp_val]") as "HPKVS";eauto.
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

  Lemma KVS_read_spec_notin_layer_1
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (lkvs : kvs_logical_map) (m : kvs_user_map)
    (E : coPset)
    :

    let fkey := (kvs_full_key user_key nkey) in

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ E ->

    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    is_uint16 nkey ->

    m !! nkey = None  ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

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
          ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: the key does not exist in the map *)
          ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
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
    pose proof (kvs_synced_logical_lookup_None _ _ _ _ _
                  His_uint16_nkey Hsync Hlkvs_user_key Hm_nkey)
      as Hpkvs_idx.

    iApply (KVS_read_spec_notin_layer_0 with
             "[- $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
              $Hcode $Ha_unsealing $Ha_user_key
              $HPKVS]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
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


  Lemma KVS_read_spec_notin_layer_2
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (m : kvs_user_map)
    (E : coPset)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->

    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->

    m !! nkey = None ->

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
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: the key does not exist in the map *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
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
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key Hm_nkey)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
        & Ha_user_key & Hm & Hpost)".
    iMod (na_inv_acc with "Hkvs_logical_inv Hna")
      as "( (%lkvs & Hlkvs_auth & HLKVS) & Hna & Hkvs_logical_inv_close)"; eauto.

    iApply (KVS_read_spec_notin_layer_1 with
             "[- $Hkvs_inv
                 $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                 $Ha_user_key
                 $Hlkvs_auth $HLKVS $Hm]"); last iFrame; eauto.
    {  solve_ndisj. }

    iNext; iIntros "(Hna
                     & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
                     & Ha_user_key
                     & Hlkvs_auth & HLKVS & Hm)".

    iMod ("Hkvs_logical_inv_close" with "[$Hna $Hlkvs_auth $HLKVS]") as "Hna" ; auto.
    iApply "Hpost"; iFrame; done.
  Qed.

  Lemma KVS_read_spec_notin
    (wret : Word)
    (user_key : user_key_t) (nkey : map_key_t) (l_user_key : Locality) (user_key_addr : Addr)
    (E : coPset)
    :

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
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* FALSE: the key does not exist in the map *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
         ctp ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ct2 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         user_key_addr ↦ₐ WInt user_key ∗

         user_kvs_inv user_key ∗
         (user_key, nkey) ↦(KVS) ⊥

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Huser_key_shadow Hnkvs_E Hnkvs_E' His_uint16_nkey Hbounds_a_user_key)
      "(#Hkvs_inv & #Hkvs_logical_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
      & Ha_user_key & (%ukvs & >Hukvs_auth & (%m & Hm & >%Hsync)) & >Hk & Hpost)".

    iDestruct (kvs_user_kvs_valid with "Hukvs_auth Hk") as "%Hk".
    opose proof (kvs_synced_logical_user_kvs_None _ _ _ _ Hk) as Hm_kvs; eauto.

    iApply (KVS_read_spec_notin_layer_2
             with "[- $Hkvs_inv $Hkvs_logical_inv $Hna
                    $HPC $Hcgp $Hcra $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
                     $Ha_user_key $Hm]"); eauto.
    iNext; iIntros "(Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct1 & Hct2 & Hcnull
              & Ha_user_key & Hm)".

    iAssert (user_kvs_inv user_key)%I with "[$Hm $Hukvs_auth]" as "Hlukvs"; auto.

    iApply "Hpost"; iFrame; done.
  Qed.

  (*** KVS READ: Ill-formed inputs *)

  Lemma KVS_read_spec_not_uint16_map_key_pre
    (pc_b pc_e pc_a : Addr)
    (wret : Word)
    (wca1 : Word)
    :

    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs)%a ->
    ¬ word_is_uint16 wca1 ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_read_instrs ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt ASM_FALSE ∗ (* ERROR: map key is not a unint16  *)
         ca1 ↦ᵣ WInt 0 ∗ (* Dummy value *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         codefrag pc_a kvs_read_instrs
         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (HsubBounds Hnkey_is_uint16)
      "(HPC & Hcra & [%wca0 Hca0] & Hca1 & Hct1 & [%wcnull Hcnull] & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_read_instrs /assembled_kvs_read.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_not_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".read_not_uint16")%asm ct1; *)
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

  Lemma KVS_read_spec_not_uint16_map_key
    (wret : Word)
    (wca1 : Word)
    (E : coPset)
    :

    ↑(Nkvs.@"physical") ⊆ E ->

    ¬ word_is_uint16 wca1 ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ wca1 ∗ (* Key to read *)
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
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
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
    focus_block_nochangePC 1 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    iApply ( KVS_read_spec_not_uint16_map_key_pre ); eauto; iFrame.
    iNext; iIntros "(HPC & Hcra & Hca0 & Hca1 & Hct1 & Hcnull & Hcode)".

    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    iMod ("Hkvs_inv_close" with "[$Hna $Hcode $Himports $HKVS]") as "Hna".
    iApply "Hpost"; iFrame.
  Qed.

  Lemma KVS_read_spec_invalid_sealed_user_key_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    :

    is_shadow_address (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_read_instrs)%a ->
    is_uint16 nkey ->
    (is_sealed_with_o wca0 KVS_OTYPE = false \/ get_tag wca0 = false) ->

    (cgp_b + length kvs_data)%a = Some cgp_e ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap true RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_read_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow HsubBounds Hnkey_is_uint16 Hwca0 Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct1 & Hct2 & Hctp
      & [%wcnull Hcnull] & Hcode & Ha_unsealing)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.


    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_read_instrs /assembled_kvs_read.
    rewrite -/(kvs_getFullKey ctp ca0 ca1 ct1 ct2).
    rewrite -/(kvs_search ca0 ctp ct1 ct2).
    rewrite -/(kvs_check_uint16 ca1 ct1).

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (KVS_check_uint16_spec_is_uint16 with "[- $HPC $Hca1 $Hct1 $Hcode]"); eauto;iNext.
    iIntros "(HPC & Hca1 & Hcode & Hct1)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_check_uint Ha_check_uint "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* jnz (".read_not_uint16")%asm ct1; *)
    iInstr "Hcode".
    (* jmp (".read_uint16_check_pass")%asm; *)
    iInstr "Hcode".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 2 "Hcode" as a_get_full_key Ha_get_full_key "Hcode" "Hcont"; iHide "Hcont" as hcont
    ; clear dependent Ha_check_uint.
    iApply (KVS_getFullKey_spec_invalid_sealed_user_key with "[- $HPC $Hctp $Hca0 $Hct1 $Hct2 $Ha_unsealing $Hcode]") ; eauto; iNext.
  Qed.

  Lemma KVS_read_spec_invalid_sealed_user_key
    (wret : Word)
    (wca0 : Word)
    (nkey : Z)
    (E : coPset)
    :

    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    ↑(Nkvs.@"physical") ⊆ E ->

    is_uint16 nkey ->
    (is_sealed_with_o wca0 KVS_OTYPE = false \/ get_tag wca0 = false) ->

    ( na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap true RX Global KVS_pcc_b KVS_pcc_e kvs_read_pcc_addr ∗
      cgp ↦ᵣ WCap true RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ wca0 ∗ (* Sealed User Key *)
      ca1 ↦ᵣ WInt nkey ∗ (* Key to read *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ct2 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ -

      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow HE Hnkey_is_uint16 Hwca0)
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
    focus_block_nochangePC 1 "Hcode" as a_read Ha_read "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_read = kvs_read_pcc_addr) as -> by (rewrite /kvs_read_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_read).
    iApply ( KVS_read_spec_invalid_sealed_user_key_pre ); eauto; iFrame.
  Qed.

  Lemma KVS_read_spec_known_to_known
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (arg_rmap : Reg) (cstk : CSTK) (E : coPset)
    (user_key : user_key_t) (nkey : map_key_t)
    (l_user_key : Locality) (user_key_addr : Addr) (w : Word) :
    is_shadow_address (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a = false ->
    is_shadow_address user_key_addr = false ->
    is_heap_cap w = false ->
    ↑(Nkvs.@"physical") ⊆ E ->
    ↑(Nkvs.@"logical") ⊆ E ->
    is_uint16 nkey ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->
    arg_rmap !! ca0 = Some (kvs_user_seal_key l_user_key user_key_addr) ->
    arg_rmap !! ca1 = Some (WInt nkey) ->
    na_inv cerise_nais (Nkvs.@"physical") kvs_inv ∗
    na_inv cerise_nais (Nkvs.@"logical") logical_kvs_inv
    ⊢
    switcher_cc_specification_known_to_known_function
      (user_key_addr ↦ₐ WInt user_key ∗
       user_kvs_inv user_key ∗
       (user_key, nkey) ↦(KVS) w)
      (λ wca0 wca1,
         user_key_addr ↦ₐ WInt user_key ∗
         user_kvs_inv user_key ∗
         (user_key, nkey) ↦(KVS) w ∗
         ⌜ wca0 = WInt ASM_TRUE ⌝ ∗
         ⌜ wca1 = w ⌝)
      wcgp_caller wcra_caller wcs0_caller wcs1_caller
      b_stk e_stk a_stk arg_rmap cstk kvs_read_nargs E
      KVS_pcc_b KVS_pcc_e KVS_cgp_b KVS_cgp_e kvs_read_pcc_off.
  Proof.
    pose proof KVS_cgp_disjoint_from_shadow as Hcgp_shadow.
    iIntros (Hunsealing_shadow Huser_key_shadow Hw_nonheap Hphysical Hlogical Hnkey Huser_key Hca0_arg Hca1_arg).
    rewrite /switcher_cc_specification_known_to_known_function.
    iIntros "[ #Hkvs #Hkvs_logical ]" (arg_rmap' rmap')
      "#Halloc (%Harg_rmap' & %Hrmap' & Hna & HPC & Hcgp & Hcra & Hcsp
       & Hargs & Hrmap & Hstk & Hcstk
       & (Huser_key & Huser_kvs & Hkey)
       & Hpost)".
    iEval (cbn) in "HPC".

    iExtractList "Hargs" [ca0;ca1;ca2;ca3;ca4;ca5;ct0]
      as ["[Hca0 %Hwca0]";"[Hca1 %Hwca1]";"[Hca2 %Hwca2]";
          "[Hca3 %Hwca3]";"[Hca4 %Hwca4]";"[Hca5 %Hwca5]";
          "[Hct0 %Hwct0]"]
    ; iClear "Hargs".
    destruct (decide (ca0 ∈ dom_arg_rmap kvs_read_nargs)) as [_|]; last done.
    destruct (decide (ca1 ∈ dom_arg_rmap kvs_read_nargs)) as [_|]; last done.
    destruct (decide (ca2 ∈ dom_arg_rmap kvs_read_nargs)) as [|_]; first done.
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

    iApply (KVS_read_spec_in with
      "[- $Hkvs $Hkvs_logical $Hna $HPC $Hcgp $Hcra
       $Hca0 $Hca1 $Hctp $Hct1 $Hct2 $Hcnull
       $Huser_key $Huser_kvs $Hkey]"); auto.
    iNext.
    iIntros "(Hna & HPC & [%wcgp Hcgp] & [%wcra Hcra]
              & Hca0 & (%actual & Hca1 & %Hactual) & [%wct1 Hct1] & [%wct2 Hct2]
              & [%wctp Hctp] & [%wcnull Hcnull]
              & Huser_key & Huser_kvs & Hkey)".
    destruct Hactual as [-> | Hcleared]; last (destruct Hcleared as [Hheap _]; congruence).
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap _]".
    iInsertList "Hrmap" [ctp;ct1;ct2;cnull;ca2;ca3;ca4;ca5;ct0].
    set (rmap_ret0 := delete cs1 (delete cs0 rmap')).
    set (rmap_ret1 := <[ctp := wctp]> rmap_ret0).
    set (rmap_ret2 := <[ct1 := wct1]> rmap_ret1).
    set (rmap_ret3 := <[ct2 := wct2]> rmap_ret2).
    set (rmap_ret4 := <[cnull := wcnull]> rmap_ret3).
    set (rmap_ret5 := <[ca2 := WInt 0]> rmap_ret4).
    set (rmap_ret6 := <[ca3 := WInt 0]> rmap_ret5).
    set (rmap_ret7 := <[ca4 := WInt 0]> rmap_ret6).
    set (rmap_ret8 := <[ca5 := WInt 0]> rmap_ret7).
    set (rmap_ret := <[ct0 := WInt 0]> rmap_ret8).
    iEval (cbn) in "HPC".

    iApply ("Hpost" $! (WInt ASM_TRUE) w rmap_ret
              (region_addrs_zeroes (a_stk ^+ 4)%a e_stk)).
    iSplit.
    { iPureIntro.
      rewrite /rmap_ret /rmap_ret8 /rmap_ret7 /rmap_ret6 /rmap_ret5
        /rmap_ret4 /rmap_ret3 /rmap_ret2 /rmap_ret1 /rmap_ret0.
      repeat (rewrite dom_insert_L).
      repeat (rewrite dom_delete_L).
      rewrite Hrmap' /dom_arg_rmap /=. set_solver+. }
    iFrame.
    iFrame. iSplit; first done. done.
  Qed.


End KVS_spec_read.
