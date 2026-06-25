From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import wp_rules_interp.
From griotte Require Import switcher kvs.
From griotte Require Export kvs_preamble.

Section KVS_getFullKey.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {relg : relGS Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification for known code *)
  Lemma KVS_getFullKey_spec
    (pc_b pc_e pc_a : Addr)
    (rdst rsealkey rkey rscratch1 rscratch2 : RegName)
    (user_key nkey : Z) (l_user_key : Locality) ( user_key_addr : Addr )
    :
    let instrs := (kvs_getFullKey_instrs rdst rsealkey rkey rscratch1 rscratch2) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    (0 <= user_key < MAX_USER_KEY)%Z ->
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->


    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch1 ↦ᵣ - ∗
      rscratch2 ↦ᵣ - ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rdst ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
          rkey ↦ᵣ WInt nkey ∗
          rscratch1 ↦ᵣ WInt (pc_b - pc_a) ∗
          rscratch2 ↦ᵣ WInt pc_a ∗

          (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          user_key_addr ↦ₐ WInt user_key ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_user_key Hbounds_user_key_addr Hrscratch1 Hrscratch2 Hrsealkey Hkey Hdst)
      "(HPC & [%wdst Hrdst] & Hrsealkey & Hrkey & [%wscratch1 Hrscratch1] & [%wscratch2 Hrscratch2]
      & Ha_unsealing & Ha_user_key & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea;[solve_addr|].
    assert ((pc_b + UNSEALING_USER_KEY_OFFSET)%a = Some (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a) as Hpc_bn
    ;[rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr|].
    (* mov rdst PC; *)
    iInstr "Hcode".
    (* getb rscratch1 rdst; *)
    iInstr "Hcode".
    (* geta rscratch2 rdst; *)
    iInstr "Hcode".
    (* sub rscratch1 rscratch1 rscratch2; *)
    iInstr "Hcode".
    (* lea rdst rscratch1; *)
    iInstr "Hcode".
    (* lea rdst UNSEALING_USER_KEY_OFFSET; *)
    iInstr "Hcode".
    (* load rdst rdst; *)
    iInstr "Hcode".
    { rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr. }
    (* unseal rdst rsealkey rscratch; *)
    iInstr "Hcode"; first done.
    { rewrite /withinBounds; pose proof KVS_OTYPE_size; solve_addr. }
    (* load rdst rdst; *)
    iInstr "Hcode".
    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  (*** Specification for unknown code *)
  Lemma KVS_getFullKey_spec_safe
    (Wskey W : WORLD) (C : CmptName)
    (pc_b pc_e pc_a : Addr)
    (rdst rsealkey rkey rscratch1 rscratch2 : RegName)
    (wskey : Word) (nkey : Z)
    ( E : coPset )
    :
    let instrs := (kvs_getFullKey_instrs rdst rsealkey rkey rscratch1 rscratch2) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->

    ↑Nkvs_otype ⊆ E ->

    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->
    rdst ≠ cnull ->

    related_sts_priv_world Wskey W ->

    (PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ wskey ∗ interp Wskey C wskey ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch1 ↦ᵣ - ∗
      rscratch2 ↦ᵣ - ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      seal_pred KVS_OTYPE kvs_otype_propC ∗

      world_interp W C ∗

      ▷ ( ∀ (s : gset Z) (l_user_key : Locality) (user_key_addr : Addr) (user_key : Z) ,
            ⌜ wskey = kvs_user_seal_key l_user_key user_key_addr ⌝ ∗
            ⌜ (0 <= user_key < MAX_USER_KEY)%Z ⌝ ∗
            ⌜ withinBounds user_key_addr (user_key_addr ^+1)%a user_key_addr = true ⌝ ∗
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            rdst ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
            rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
            rkey ↦ᵣ WInt nkey ∗
            rscratch1 ↦ᵣ WInt (pc_b - pc_a) ∗
            rscratch2 ↦ᵣ WInt pc_a ∗

            (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
            codefrag pc_a instrs ∗
            user_key_addr ↦ₐ WInt user_key ∗
            sealing_map_resource_open W C KVS_OTYPE kvs_otype_propC {[WSealable (kvs_user_seal_key_scap l_user_key user_key_addr)]} ∗
            ◯(ALLOC)[ user_key ] s ∗
            ([∗ set] kn ∈ s, ∃ w : Word, kvs_full_key user_key kn⤇(KVS) w ∗ ∀ W' : WORLD
             , ⌜related_sts_priv_world W W'⌝ -∗ interp W' C w) ∗

            world_interp_sopen W C KVS_OTYPE
            -∗

            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds HN Hrscratch1 Hrscratch2 Hrsealkey Hkey Hdst Hrelated_Wskey_W)
      "(HPC & [%wdst Hrdst] & Hrsealkey
      & Hinterp_wskey & Hrkey & [%wscratch1 Hrscratch1]  & [%wscratch2 Hrscratch2]
      & Ha_unsealing & Hcode & #Hspred
      & Hworld
      & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    assert ((pc_a + (pc_b - pc_a))%a = Some pc_b) as Hlea;[solve_addr|].
    assert ((pc_b + UNSEALING_USER_KEY_OFFSET)%a = Some (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a) as Hpc_bn
    ;[rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr|].
    (* mov rdst PC; *)
    iInstr "Hcode".
    (* getb rscratch1 rdst; *)
    iInstr "Hcode".
    (* geta rscratch2 rdst; *)
    iInstr "Hcode".
    (* sub rscratch1 rscratch1 rscratch2; *)
    iInstr "Hcode".
    (* lea rdst rscratch1; *)
    iInstr "Hcode".
    (* lea rdst UNSEALING_USER_KEY_OFFSET; *)
    iInstr "Hcode".
    (* load rdst rdst; *)
    iInstr "Hcode".
    { rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr. }
    iEval (cbn) in "Hrdst".

    (* unseal rdst rsealkey rscratch; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown' with "[$HPC $Hi $Hrdst $Hrsealkey]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hrdst & Hrsealkey & %Heq & % & %spec)]".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    simplify_eq.
    iDestruct (monotone.interp_monotone_sd with "[] Hinterp_wskey") as "Hinterp_wskey"; auto.

    rewrite /kvs_service_unsealing_key in Heq; simplify_eq.
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_wskey".
    iAssert (sts_seals_std C KVS_OTYPE {[WSealable wsb]}) as "#Hinterp_wskey'".
    { iApply sts_seals_std_weaken; last iFrame "Hinterp_wskey"; last set_solver+. }
    iDestruct (sopen_world_interp_singleton with "Hspred Hinterp_wskey' Hworld")
                as "(Hworld & Hres_open & HP)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /kvs_otype_propC /= /kvs_otype_prop //= /kvs_otype_inv.
    iDestruct "HP" as "(%ku & %a & %s & %Heq_sb & %Hku & %Hbounds & Ha & Halloc & Hfkeys)".
    destruct wsb; rewrite /kvs_user_seal_key_scap in Heq_sb; cbn in Heq_sb; simplify_eq.
    rewrite -/(kvs_user_seal_key_scap g a).

    (* load rdst rdst; *)
    iInstr "Hcode".

    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame "∗#%".
    iPureIntro; auto.
  Qed.

End KVS_getFullKey.
