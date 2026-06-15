From iris.proofmode Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.
From griotte Require Import proofmode.
From griotte Require Export kvs_preamble.
From griotte Require Import wp_rules_interp.

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
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification for known code *)
  Lemma KVS_getFullKey_spec
    (pc_b pc_e pc_a : Addr)
    (rdst rsealkey rkey rscratch1 rscratch2 : RegName)
    (user_key nkey : Z) (l_user_key : Locality)
    :
    let instrs := (kvs_getFullKey_instrs rdst rsealkey rkey rscratch1 rscratch2) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    (0 <= user_key < addresses.top)%Z ->

    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch1 ↦ᵣ - ∗
      rscratch2 ↦ᵣ - ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rdst ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rsealkey ↦ᵣ WSealed KVS_OTYPE (kvs_user_seal_key_scap l_user_key user_key) ∗
          rkey ↦ᵣ WInt nkey ∗
          rscratch1 ↦ᵣ WInt (pc_b - pc_a) ∗
          rscratch2 ↦ᵣ WInt pc_a ∗

          (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_user_key Hrscratch1 Hrscratch2 Hrsealkey Hkey Hdst)
      "(HPC & [%wdst Hrdst] & Hrsealkey & Hrkey & [%wscratch1 Hrscratch1] & [%wscratch2 Hrscratch2]
      & Ha_unsealing & Hcode & Hpost)".
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
    (* geta rdst rdst; *)
    iInstr "Hcode".
    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    replace (Z.lor ((0 ^+ user_key)%a ≪ 16) nkey) with (kvs_full_key user_key nkey).
    2: {
      replace (@finz.to_z MemNum (0 ^+ user_key)%a) with user_key; first done.
      solve_addr.
    }

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

      ▷ ( ∀ l_user_key user_key ,
            ⌜ kvs_users_seals !! C = Some user_key ∧ wskey = kvs_user_seal_key l_user_key user_key ⌝ ∗
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            rdst ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
            rsealkey ↦ᵣ WSealed KVS_OTYPE (kvs_user_seal_key_scap l_user_key user_key) ∗
            rkey ↦ᵣ WInt nkey ∗
            rscratch1 ↦ᵣ WInt (pc_b - pc_a) ∗
            rscratch2 ↦ᵣ WInt pc_a ∗

            (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
            codefrag pc_a instrs ∗

            (sts_seals_std C KVS_OTYPE {[WSealable (kvs_user_seal_key_scap l_user_key user_key)]}) ∗

            world_interp W C
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
    iDestruct "HP" as "(%ku & %a & %s & %Heq_sb & %Hku_C & %Hku & Halloc & Hfkeys)".
    destruct wsb; rewrite /kvs_user_seal_key_scap in Heq_sb; cbn in Heq_sb; simplify_eq.
    rewrite -/(kvs_user_seal_key_scap g a).

    (* geta rdst rdst; *)
    iInstr "Hcode".
    replace (finz.to_z (0 ^+ a)%a) with ku by solve_addr.

    iAssert (kvs_otype_propC (W, C, (force_global (WSealable (kvs_user_seal_key_scap g a))))) with "[Halloc Hfkeys]"
    as "HP".
    { iExists ku, a, s; iFrame "∗ %"; done. }
    iDestruct (sclose_world_interp_singleton with "Hspred Hres_open HP Hworld") as "Hworld".

    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    replace (Z.lor (ku ≪ 16) nkey) with (kvs_full_key ku nkey) by solve_addr.
    replace (z_of a) with ku by solve_addr+Hku.
    iApply "Hpost"; iFrame "∗#".
    iPureIntro; split; auto.
  Qed.

End KVS_getFullKey.
