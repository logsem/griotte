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
    withinBounds user_key_addr (user_key_addr ^+ 1)%a user_key_addr = true ->


    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ kvs_user_seal_key l_user_key user_key_addr ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch1 ↦ᵣ - ∗
      rscratch2 ↦ᵣ - ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      user_key_addr ↦ₐ WInt user_key ∗

      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
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
    iIntros (HsubBounds Hbounds_user_key_addr Hrscratch1 Hrscratch2 Hrsealkey Hkey Hdst)
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
    (* unseal rdst rsealkey rscratch; *)
    iInstr "Hcode".
    (* load rdst rdst; *)
    iInstr "Hcode".
    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
  Qed.

  (*** Specification for unknown code *)
  Lemma KVS_getFullKey_spec_invalid_sealed_user_key
    (pc_b pc_e pc_a : Addr)
    (rdst rsealkey rkey rscratch1 rscratch2 : RegName)
    ( wsealkey : Word )
    :
    let instrs := (kvs_getFullKey_instrs rdst rsealkey rkey rscratch1 rscratch2) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->

    (is_sealed_with_o wsealkey KVS_OTYPE = false \/ get_tag wsealkey = false) ->

    rscratch1 ≠ cnull ->
    rscratch2 ≠ cnull ->
    rsealkey ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      rdst ↦ᵣ - ∗
      rsealkey ↦ᵣ wsealkey ∗
      rscratch1 ↦ᵣ - ∗
      rscratch2 ↦ᵣ - ∗

      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗

      codefrag pc_a instrs
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hnot_sealed_with_kvs_otype Hrscratch1 Hrscratch2 Hrsealkey Hdst)
      "(HPC & [%wdst Hrdst] & Hrsealkey & [%wscratch1 Hrscratch1] & [%wscratch2 Hrscratch2]
      & Ha_unsealing & Hcode)".
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
    (* unseal rdst rsealkey rscratch; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown' with "[$HPC $Hi $Hrdst $Hrsealkey]"); try solve_pure.
    iIntros "!>" (ret)
      "[-> | [(% & % & % & % & % & %o & %wsb & -> & HPC & Hi & Hrdst & Hrsealkey & %Heq & % & %spec & %Htag & %Hrange)
      | (%tsr & %psr & %gsr & %bsr & %esr & %asr & %ot & %sb
         & -> & HPC & Hi & Hrdst & Hrsealkey & %Heq & %Hsealed & %Hinvalid)]]".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    {
    destruct Hnot_sealed_with_kvs_otype as [Hnot_sealed_with_kvs_otype | Hclear].
    2: { rewrite spec /= Htag in Hclear; done. }
    rewrite spec in Hnot_sealed_with_kvs_otype.
    rewrite /kvs_service_unsealing_key /load_word //= in Heq; simplify_eq.
    apply withinBounds_le_addr in Hrange.
    assert (o = KVS_OTYPE) as -> by solve_addr.
    cbn in Hnot_sealed_with_kvs_otype.
    by rewrite Z.eqb_neq in Hnot_sealed_with_kvs_otype.
    }
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iInstr "Hcode".
    wp_end; iIntros "%Hcontr"; done.
  Qed.

End KVS_getFullKey.
