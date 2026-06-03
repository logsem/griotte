From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.
From cap_machine Require Export kvs_preamble.
From cap_machine Require Import wp_rules_interp.

Section KVS_getFullKey.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ}
    {heapg : heapGS Σ}
    {kvsg:kvsG Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
    {KVS_layout : kvsLayout} {KVS_layout_WF : kvsLayoutWf} {KVS_users: kvs_users} {KVS_namespaces : kvs_namespaces}
  .

  (*** Specification for known code *)
  Lemma KVS_getFullKey_spec
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (rsealkey rkey rscratch : RegName)
    (user_key nkey : Z)
    :
    let instrs := (kvs_getFullKey_instrs rsealkey rsealkey rkey rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->
    (0 <= user_key < addr_reg.top)%Z ->

    rscratch ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rsealkey ↦ᵣ kvs_user_seal_key user_key ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch ↦ᵣ - ∗

      cgp_b ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
          rsealkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
          rkey ↦ᵣ WInt nkey ∗
          rscratch ↦ᵣ kvs_service_unsealing_key ∗

          cgp_b ↦ₐ kvs_service_unsealing_key ∗
          codefrag pc_a instrs -∗

          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp Hbounds_user_key Hrscratch Hrsealkey Hkey)
      "(HPC & Hcgp & Hrsealkey & Hrkey & [%wscratch Hrscratch] & Hcgp_b & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; done. }
    iEval (cbn) in "Hrscratch".

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
    (cgp_b cgp_e : Addr)
    (rsealkey rkey rscratch : RegName)
    (wskey : Word) (nkey : Z)
    ( E : coPset )
    :
    let instrs := (kvs_getFullKey_instrs rsealkey rsealkey rkey rscratch) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    withinBounds cgp_b cgp_e cgp_b = true ->

    ↑Nkvs_otype ⊆ E ->

    rscratch ≠ cnull ->
    rsealkey ≠ cnull ->
    rkey ≠ cnull ->

    related_sts_priv_world Wskey W ->

    (PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rsealkey ↦ᵣ wskey ∗ interp Wskey C wskey ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch ↦ᵣ - ∗

      cgp_b ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      seal_pred KVS_OTYPE kvs_otype_propC ∗

      sealing_map W C ∗
      sts_full_world W C ∗

      ▷ ( ∀ user_key ,
            ⌜ kvs_users_seals !! C = Some user_key ∧ wskey = kvs_user_seal_key user_key ⌝ ∗
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
            rsealkey ↦ᵣ WInt (kvs_full_key user_key nkey) ∗
            rkey ↦ᵣ WInt nkey ∗
            rscratch ↦ᵣ kvs_service_unsealing_key ∗

            cgp_b ↦ₐ kvs_service_unsealing_key ∗
            codefrag pc_a instrs ∗

            (sts_seals_std C KVS_OTYPE {[WSealable (kvs_user_seal_key_scap user_key)]}) ∗

            sealing_map W C ∗
            sts_full_world W C -∗

            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hbounds_cgp HN Hrscratch Hrsealkey Hkey Hrelated_Wskey_W)
      "(HPC & Hcgp & Hrsealkey
      & Hinterp_wskey & Hrkey & [%wscratch Hrscratch]
      & Hcgp_b & Hcode & #Hspred
      & Hseals & Hsts
      & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)

    (* load rscratch cgp; *)
    iInstr "Hcode".
    { split; done. }
    iEval (cbn) in "Hrscratch".

    (* unseal rdst rsealkey rscratch; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown with "[$HPC $Hi $Hrscratch $Hrsealkey]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hrsealkey & Hrscratch & %Heq & % & %spec)]".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    simplify_eq.
    iDestruct (monotone.interp_monotone_sd with "[] Hinterp_wskey") as "Hinterp_wskey"; auto.

    rewrite /kvs_service_unsealing_key in Heq; simplify_eq.
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_wskey".
    iAssert (sts_seals_std C KVS_OTYPE {[WSealable wsb]}) as "#Hinterp_wskey'".
    { iApply sts_seals_std_weaken; last iFrame "Hinterp_wskey"; last set_solver+. }
    iDestruct (open_sealing_map_singleton with "Hspred Hinterp_wskey' Hseals Hsts")
                as "(Hseals & Hsts & Hres_open & HP)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /kvs_otype_propC /safeC /= /kvs_otype_prop //= /kvs_otype_inv.
    iDestruct "HP" as "(%ku & %a & %s & %Heq_sb & %Hku_C & %Hku & Halloc & Hfkeys)"; simplify_eq.

    (* geta rdst rdst; *)
    iInstr "Hcode".
    replace (finz.to_z (0 ^+ a)%a) with ku by solve_addr.

    iAssert (kvs_otype_propC (W, C, WSealable (kvs_user_seal_key_scap a))) with "[Halloc Hfkeys]"
    as "HP".
    { iExists ku, a, s; iFrame "∗ %"; done. }
    iDestruct (close_sealing_map_singleton with "Hspred Hres_open HP Hseals") as "Hseals".

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
