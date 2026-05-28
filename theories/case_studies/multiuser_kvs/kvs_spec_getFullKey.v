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
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
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
    (0 <= user_key < top)%Z ->

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
    (W : WORLD) (C : CmptName)
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

    ( na_own logrel_nais E ∗
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      rsealkey ↦ᵣ wskey ∗ interp W C wskey ∗
      rkey ↦ᵣ WInt nkey ∗
      rscratch ↦ᵣ - ∗

      cgp_b ↦ₐ kvs_service_unsealing_key ∗
      codefrag pc_a instrs ∗
      seal_pred KVS_OTYPE kvs_otype_propC ∗

      ▷ ( ∀ user_key ,
            ⌜ kvs_users_seals !! C = Some user_key ∧ wskey = kvs_user_seal_key user_key ⌝ ∗
            na_inv logrel_nais (Nkvs_otype.@C) (kvs_otype_inv W C (WSealable (kvs_user_seal_key_scap user_key))) ∗
            na_own logrel_nais E ∗
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
    iIntros (HsubBounds Hbounds_cgp HN Hrscratch Hrsealkey Hkey)
      "(Hna & HPC & Hcgp & Hrsealkey & Hinterp_wskey & Hrkey & [%wscratch Hrscratch] & Hcgp_b & Hcode & Hspred & Hpost)".
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

    rewrite /kvs_service_unsealing_key in Heq; simplify_eq.
    rewrite (fixpoint_interp1_eq _ _ (WSealed KVS_OTYPE wsb)).
    iDestruct "Hinterp_wskey" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hspred HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable wsb)).
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    rewrite /kvs_otype_propC /safeC /= /kvs_otype_prop //=.
    iDestruct "HP" as "#HP".
    iMod (na_inv_acc with "HP Hna")
      as "( (%ku & %a & %s & >%Heq & >%Hku_C & >%Hku & Halloc & Hfkeys) & Hna & HP_close)"
    ; eauto; simplify_eq; first solve_ndisj.

    (* geta rdst rdst; *)
    iInstr "Hcode".
    replace (finz.to_z (0 ^+ a)%a) with ku by solve_addr.

    (* lshiftl rdst rdst 16; *)
    iInstr "Hcode".
    (* lor rdst rdst rkey *)
    iInstr "Hcode".

    replace (Z.lor (ku ≪ 16) nkey) with (kvs_full_key ku nkey) by solve_addr.
    iMod ("HP_close" with "[$Hna $Halloc $Hfkeys]") as "Hna"; first eauto.
    replace (z_of a) with ku by solve_addr+Hku.
    iApply "Hpost"; iFrame "∗#".
    iPureIntro; split; auto.
  Qed.

End KVS_getFullKey.
