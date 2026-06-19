From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode map_simpl.
From griotte Require Import logrel rules.
From griotte Require Import region_invariants_revocation wp_rules_interp interp_weakening.
From griotte Require Import switcher_preamble switcher_spec_return.
From griotte Require Import switcher fetch_spec kvs kvs_preamble.

Section KVS_spec_initialise.
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

  Lemma KVS_initialise_spec_pre
    (pc_b pc_e pc_a : Addr)
    (cgp_b cgp_e : Addr)
    (wret : Word)
    (next_free_uk : Z)
    :

    (0 <= next_free_uk <= MAX_USER_KEY)%Z ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length kvs_initialise_instrs)%a ->

    (cgp_b + length_kvs_data)%a = Some cgp_e ->

    (
      (* initial register file *)
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      cgp ↦ᵣ WCap RW Global cgp_b cgp_e cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ - ∗
      ct0 ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      (* initial memory layout *)
      codefrag pc_a kvs_initialise_instrs ∗
      (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
      (cgp_b ^+ OFFSET_NEXT_FREE_SEALED_USER_KEY)%a ↦ₐ WInt next_free_uk ∗
      (cgp_b ^+ OFFSET_SCAP_USER_KEY)%a ↦ₐ kvs_user_seal_key_scap_init ∗

      ▷ ([∗ list] uk ∈ (seqZ_between next_free_uk MAX_USER_KEY), ◯(ALLOC)[uk] ∅) ∗

      ▷ (PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ca0 ↦ᵣ WInt (if ( next_free_uk <? MAX_USER_KEY)%Z then ASM_TRUE else ASM_FALSE) ∗
         (
           if ( next_free_uk <? MAX_USER_KEY)%Z
           then ca1 ↦ᵣ (kvs_user_seal_key Global next_free_uk)
           else ca1 ↦ᵣ WInt 0
         ) ∗ (* result of the initialise *)
         ct0 ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ctp ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗

         codefrag pc_a kvs_initialise_instrs ∗
         (pc_b ^+ UNSEALING_USER_KEY_OFFSET)%a ↦ₐ kvs_service_unsealing_key ∗
         (cgp_b ^+ OFFSET_NEXT_FREE_SEALED_USER_KEY)%a ↦ₐ
           WInt (if   (next_free_uk <? MAX_USER_KEY)%Z
                 then (next_free_uk + 1)%Z
                 else next_free_uk)
         ∗
         (cgp_b ^+ OFFSET_SCAP_USER_KEY)%a ↦ₐ kvs_user_seal_key_scap_init ∗

         (
           if ( next_free_uk <? MAX_USER_KEY)%Z
           then ( ([∗ list] uk ∈ (seqZ_between (next_free_uk +1) MAX_USER_KEY), ◯(ALLOC)[uk] ∅) ∗ ◯(ALLOC)[next_free_uk] ∅)
           else ([∗ list] uk ∈ (seqZ_between next_free_uk MAX_USER_KEY), ◯(ALLOC)[uk] ∅)
         )

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hnext_free_bounds HsubBounds Hcgp_contiguous)
      "(HPC & Hcgp & Hcra & [%wca0 Hca0] & [%wca1 Hca1] & [%wct0 Hct0] & [%wct1 Hct1] & [%wctp Hctp] & [%wcnull Hcnull] & Hcode
      & Ha_unsealing & Ha_next_free_uk & Ha_uk_scap & Hnext_free_alloc & Hpost)".
    rewrite /length_kvs_data /= in Hcgp_contiguous.
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* --------------------------------------------------- *)
    (* ----------------- Start the proof ----------------- *)
    (* --------------------------------------------------- *)
    rewrite /kvs_initialise_instrs /assembled_kvs_initialise.
    (* rewrite -/(fetch_instrs UNSEALING_USER_KEY_OFFSET ct0 ctp ct1). *)

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (fetch_spec with "[- $HPC $Hct0 $Hctp $Hct1 $Ha_unsealing $Hcode]"); eauto.
    { rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr. }
    iNext ; iIntros "(HPC & Hct0 & Hctp & Hct1 & Hcode & Ha_unsealing)".
    iEval (cbn) in "Hct0".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    focus_block 1 "Hcode" as a_initialise Ha_initialise "Hcode" "Hcont". iHide "Hcont" as hcont.
    (* lea cgp OFFSET_NEXT_FREE_SEALED_USER_KEY; *)
    iInstr "Hcode".
    { transitivity (Some (cgp_b ^+ OFFSET_NEXT_FREE_SEALED_USER_KEY)%a); auto; solve_addr. }
    (* load ct1 cgp; *)
    iInstr "Hcode".
    { split; auto; solve_addr. }
    iEval (cbn) in "Hct1".
    (* lt ctp ctp MemNum; (* ctp := if (ctp < MemNum) then 1 else 0 *) *)
    iInstr "Hcode".
    Transparent MemNum.
    replace 1999999%Z with MAX_USER_KEY.
    2: { rewrite /MAX_USER_KEY /MemNum; lia. }

    destruct ( (next_free_uk <? MAX_USER_KEY)%Z ) eqn:Hnext_free_uk; iEval (cbn) in "Hctp".
    - apply Z.ltb_lt in Hnext_free_uk.
      (* jnz (".initialise_next_free_available")%asm ctp; *)
      iInstr "Hcode".
      (* add ca0 ct1 1%Z; *)
      iInstr "Hcode".
      (* store cgp ca0; *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Store.wp_store_success_reg with "[$HPC $Hi $Hca0 $Hcgp $Ha_next_free_uk]")
      ; try solve_pure; auto.
      { solve_addr. }
      iNext; iIntros "(HPC & Hi & Hca0 & Hcgp & Ha_next_free_uk)".
      wp_pure.
      iInstr_close "Hcode".
      (* lea cgp 1; *)
      iInstr "Hcode".
      { transitivity (Some ( (cgp_b ^+ OFFSET_SCAP_USER_KEY)%a )); auto; solve_addr. }
      (* load ctp cgp; *)
      iInstr "Hcode".
      { split; auto; solve_addr. }
      iEval (cbn) in "Hctp".
      (* lea ctp ct1; *)
      iInstr "Hcode".
      { transitivity ( Some ( (0 ^+ next_free_uk)%a ) ); auto.
        rewrite addr_incr_zero_nat.
        apply finz_incr_Some_prove_spec; split; [|split]; try solve_addr.
        - replace (z_of 0%a) with 0%Z by solve_addr.
          rewrite /MAX_USER_KEY /MemNum in Hnext_free_uk.
          rewrite /MemNum.
          lia.
        - replace (z_of 0%a) with 0%Z by solve_addr.
          rewrite /finz.incr_default /finz.incr.
          destruct ( Z.lt_dec (0%a + next_free_uk)%Z MemNum ); try solve_addr.
          { destruct (Z.le_dec 0%Z (0%a + next_free_uk)%Z); first done.
            exfalso; apply n.
            replace (z_of 0%a) with 0%Z by solve_addr.
            lia.
          }
          exfalso; apply n.
          replace (z_of 0%a) with 0%Z by solve_addr.
          rewrite /MAX_USER_KEY /MemNum in Hnext_free_uk.
          rewrite /MemNum.
          lia.
      }
      (* seal ca1 ct0 ctp; *)
      iInstr "Hcode"; auto.
      { pose proof KVS_OTYPE_size; solve_addr. }
      (* mov ca0 ASM_TRUE; *)
      iInstr "Hcode".
      (* ret *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iApply "Hpost".
      iFrame "HPC Hcgp Hcra Hca0 Hca1 Hct1 Hct0 Hctp Hcnull Hcode Ha_unsealing Ha_next_free_uk Ha_uk_scap".
      rewrite seqZ_between_cons.
      { iDestruct "Hnext_free_alloc" as "[$ $]". }
      lia.

    - apply Z.ltb_ge in Hnext_free_uk.
      (* jnz (".initialise_next_free_available")%asm ctp; *)
      iInstr "Hcode".
      (* mov ca0 ASM_FALSE; *)
      iInstr "Hcode".
      (* mov ca1 0; *)
      iInstr "Hcode".
      (* ret; *)
      iInstr "Hcode".
      subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

      iApply "Hpost".
      iFrame "HPC Hcgp Hcra Hca0 Hca1 Hct1 Hct0 Hctp Hcnull Hcode Ha_unsealing Ha_next_free_uk Hnext_free_alloc Ha_uk_scap".
  Qed.

  Lemma KVS_initialise_spec
    (wret : Word)
    (E : coPset)
    :

    ↑Nkvs ⊆ E ->

    ( na_inv cerise_nais Nkvs kvs_inv ∗
      na_own cerise_nais E ∗

      (* initial register file *)
      PC ↦ᵣ WCap RX Global KVS_pcc_b KVS_pcc_e kvs_initialise_pcc_addr ∗
      cgp ↦ᵣ WCap RW Global KVS_cgp_b KVS_cgp_e KVS_cgp_b ∗
      cra ↦ᵣ wret ∗
      ca0 ↦ᵣ - ∗
      ca1 ↦ᵣ - ∗
      ct0 ↦ᵣ - ∗ (* scratch *)
      ct1 ↦ᵣ - ∗ (* scratch *)
      ctp ↦ᵣ - ∗ (* scratch *)
      cnull ↦ᵣ - ∗

      ▷ (na_own cerise_nais E ∗
         PC ↦ᵣ updatePcPerm wret ∗
         cgp ↦ᵣ - ∗
         cra ↦ᵣ - ∗
         ct0 ↦ᵣ - ∗ (* scratch *)
         ct1 ↦ᵣ - ∗ (* scratch *)
         ctp ↦ᵣ - ∗ (* scratch *)
         cnull ↦ᵣ - ∗
         (
           ( ∃ next_free_uk,
               ⌜ (0 <= next_free_uk < MAX_USER_KEY)%Z ⌝ ∗
               ca0 ↦ᵣ WInt ASM_TRUE ∗
               ca1 ↦ᵣ (kvs_user_seal_key Global next_free_uk) ∗
               ◯(ALLOC)[next_free_uk] ∅
           )
           ∨
             (
               ca0 ↦ᵣ WInt ASM_FALSE ∗
               ca1 ↦ᵣ -
             )
         )

         -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
      ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    iIntros (Hnkvs_E)
      "(#Hkvs_inv & Hna & HPC & Hcgp & Hcra & Hca0 & Hca1 & Hct0 & Hct1 & Hctp & Hcnull & Hpost)".
    iMod (na_inv_acc with "Hkvs_inv Hna")
      as "( (%m & %s & %next_free_uk & >Himports & >Ha_next_uk & >Ha_uk_scap & >Hcode
            & HisKVS & >%Hwf_free_uk & Hfree_uk_alloc & #Hspred)
            & Hna & Hkvs_inv_close)"; eauto.
    pose proof (Hcgp_continuous := KVS_size_data).
    pose proof (HKVS_pcc_b' := KVS_size_imports).
    pose proof (Hcode_continuous := KVS_size_code).
    assert (SubBounds KVS_pcc_b KVS_pcc_e kvs_initialise_pcc_addr (kvs_initialise_pcc_addr ^+ length kvs_initialise_instrs)%a) as HSubBounds.
    { rewrite /kvs_initialise_pcc_addr; cbn in *; solve_addr. }
    codefrag_facts "Hcode"; rename H into Hpc_contiguous.
    rewrite /kvs_imports /kvs.kvs_imports_pre.
    assert ((KVS_pcc_b + 1)%a = Some (KVS_pcc_b ^+ 1)%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1)%a <= KVS_pcc_b')%a  by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    assert ((KVS_pcc_b ^+ 1 + 1)%a = Some (KVS_pcc_b')%a) by ( rewrite /length_kvs_imports in HKVS_pcc_b'; solve_addr+ HKVS_pcc_b').
    iDestruct (region_pointsto_cons with "Himports") as "[Himports_sw Himports]"; eauto.
    iDestruct (region_pointsto_single with "Himports") as "(% & Ha_unsealing & %Heq)"; eauto; simplify_eq.

    rewrite /kvs_service_instrs.
    focus_block_nochangePC 3 "Hcode" as a_initialise Ha_initialise "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a_initialise = kvs_initialise_pcc_addr) as -> by (rewrite /kvs_initialise_pcc_addr ; cbn in * ; solve_addr+Hcode_continuous HKVS_pcc_b' Ha_initialise).
    replace (KVS_pcc_b ^+ 1)%a with (KVS_pcc_b ^+ UNSEALING_USER_KEY_OFFSET)%a by (rewrite /UNSEALING_USER_KEY_OFFSET; solve_addr+).
    iApply (KVS_initialise_spec_pre with "[- $HPC]"); last iFrame; eauto.
    iNext; iIntros "(HPC & Hcgp & Hcra & Hca0 & Hca1 & Hctp & Hct0 & Hct1
              & Hcnull & Hcode & Ha_unsealing & Ha_next_uk & Ha_uk_scap & Hfree_uk_alloc)".
    subst hcont; unfocus_block "Hcode" "Hcont" as "Hcode".

    destruct ( (next_free_uk <? MAX_USER_KEY)%Z ) eqn:Hfree.
    - iDestruct "Hfree_uk_alloc" as "[Hfree_uk_alloc Halloc]".
      assert (0 <= next_free_uk + 1 <= MAX_USER_KEY )%Z by (apply Z.ltb_lt in Hfree; lia).
      iMod ("Hkvs_inv_close" with "[$Hcode $Ha_next_uk $Ha_uk_scap Himports_sw Ha_unsealing $HisKVS $Hfree_uk_alloc $Hspred $Hna]") as "Hna" ; auto.
      { iNext.
        iSplit; last done.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }
      iApply "Hpost"; iFrame.
      iLeft; iFrame.
      iPureIntro; auto.
      apply Z.ltb_lt in Hfree.
      lia.
    - iMod ("Hkvs_inv_close" with "[$Hcode $Ha_next_uk $Ha_uk_scap Himports_sw Ha_unsealing $HisKVS $Hfree_uk_alloc $Hspred $Hna]") as "Hna" ; auto.
      { iNext.
        iSplit; last done.
        iApply (region_pointsto_cons with "[Ha_unsealing Himports_sw]"); eauto; iFrame.
        iApply (region_pointsto_cons with "[Ha_unsealing]"); eauto; [solve_addr+|]; iFrame.
        rewrite /region_pointsto finz_seq_between_empty; auto; solve_addr+.
      }
      iApply "Hpost"; iFrame.
      iRight; iFrame.
  Qed.

End KVS_spec_initialise.
