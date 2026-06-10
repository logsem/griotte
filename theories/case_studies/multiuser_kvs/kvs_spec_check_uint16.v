From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel rules.
From cap_machine Require Import switcher kvs.
From cap_machine Require Import proofmode.
From cap_machine Require Export kvs_preamble.

Section KVS_check_uint16.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Lemma KVS_check_uint16_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (wrv : Word)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ wrv ∗
      rdst ↦ᵣ - ∗
      codefrag pc_a instrs ∗

      ▷ (
          ∀ nkey,
            ⌜ wrv = WInt nkey ⌝ ∗
            PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
            rv ↦ᵣ wrv ∗
            codefrag pc_a instrs ∗
            (
              ( rdst ↦ᵣ WInt ASM_TRUE ∗ ⌜ is_uint16 nkey ⌝ )
              ∨
                ( rdst ↦ᵣ WInt ASM_FALSE ∗ ⌜ ¬ (is_uint16 nkey) ⌝ )
            )
            -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hrv Hrdst)
      "(HPC & Hrv & [%wdst Hrdst] & Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* lt rdst (UINT16_MIN-1)%Z rv; *)
    destruct (is_z wrv) eqn:His_z_wrv; cycle 1.
    { iInstr "Hcode"; wp_end; iIntros (?); done. }
    destruct wrv as [ nkey | | | ]; try done.
    iInstr "Hcode".

    destruct (decide ( UINT16_MIN <= nkey )%Z) as [Hnkey_pass_min_uint16 | Hnkey_fail_min_uint16] ; cycle 1.
    { replace (-1 <? nkey)%Z with false by (rewrite /UINT16_MIN in Hnkey_fail_min_uint16; lia).
      iEval (cbn) in "Hrdst".
      (* jnz (".kvs_key_check_uint16_min")%asm rdst; *)
      iInstr "Hcode".
      (* mov rdst ASM_FALSE; *)
      iInstr "Hcode".
      rewrite decide_False //.
      (* jmp (".kvs_key_ret")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame.
      iSplit; eauto.
      iRight; iFrame.
      iPureIntro; rewrite /is_uint16; lia.
    }
    replace (-1 <? nkey)%Z with true by (rewrite /UINT16_MIN in Hnkey_pass_min_uint16; lia).
    iEval (cbn) in "Hrdst".
    (* jnz (".kvs_key_check_uint16_min")%asm rdst; *)
    iInstr "Hcode".
    (* lt rdst rv UINT16_MAX; *)
    iInstr "Hcode".

    destruct (decide (nkey < UINT16_MAX )%Z) as [Hnkey_pass_max_uint16 | Hnkey_fail_max_uint16] ; cycle 1.
    { replace (nkey <? 65536)%Z with false by (rewrite /UINT16_MAX in Hnkey_fail_max_uint16; lia).
      iEval (cbn) in "Hrdst".
      (* jnz (".kvs_key_check_uint16_max")%asm rdst; *)
      iInstr "Hcode".
      (* mov rdst ASM_FALSE; *)
      iInstr "Hcode".
      rewrite decide_False //.
      (* jmp (".kvs_key_ret")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame.
      iSplit; eauto.
      iRight; iFrame.
      iPureIntro; rewrite /is_uint16; lia.
    }
    replace (nkey <? 65536)%Z with true by (rewrite /UINT16_MAX in Hnkey_pass_max_uint16; lia).
    iEval (cbn) in "Hrdst".
    (* jnz (".kvs_key_check_uint16_min")%asm rdst; *)
    iInstr "Hcode".
    (* mov rdst ASM_TRUE; *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame.
    iSplit; eauto.
  Qed.

  Lemma KVS_check_uint16_spec_known `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (nkey : Z)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    is_uint16 nkey ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ WInt nkey ∗
      rdst ↦ᵣ - ∗
      codefrag pc_a instrs ∗

      ▷ (
          PC ↦ᵣ WCap RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ WInt nkey ∗
          codefrag pc_a instrs ∗
          rdst ↦ᵣ WInt ASM_TRUE
          -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hnkey Hrv Hrdst) "(HPC & Hrv & Hrdst & Hcode & Hpost)".
    iApply (KVS_check_uint16_spec with "[- $HPC $Hrv $Hrdst $Hcode]"); eauto.
    iNext; iIntros (nkey') "(%Hnkey_eq & HPC & Hrv & Hcode & [ (Hrdst & %Hnkey') | (Hrdst & %Hnkey')] )"; simplify_eq.
    iApply "Hpost"; iFrame.
  Qed.

End KVS_check_uint16.
