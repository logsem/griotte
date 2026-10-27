From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.
From griotte Require Export kvs_preamble.

Section KVS_check_uint16.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Definition word_is_uint16 (w : Word) : Prop :=
    match w with
    | WInt z => is_uint16 z
    | _ => False
    end.

  #[global] Instance word_is_uint16_dec (w : Word ) : Decision (word_is_uint16 w).
  Proof. destruct w; solve_decision. Qed.

  Lemma KVS_check_uint16_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (wrv : LWord)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ₚ[th] WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ[th] wrv ∗
      rdst ↦ᵣ[th] - ∗
      codefrag_pers pc_a instrs ∗

      ▷ (
          PC ↦ₚ[th] WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ[th] wrv ∗
          codefrag_pers pc_a instrs ∗
          (
            ( rdst ↦ᵣ[th] WInt ASM_TRUE ∗ ⌜ word_is_uint16 wrv.(lw) ⌝ )
            ∨
              ( rdst ↦ᵣ[th] WInt ASM_FALSE ∗ ⌜ ¬ word_is_uint16 wrv.(lw) ⌝ )
          )
          -∗
            WP Seq (Instr Executable) @[th] {{ HO th }}
        )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hrv Hrdst)
      "(HPC & Hrv & [%wdst Hrdst] & #Hcode & Hpost)".
    codefrag_facts "Hcode"; rename H into Hpc_contiguous ; clear H0.

    (* GetWType rdst rv. *)
    iInstr "Hcode".
    (* Sub rdst rdst (encodeWordType wt_int). *)
    iInstr "Hcode".
    destruct wrv as [wv πv].
    destruct (is_z wv) eqn:His_z_wrv; cycle 1.
    { (* Not an integer *)
      assert (nonZero (WInt (encodeWordType wv - encodeWordType (WInt 0))) = true) as Hnz.
      { apply negb_true_iff, Z.eqb_neq. cbn. intros Hzero.
        pose proof (encodeWordType_correct wv (WInt 0)) as Hencode.
        assert (encodeWordType wv = encodeWordType (WInt 0)) as Heq by lia.
        destruct wv as [| [] | | ]; cbn in His_z_wrv, Hencode; done. }
      (* Jne .kvs_key_check_uint16_not_int rdst 0. *)
      iInstr "Hcode".
      (* Mov rdst ASM_FALSE. *)
      iInstr "Hcode".
      (* Jmp .kvs_key_ret. *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
      iRight; iFrame.
      iPureIntro. destruct wv; cbn in *; [done | tauto ..]. }
    destruct wv as [nkey | | | ]; try done.
    rewrite (encodeWordType_correct_int nkey 0) Z.sub_diag.
    (* Jne .kvs_key_check_uint16_not_int rdst 0. *)
    iInstr "Hcode".
    (* Lt rdst (UINT16_MIN-1)%Z rv. *)
    iInstr "Hcode".

    destruct (decide ( UINT16_MIN <= nkey )%Z) as [Hnkey_pass_min_uint16 | Hnkey_fail_min_uint16] ; cycle 1.
    { replace (-1 <? nkey)%Z with false by (rewrite /UINT16_MIN in Hnkey_fail_min_uint16; lia).
      iEval (cbn) in "Hrdst".
      (* jnez (".kvs_key_check_uint16_min")%asm rdst; *)
      iInstr "Hcode".
      (* mov rdst ASM_FALSE; *)
      iInstr "Hcode".
      (* jmp (".kvs_key_ret")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
      iRight; iFrame.
      iPureIntro; rewrite /word_is_uint16 /is_uint16; lia.
    }
    replace (-1 <? nkey)%Z with true by (rewrite /UINT16_MIN in Hnkey_pass_min_uint16; lia).
    iEval (cbn) in "Hrdst".
    (* jnez (".kvs_key_check_uint16_min")%asm rdst; *)
    iInstr "Hcode".
    (* lt rdst rv UINT16_MAX; *)
    iInstr "Hcode".

    destruct (decide (nkey < UINT16_MAX )%Z) as [Hnkey_pass_max_uint16 | Hnkey_fail_max_uint16] ; cycle 1.
    { replace (nkey <? 65536)%Z with false by (rewrite /UINT16_MAX in Hnkey_fail_max_uint16; lia).
      iEval (cbn) in "Hrdst".
      (* jnez (".kvs_key_check_uint16_max")%asm rdst; *)
      iInstr "Hcode".
      (* mov rdst ASM_FALSE; *)
      iInstr "Hcode".
      (* jmp (".kvs_key_ret")%asm; *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
      iRight; iFrame.
      iPureIntro; rewrite /word_is_uint16 /is_uint16; lia.
    }
    replace (nkey <? 65536)%Z with true by (rewrite /UINT16_MAX in Hnkey_pass_max_uint16; lia).
    iEval (cbn) in "Hrdst".
    (* jnez (".kvs_key_check_uint16_min")%asm rdst; *)
    iInstr "Hcode".
    (* mov rdst ASM_TRUE; *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame "∗ Hcode".
    iLeft; iFrame.
    iPureIntro; rewrite /word_is_uint16 /is_uint16; lia.
  Qed.

  Lemma KVS_check_uint16_spec_is_uint16 `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (nkey : Z) (πnkey : option AId)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    is_uint16 nkey ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ₚ[th] WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ[th] WInt nkey @@? πnkey ∗
      rdst ↦ᵣ[th] - ∗
      codefrag_pers pc_a instrs ∗

      ▷ (
          PC ↦ₚ[th] WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ[th] WInt nkey @@? πnkey ∗
          codefrag_pers pc_a instrs ∗
          rdst ↦ᵣ[th] WInt ASM_TRUE
          -∗
          WP Seq (Instr Executable) @[th] {{ HO th }}
        )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hnkey Hrv Hrdst) "(HPC & Hrv & Hrdst & #Hcode & Hpost)".
    iApply (KVS_check_uint16_spec with "[- $HPC $Hrv $Hrdst $Hcode]"); eauto.
    iNext; iIntros "(HPC & Hrv & _ & [ (Hrdst & %Hnkey') | (Hrdst & %Hnkey')] )".
    - iApply "Hpost"; iFrame "∗ Hcode".
    - done.
  Qed.

  Lemma KVS_check_uint16_spec_not_uint16 `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (wrv : LWord)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->
    ¬ word_is_uint16 wrv.(lw) ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ₚ[th] WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ[th] wrv ∗
      rdst ↦ᵣ[th] - ∗
      codefrag_pers pc_a instrs ∗

      ▷ (
          PC ↦ₚ[th] WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ[th] wrv ∗
          codefrag_pers pc_a instrs ∗
          rdst ↦ᵣ[th] WInt ASM_FALSE
          -∗
          WP Seq (Instr Executable) @[th] {{ HO th }}
        )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hnkey Hrv Hrdst) "(HPC & Hrv & Hrdst & #Hcode & Hpost)".
    iApply (KVS_check_uint16_spec with "[- $HPC $Hrv $Hrdst $Hcode]"); eauto.
    iNext; iIntros "(HPC & Hrv & _ & [ (Hrdst & %Hnkey') | (Hrdst & %Hnkey')] )".
    - done.
    - iApply "Hpost"; iFrame "∗ Hcode".
  Qed.

End KVS_check_uint16.
