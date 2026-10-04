From iris.proofmode Require Import proofmode.
From griotte Require Import proofmode.
From griotte Require Import logrel rules.
From griotte Require Import switcher kvs.
From griotte Require Export kvs_preamble.

Section KVS_check_uint16.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {kvsg:kvsG Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  (* TODO: move to rules_BinOp *)
  (** [wp_binop_success_r_z] for an integer register with any identifier. *)
  Lemma wp_binop_success_r_z_prov E dst pc_p pc_g pc_b pc_e pc_a pc_π w wdst ins r1 n1 π1 n2
      pc_a' :
    decodeInstrW w.(lw) = ins →
    is_BinOp ins dst (inr r1) (inl n2) →
    (pc_a + 1)%a = Some pc_a' →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) ->
    dst ≠ cnull ->
    r1 ≠ cnull ->
    {{{ PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ pc_a ↦ₐ w
        ∗ r1 ↦ᵣ WInt n1 @@? π1
        ∗ dst ↦ᵣ wdst
    }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ᵣ WCap true pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ w
          ∗ r1 ↦ᵣ WInt n1 @@? π1
          ∗ dst ↦ᵣ WInt (denote ins n1 n2)
      }}}.
  Proof.
    iIntros (Hdecode Hinstr Hpc_a Hvpc Hcnull Hcnull' ϕ) "(HPC & Hpc_a & Hr1 & Hdst) Hφ".
    iDestruct (map_of_regs_3 with "HPC Hr1 Hdst") as "[Hmap (%&%&%)]".
    iApply (wp_BinOp with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    { by erewrite regs_of_is_BinOp; eauto; rewrite !dom_insert; set_solver+. }
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.
    destruct Hspec as [| * Hfail].
    { iApply "Hφ". iFrame. incrementPC_inv; simplify_map_eq.
      rewrite (insert_insert_ne _ PC dst) // insert_insert_eq (insert_insert_ne _ r1 dst) //
              (insert_insert_ne _ dst PC) // insert_insert_eq.
      iDestruct (regs_of_map_3 with "Hmap") as "(?&?&?)"; eauto; iFrame. }
    { destruct Hfail; try incrementPC_inv; simplify_map_eq; eauto. congruence. }
  Qed.

  Lemma KVS_check_uint16_spec `{KVS : kvsLayout}
    (pc_b pc_e pc_a : Addr)
    (rv rdst : RegName) (wrv : LWord)
    :
    let instrs := (kvs_check_uint16_instrs rv rdst) in
    SubBounds pc_b pc_e pc_a (pc_a ^+ length instrs)%a ->

    rv ≠ cnull ->
    rdst ≠ cnull ->

    (
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ wrv ∗
      rdst ↦ᵣ - ∗
      codefrag pc_a instrs ∗

      ▷ (
          ∀ nkey,
            ⌜ wrv.(lw) = WInt nkey ⌝ ∗
            PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
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
    destruct (is_z wrv.(lw)) eqn:His_z_wrv; cycle 1.
    { iInstr "Hcode"; wp_end; iIntros (?); done. }
    destruct wrv as [ [ nkey | | | ] π]; try done.
    (* lt rdst (UINT16_MIN-1)%Z rv; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_binop_success_z_r_prov with "[$HPC $Hi $Hrv $Hrdst]"); try solve_pure.
    iIntros "!> (HPC & Hi & Hrv & Hrdst)". wp_pure.
    iSpecialize ("Hcode" with "Hi"). cbn [denote].

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
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_binop_success_r_z_prov with "[$HPC $Hi $Hrv $Hrdst]"); try solve_pure.
    iIntros "!> (HPC & Hi & Hrv & Hrdst)". wp_pure.
    iSpecialize ("Hcode" with "Hi"). cbn [denote].

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
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ WInt nkey @@? πnkey ∗
      rdst ↦ᵣ - ∗
      codefrag pc_a instrs ∗

      ▷ (
          PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ WInt nkey @@? πnkey ∗
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
    iNext; iIntros (nkey') "(%Hnkey_eq & HPC & Hrv & Hcode & [ (Hrdst & %Hnkey') | (Hrdst & %Hnkey')] )"; cbn in Hnkey_eq; simplify_eq.
    iApply "Hpost"; iFrame.
  Qed.

  Definition word_is_uint16 (w : Word) : Prop :=
    match w with
    | WInt z => is_uint16 z
    | _ => False
    end.

  Global Instance word_is_uint16_dec (w : Word ) : Decision (word_is_uint16 w).
  Proof. destruct w; solve_decision. Qed.

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
      PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a ∗
      rv ↦ᵣ wrv ∗
      rdst ↦ᵣ - ∗
      codefrag pc_a instrs ∗

      ▷ (
          PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length instrs)%a ∗
          rv ↦ᵣ wrv ∗
          codefrag pc_a instrs ∗
          rdst ↦ᵣ WInt ASM_FALSE
          -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
        )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})%I.
  Proof.
    intros instrs ; subst instrs.
    iIntros (HsubBounds Hnkey Hrv Hrdst) "(HPC & Hrv & Hrdst & Hcode & Hpost)".
    iApply (KVS_check_uint16_spec with "[- $HPC $Hrv $Hrdst $Hcode]"); eauto.
    iNext; iIntros (nkey') "(%Hnkey_eq & HPC & Hrv & Hcode & [ (Hrdst & %Hnkey') | (Hrdst & %Hnkey')] )"; rewrite Hnkey_eq in Hnkey; simplify_eq.
    iApply "Hpost"; iFrame.
  Qed.

End KVS_check_uint16.
