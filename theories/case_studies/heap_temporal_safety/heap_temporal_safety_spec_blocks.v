From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode register_tactics map_simpl call_stack.
From griotte Require Import heap_temporal_safety heap_temporal_safety_preamble.

Section Heap_Temporal_Safety_Blocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** Select the assembler blocks used by the local instruction proofs. *)
  Definition hts_assert_prep_instrs : list Word :=
    hts_main_instrs_n 20.
  Definition hts_check_buffer_instrs : list Word :=
    hts_main_instrs_n 10.
  Definition hts_free_result_instrs : list Word :=
    hts_main_instrs_n 15.
  Definition hts_malloc_result_instrs : list Word :=
    hts_main_instrs_n 4.
  Definition hts_reload_buffer_instrs : list Word :=
    hts_main_instrs_n 9.

  Lemma hts_assert_prep_spec pc_b pc_e pc_a p e (w0 w1 : Word) :
    disjoint_from_shadow p e ->
    (p < e)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_assert_prep_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ cgp ↦ᵣ WCap true RW Global p e p
    ∗ ct0 ↦ᵣ w0 ∗ ct1 ↦ᵣ w1
    ∗ p ↦ₐ WInt 0
    ∗ codefrag pc_a hts_assert_prep_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_assert_prep_instrs)%a
         ∗ cgp ↦ᵣ WCap true RW Global p e p
         ∗ ct0 ↦ᵣ WInt 0 ∗ ct1 ↦ᵣ WInt 0
         ∗ p ↦ₐ WInt 0 ∗ codefrag pc_a hts_assert_prep_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hshadow Hsize Hsub) "(HPC & Hcgp & Hct0 & Hct1 & Hp & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_assert_prep_instrs.
    (* --- Load ct0 cgp 0 --- *)
    iInstr "Hcode".
    (* --- Mov ct1 0 --- *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

  Lemma hts_check_live_buffer_spec pc_b pc_e pc_a b e a (w0 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_check_buffer_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WCap true RW Global b e a ∗ ct0 ↦ᵣ w0
    ∗ codefrag pc_a hts_check_buffer_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_check_buffer_instrs)%a
         ∗ ca0 ↦ᵣ WCap true RW Global b e a ∗ ct0 ↦ᵣ WInt 1
         ∗ codefrag pc_a hts_check_buffer_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hct0 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_check_buffer_instrs.
    (* --- GetTag ct0 ca0 --- *)
    iInstr "Hcode".
    (* --- Jnz 2 ct0 (skip Halt for a tagged buffer) --- *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

  Lemma hts_check_quarantined_buffer_spec pc_b pc_e pc_a b e a (w0 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_check_buffer_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WCap false RW Global b e a ∗ ct0 ↦ᵣ w0
    ∗ codefrag pc_a hts_check_buffer_instrs
    ∗ na_own cerise_nais ⊤
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hct0 & Hcode & Hna)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_check_buffer_instrs.
    (* --- GetTag ct0 ca0 --- *)
    iInstr "Hcode".
    (* --- Jnz 2 ct0 (fall through for an untagged buffer) --- *)
    iInstr "Hcode".
    (* --- Halt --- *)
    iInstr "Hcode".
    wp_end. by iIntros (?).
  Qed.

  Lemma hts_free_result_success_spec pc_b pc_e pc_a :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_free_result_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WInt 0
    ∗ codefrag pc_a hts_free_result_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_free_result_instrs)%a
         ∗ ca0 ↦ᵣ WInt 0
         ∗ codefrag pc_a hts_free_result_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_free_result_instrs.
    (* Jnz 2 ca0. *)
    iInstr "Hcode".
    (* Jmp 2. *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

  Lemma hts_free_result_failure_spec pc_b pc_e pc_a (result : Z) :
    result ≠ 0 ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_free_result_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WInt result
    ∗ codefrag pc_a hts_free_result_instrs ∗ na_own cerise_nais ⊤
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hresult Hsub) "(HPC & Hca0 & Hcode & Hna)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_free_result_instrs.
    (* Jnz 2 ca0. *)
    iInstr "Hcode".
    (* Halt. *)
    iInstr "Hcode".
    wp_end. by iIntros (?).
  Qed.

  Lemma hts_malloc_result_success_spec pc_b pc_e pc_a b e a (w0 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_malloc_result_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WCap true RW Global b e a
    ∗ ct0 ↦ᵣ w0
    ∗ codefrag pc_a hts_malloc_result_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_malloc_result_instrs)%a
         ∗ ca0 ↦ᵣ WCap true RW Global b e a
         ∗ ct0 ↦ᵣ WInt 1
         ∗ codefrag pc_a hts_malloc_result_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hct0 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_malloc_result_instrs.
    (* GetTag ct0 ca0. *)
    iInstr "Hcode".
    (* Jnz 2 ct0. *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.
End Heap_Temporal_Safety_Blocks.
