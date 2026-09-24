From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode register_tactics map_simpl call_stack.
From griotte Require Import heap_temporal_safety heap_temporal_safety_preamble.

Section Heap_Temporal_Safety_Blocks.
  Context {Σ : gFunctors} {ceriseg : ceriseG Σ} `{MP : MachineParameters}.

  (** Select the assembler blocks used by the local instruction proofs. *)
  Definition hts_assert_prep_instrs : list Word :=
    hts_main_instrs_n 20.
  Definition hts_store_private_instrs : list Word :=
    hts_main_instrs_n 11.
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

  (** This block is purely local: it assumes physical ownership of a live
      cell, rather than pretending that a tag check recovers that ownership. *)
  Lemma hts_store_private_spec pc_b pc_e pc_a p e b be (w w0 w1 w2 : Word) :
    disjoint_from_shadow b be ->
    (p + 1)%a = Some (p ^+ 1)%a ->
    (p < e /\ p ^+ 1 <= e /\ b < be)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_store_private_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ cgp ↦ᵣ WCap true RW Global p e p
    ∗ ca0 ↦ᵣ WCap true RW Global b be b
    ∗ ct0 ↦ᵣ w0 ∗ ct1 ↦ᵣ w1 ∗ ct2 ↦ᵣ w2
    ∗ b ↦ₐ w ∗ codefrag pc_a hts_store_private_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_store_private_instrs)%a
         ∗ cgp ↦ᵣ WCap true RW Global p e p
         ∗ ca0 ↦ᵣ WCap true RW Global b be b
         ∗ ct0 ↦ᵣ WCap true RW Global p (p ^+ 1)%a p
         ∗ ct1 ↦ᵣ WInt (p : Z) ∗ ct2 ↦ᵣ WInt (p + 1)%Z
         ∗ b ↦ₐ WCap true RW Global p (p ^+ 1)%a p
         ∗ codefrag pc_a hts_store_private_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hshadow Hp1 Hbounds Hsub)
      "(HPC & Hcgp & Hca0 & Hct0 & Hct1 & Hct2 & Hb & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_store_private_instrs.
    (* --- Mov ct0 cgp --- *)
    iInstr "Hcode".
    (* --- GetB ct1 ct0 --- *)
    iInstr "Hcode".
    (* --- Add ct2 ct1 1 --- *)
    iInstr "Hcode".
    (* --- Subseg ct0 ct1 ct2 --- *)
    iInstr "Hcode".
    (* --- Store ca0 ct0 0 --- *)
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
    ∗ ca0 ↦ᵣ WInt 0 ∗ ca1 ↦ᵣ WInt 0
    ∗ codefrag pc_a hts_free_result_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_free_result_instrs)%a
         ∗ ca0 ↦ᵣ WInt 0 ∗ ca1 ↦ᵣ WInt 0
         ∗ codefrag pc_a hts_free_result_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hca1 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_free_result_instrs.
    (* --- Jnz 2 ca0 (successful return value) --- *)
    iInstr "Hcode".
    (* --- Jmp 2 (skip Halt) --- *)
    iInstr "Hcode".
    (* --- Jnz 2 ca1 (successful allocator status) --- *)
    iInstr "Hcode".
    (* --- Jmp 2 (skip Halt) --- *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

  Lemma hts_free_result_failure_spec pc_b pc_e pc_a (result status : Z) :
    result ≠ 0 ∨ status ≠ 0 ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_free_result_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WInt result ∗ ca1 ↦ᵣ WInt status
    ∗ codefrag pc_a hts_free_result_instrs ∗ na_own cerise_nais ⊤
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hfailure Hsub) "(HPC & Hca0 & Hca1 & Hcode & Hna)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_free_result_instrs.
    destruct (decide (result = 0)) as [->|Hresult].
    - assert (status ≠ 0) by naive_solver.
      (* --- Jnz 2 ca0 (zero return value) --- *)
      iInstr "Hcode".
      (* --- Jmp 2 (skip first Halt) --- *)
      iInstr "Hcode".
      (* --- Jnz 2 ca1 (nonzero allocator status) --- *)
      iInstr "Hcode".
      (* --- Halt --- *)
      iInstr "Hcode".
      wp_end. by iIntros (?).
    - (* --- Jnz 2 ca0 (switcher failure) --- *)
      iInstr "Hcode".
      (* --- Halt --- *)
      iInstr "Hcode".
      wp_end. by iIntros (?).
  Qed.

  Lemma hts_malloc_result_success_spec pc_b pc_e pc_a b e a (w0 : Word) :
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_malloc_result_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ ca0 ↦ᵣ WCap true RW Global b e a
    ∗ ca1 ↦ᵣ WInt 0 ∗ ct0 ↦ᵣ w0
    ∗ codefrag pc_a hts_malloc_result_instrs
    ∗ ▷ (PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_malloc_result_instrs)%a
         ∗ ca0 ↦ᵣ WCap true RW Global b e a
         ∗ ca1 ↦ᵣ WInt 0 ∗ ct0 ↦ᵣ WInt 1
         ∗ codefrag pc_a hts_malloc_result_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub) "(HPC & Hca0 & Hca1 & Hct0 & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_malloc_result_instrs.
    (* --- Jnz 2 ca1 --- *)
    iInstr "Hcode".
    (* --- Jmp 2 --- *)
    iInstr "Hcode".
    (* --- GetWType ct0 ca0 --- *)
    iInstr "Hcode".
    (* --- Sub ct0 ct0 (encodeWordType wt_cap) --- *)
    iInstr "Hcode".
    assert (encodeWordType (WCap true RW Global b e a) = encodeWordType wt_cap)
      as Htype by solve_encodeWordType.
    iEval (rewrite Htype Z.sub_diag) in "Hct0".
    (* --- Jnz 2 ct0 --- *)
    iInstr "Hcode".
    (* --- Jmp 2 --- *)
    iInstr "Hcode".
    (* --- GetTag ct0 ca0 --- *)
    iInstr "Hcode".
    (* --- Jnz 2 ct0 --- *)
    iInstr "Hcode".
    iApply "Hpost". iFrame.
  Qed.

  (** The physical load can return either the saved capability or its untagged
      form. This deliberately does not recover heap ownership: that is the
      missing world transition after the unknown call. Failure is permitted
      by the enclosing safety WP if the shadow entry is unavailable. *)
  Lemma hts_reload_buffer_spec pc_b pc_e pc_a p e b (w0 : Word) :
    disjoint_from_shadow p e ->
    (p + 1)%a = Some (p ^+ 1)%a ->
    (p < p ^+ 1 /\ p ^+ 1 < e)%a ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ length hts_reload_buffer_instrs)%a ->
    PC ↦ᵣ WCap true RX Global pc_b pc_e pc_a
    ∗ cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ w0
    ∗ (p ^+ 1)%a ↦ₐ hts_buffer b ∗ codefrag pc_a hts_reload_buffer_instrs
    ∗ ▷ (∀ actual,
         ⌜load_heap (hts_buffer b) actual⌝ -∗
         PC ↦ᵣ WCap true RX Global pc_b pc_e (pc_a ^+ length hts_reload_buffer_instrs)%a
         ∗ cgp ↦ᵣ WCap true RW Global p e p ∗ ca0 ↦ᵣ actual
         ∗ (p ^+ 1)%a ↦ₐ hts_buffer b ∗ codefrag pc_a hts_reload_buffer_instrs
         -∗ WP Seq (Instr Executable)
             {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hshadow Hp1 Hbounds Hsub)
      "(HPC & Hcgp & Hca0 & Hsaved & Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /hts_reload_buffer_instrs.
    destruct (is_heap_address b) eqn:Hheap; cycle 1.
    { iEval (rewrite /hts_buffer) in "Hsaved".
      (* --- Load ca0 cgp 1 (nonheap base, unchanged tag) --- *)
      assert (is_heap_cap (hts_buffer b) = false) as Hnonheap.
      { rewrite /hts_buffer /is_heap_cap /heap_cap_base /memory_cap_base /= Hheap /=.
        reflexivity. }
      iInstr "Hcode".
      iApply ("Hpost" $! (hts_buffer b) with "[]"); last iFrame.
      iPureIntro. left. reflexivity. }
    (* --- Load ca0 cgp 1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iDestruct (map_of_regs_3 with "HPC Hcgp Hca0") as "[Hmap (%Hpc_cgp & %Hpc_ca0 & %Hcgp_ca0)]".
    iDestruct (memMap_resource_2ne_apply with "Hi Hsaved") as "[Hmem %Hpc_saved]".
    (* --- Load ca0 cgp 1: allow shadow-dependent tag clearing --- *)
    iApply (wp_load_memory_imm with "[$Hmap $Hmem]");
      eauto; try solve_pure; try (by simplify_map_eq).
    { rewrite decode_encode_instrW_inv. reflexivity. }
    { unfold regs_of. rewrite !dom_insert. set_solver+. }
    { exists true, RW, Global, p, e, p. split.
      - unfold read_reg_inr. by simplify_map_eq.
      - unfold reg_allows_load_imm. rewrite Hp1. case_decide; last done. exists (hts_buffer b). by simplify_map_eq. }
    { intros p0 g0 b0 e0 a0 ea (Hsrc & Hea & _).
      simpl_map_regs by eauto. simplify_map_eq.
      apply (disjoint_from_shadow_not_in _ _ _ Hshadow). apply withinBounds_true_iff. solve_addr. }
    iNext. iIntros (regs' retv) "(%Hspec & Hmem & Hmap)".
    destruct Hspec as [p0 g0 b0 e0 a0 ea raw actual Hallow Hlookup Hactual Hinc|].
    2: { wp_pure. wp_end. by iIntros (?). }
    destruct Hallow as (Hsrc & Hea & _).
    simpl_map_regs by eauto. simplify_map_eq.
    unfold incrementPC, incrementPC_gen in Hinc. simplify_map_eq.
    assert ((pc_a + 1)%a = Some (pc_a ^+ 1)%a) as Hpc by solve_addr.
    rewrite Hpc in Hinc. simplify_eq.
    rewrite (insert_insert_ne _ ca0 PC) // insert_insert_eq.
    rewrite (insert_insert_ne _ ca0 cgp) // insert_insert_eq.
    iDestruct (regs_of_map_3 with "Hmap") as "(HPC & Hcgp & Hca0)"; eauto.
    iDestruct (memMap_resource_2ne with "Hmem") as "[Hi Hsaved]"; auto.
    wp_pure.
    iSpecialize ("Hcode" with "Hi").
    iApply ("Hpost" $! actual with "[]"); last iFrame.
    iPureIntro. destruct Hactual as [-> | ->].
    - left. reflexivity.
    - right. split; last reflexivity.
      rewrite /hts_buffer /is_heap_cap /heap_cap_base /memory_cap_base /= Hheap /=.
      reflexivity.
  Qed.
End Heap_Temporal_Safety_Blocks.
