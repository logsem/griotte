From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export copy_context.

(** * Specification of [copy_context_asm]

    The copy of CHERIoT's [copyContext]: the source is a region of memory
    owned by the caller; the destination is generic: each store goes
    through a per-cell accessor [cells_store_acc], so that the destination
    may be owned by the caller or opened from an invariant. *)

Section CopyContextMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

  (** The stores of [ws] to the cells from [a], through a capability of
      permission [p] and identifier [π]. [D i] holds once the first [i]
      cells are written. Each store gets cell [i], outside the shadow
      table, with the liveness of [π], and gives it back with the stored
      word. *)
  Definition cells_store_acc (D : nat → iProp Σ) (p : Perm) (a : Addr)
    (π : option AId) (ws : list LWord) : iProp Σ :=
    □ ∀ i : nat,
      ⌜(i < length ws)%nat⌝ -∗
      D i
      ={⊤}=∗
      ∃ (v : LWord) (q : Qp),
        ⌜is_shadow_address (a ^+ i)%a = false⌝ ∗
        (a ^+ i)%a ↦ₐ v ∗
        deref_res π q ∗
        ▷ ((a ^+ i)%a ↦ₐ lstore_word p (ws !!! i) -∗
           deref_res π q
           ={⊤}=∗
           D (S i)).

  #[global] Instance cells_store_acc_persistent D p a π ws :
    Persistent (cells_store_acc D p a π ws).
  Proof. apply _. Qed.

  (** The stores of [w :: ws] from [a], without the first: those of [ws]
      from [a ^+ 1]. *)
  Lemma cells_store_acc_tail (D : nat → iProp Σ) (p : Perm) (a : Addr)
    (π : option AId) (w : LWord) (ws : list LWord) :
    is_Some (a + length (w :: ws))%a →
    cells_store_acc D p a π (w :: ws) -∗
    cells_store_acc (λ i, D (S i)) p (a ^+ 1)%a π ws.
  Proof.
    iIntros ([a_end Ha_end]) "#Hacc". iIntros "!>" (i Hi) "HD".
    cbn in Ha_end.
    rewrite (_ : ((a ^+ 1) ^+ i)%a = (a ^+ S i)%a); last solve_addr.
    iApply ("Hacc" $! (S i) with "[] HD"). iPureIntro; cbn; lia.
  Qed.

  (** One word per iteration, from [copy_loop] with [i] words copied. *)
  #[local] Lemma copy_context_loop_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr) (π_d : option AId)
    (ws : list LWord) (D : nat → iProp Σ) (i : nat) (wscratch : LWord) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a →
    length ws = 15%nat →
    (i < 15)%nat →
    readAllowed p_s = true →
    isDL p_s = false →
    isDRO p_s = false →
    (b_s <= a_s)%a →
    (a_s + 15 <= e_s)%Z →
    disjoint_from_shadow a_s (a_s ^+ 15)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ WCap true p_s g_s b_s e_s (a_s ^+ i)%a ∗
    dst ↦ᵣ (WCap true p_d g_d b_d e_d (a_d ^+ i)%a @@? π_d) ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ WInt (15 - i) ∗
    ([∗ list] k ↦ w ∈ ws, (a_s ^+ k)%a ↦ₐ w) ∗
    D i ∗
    cells_store_acc D p_d a_d π_d ws ∗
    ▷ ( (∃ wscratch' : LWord,
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
                   (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a ∗
           src ↦ᵣ WCap true p_s g_s b_s e_s (a_s ^+ 15)%a ∗
           dst ↦ᵣ (WCap true p_d g_d b_d e_d (a_d ^+ 15)%a @@? π_d) ∗
           scratch ↦ᵣ wscratch' ∗
           counter ↦ᵣ WInt 0 ∗
           ([∗ list] k ↦ w ∈ ws, (a_s ^+ k)%a ↦ₐ w) ∗
           D 15)
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen Hi Hread Hdl Hdro Hb_s He_s Hshadow_s Hwrite Hb_d He_d
               Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hws & HD & #Hacc & Hpost)".
    assert (dst ≠ cnull ∧ src ≠ cnull ∧ scratch ≠ cnull ∧ counter ≠ cnull)
      as (Hdst_null & Hsrc_null & Hscratch_null & Hcounter_null)
      by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    iLöb as "IH" forall (i wscratch Hi).
    destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
    iDestruct (big_sepL_lookup_acc _ _ i with "Hws") as "[Hwi Hws]"; first exact Hwi.
    (* CLoad scratch src 0 *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ scratch src 0)
      with "[$HPC $Hscratch $Hsrc $Hwi]" as "(HPC & Hscratch & Hsrc & Hwi)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; [exact Hshadow_s | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    rewrite lload_word_no_dl_dro //.
    iMod ("Hacc" $! i with "[] HD") as (v q) "(%Hsh_d & Hcell & Hderef & Hclose)".
    { iPureIntro; lia. }
    (* Store dst scratch 0 *)
    iInstrApply "Hcode"
      (wp_store_success_reg_store_word_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0)
      with "[$HPC $Hscratch $Hdst $Hcell $Hderef]"
      as "(HPC & Hscratch & Hdst & Hcell & Hderef)".
    { rewrite /withinBounds; solve_addr. }
    { solve_addr. }
    rewrite -(list_lookup_total_correct _ _ _ Hwi).
    iMod ("Hclose" with "Hcell Hderef") as "HD".
    iDestruct ("Hws" with "Hwi") as "Hws".
    (* Add counter counter (-1) *)
    iInstr "Hcode".
    (* Lea dst 1 *)
    iInstr "Hcode".
    { transitivity (Some (a_d ^+ S i)%a); solve_addr. }
    (* Lea src 1 *)
    iInstr "Hcode".
    { transitivity (Some (a_s ^+ S i)%a); solve_addr. }
    destruct (decide (i = 14)) as [-> | Hi14].
    - (* Jnz -5 counter *)
      iInstr "Hcode".
      iApply "Hpost". iExists (ws !!! 14). iFrame.
    - (* Jnz -5 counter *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      { transitivity (Some (pc_a ^+ 1)%a); solve_addr. }
      replace (15 - i + -1)%Z with (15 - S i)%Z by lia.
      iApply ("IH" $! (S i) with "[] HPC Hsrc Hdst Hscratch Hcounter Hws HD Hpost").
      iPureIntro; lia.
  Qed.

  (** [copy_context_asm dst src scratch counter] copies the 15 words [ws]
      of the region at [a_s] to the cells from [a_d], through the
      accessor of the destination. *)
  Lemma copy_context_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr) (π_d : option AId)
    (ws : list LWord) (wscratch wcounter : LWord) (D : nat → iProp Σ) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a →
    length ws = 15%nat →
    readAllowed p_s = true →
    isDL p_s = false →
    isDRO p_s = false →
    (b_s <= a_s)%a →
    (a_s + 15 <= e_s)%Z →
    disjoint_from_shadow a_s (a_s ^+ 15)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ WCap true p_s g_s b_s e_s a_s ∗
    dst ↦ᵣ (WCap true p_d g_d b_d e_d a_d @@? π_d) ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ wcounter ∗
    [[ a_s , (a_s ^+ 15)%a ]] ↦ₐ [[ ws ]] ∗
    D 0 ∗
    cells_store_acc D p_d a_d π_d ws ∗
    ▷ ( (∃ wscratch' : LWord,
           PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
                   (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a ∗
           src ↦ᵣ WCap true p_s g_s b_s e_s (a_s ^+ 15)%a ∗
           dst ↦ᵣ (WCap true p_d g_d b_d e_d (a_d ^+ 15)%a @@? π_d) ∗
           scratch ↦ᵣ wscratch' ∗
           counter ↦ᵣ WInt 0 ∗
           [[ a_s , (a_s ^+ 15)%a ]] ↦ₐ [[ ws ]] ∗
           D 15)
        -∗ WP Seq (Instr Executable) {{ φ }})
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen Hread Hdl Hdro Hb_s He_s Hshadow_s Hwrite Hb_d He_d Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hws & HD & #Hacc & Hpost)".
    assert (counter ≠ cnull) as Hcounter_null by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    (* Mov counter 15 *)
    iInstr "Hcode".
    rewrite decide_False //.
    iEval (rewrite (region_pointsto_cells a_s); last (rewrite Hlen; solve_addr)) in "Hws".
    assert ((a_s ^+ 0%nat)%a = a_s) as Ha_s0 by solve_addr.
    assert ((a_d ^+ 0%nat)%a = a_d) as Ha_d0 by solve_addr.
    iApply (copy_context_loop_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D 0
             with "[$HPC $Hcode $Hscratch $Hcounter $Hws $HD $Hacc Hsrc Hdst Hpost]").
    all: try (lia || done).
    rewrite Ha_s0 Ha_d0. iFrame.
    iNext. iIntros "(%wscratch' & HPC & Hsrc & Hdst & Hscratch & Hcounter & Hws & HD)".
    iApply "Hpost". iExists wscratch'. iFrame.
    rewrite (region_pointsto_cells a_s); last (rewrite Hlen; solve_addr).
    iFrame.
  Qed.

End CopyContextMacro.
