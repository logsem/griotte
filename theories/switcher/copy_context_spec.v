From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Export copy_context.

(** * Specification of [copy_context_asm]

    The copy of CHERIoT's [copyContext]. In [copy_context_spec], the source
    is a region of memory owned by the caller; the destination is generic:
    each store goes through a per-cell accessor [cells_store_acc], so that
    the destination may be owned by the caller or opened from an invariant.
    In [copy_context_load_spec], the source is generic: each load goes
    through a per-cell accessor [cells_load_acc], and a load past the end
    of the source capability faults; the destination is owned. *)

Section CopyContextMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}.

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

  (* TODO: move to rules_Load.v *)
  (** A load of a cell of any fraction, through a capability with an
      identifier [π], under a status witness and a dereference witness of
      [π]. *)
  Lemma wp_load_witness_imm_one_inbounds_deref E pc_p pc_g pc_b pc_e pc_a pc_a'
      dst src (imm : Z) (wi wd : LWord) dq dq' p g b e a_src a π (raw : LWord) wit dw :
    decodeInstrW wi.(lw) = CLoad dst src imm →
    isCorrectPC (WCap true pc_p pc_g pc_b pc_e pc_a) →
    (a_src + imm)%a = Some a →
    is_shadow_address a = false →
    readAllowed p = true →
    withinBounds b e a = true →
    (pc_a + 1)%a = Some pc_a' →
    π = deref_id dw →
    dst ≠ cnull →
    src ≠ cnull →
    {{{ PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ wd ∗
        src ↦ᵣ (WCap true p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}
      Instr Executable @ E
    {{{ actual, RET NextIV;
        ⌜load_post wit p raw actual⌝ ∗
        PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a' ∗
        pc_a ↦ₐ{dq} wi ∗
        dst ↦ᵣ actual ∗
        src ↦ᵣ (WCap true p g b e a_src @@? π) ∗
        a ↦ₐ{dq'} raw ∗
        load_witness_res wit ∗
        deref_witness_res dw }}}.
  Proof.
    iIntros (Hinstr Hvpc Hea Hnot_shadow Hread Hbounds Hpca' Hπ Hdst Hsrc Φ)
      "(HPC & Hi & Hdst & Hsrc & Ha & Hwit & Hdw) HΦ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hsrc_dst]".
    iAssert ((if (a =? pc_a)%a then emp else ▷ a ↦ₐ{dq'} raw) ∗
             (if (a =? pc_a)%a then a ↦ₐ{dq'} raw else emp))%I
      with "[Ha]" as "[Ha Ha_aside]".
    { destruct (a =? pc_a)%a; iFrame. }
    iAssert (⌜a = pc_a → raw = wi⌝)%I as %Hraw.
    { iIntros (->). rewrite Z.eqb_refl.
      by iDestruct (pointsto_agree with "Ha_aside Hi") as %->. }
    iDestruct (memMap_resource_2gen_clater_dq pc_a a dq dq' wi raw (λ a dq w, a ↦ₐ{dq} w)%I
                with "Hi Ha") as (mem dfracs) "[Hmem %Hmem]".
    iAssert (▷ ([∗ map] k↦revoked ∈ (∅ : ShadowTbl), k ↦ₛ{DfracDiscarded} revoked))%I
      as "Hshadow".
    { by rewrite big_sepM_empty. }
    assert (mem !! pc_a = Some wi ∧ mem !! a = Some raw ∧ dom mem = dom dfracs)
      as (Hmem_pc & Hmem_a & Hdom).
    { destruct (a =? pc_a)%a eqn:Heq; destruct Hmem as [-> ->].
      - apply Z.eqb_eq in Heq. assert (a = pc_a) as -> by solve_addr.
        rewrite (Hraw eq_refl).
        split_and!; [by simplify_map_eq | by simplify_map_eq | by rewrite !dom_insert_L].
      - apply Z.eqb_neq in Heq. assert (a ≠ pc_a) by (intros ->; done).
        split_and!; [by simplify_map_eq | by simplify_map_eq | by rewrite !dom_insert_L]. }
    iApply (wp_load_general_shadow_imm E pc_p pc_g pc_b pc_e pc_a None dst src imm wi
      mem dfracs _ ∅ DfracDiscarded wit dw
      with "[$HPC $Hmem $Hshadow $Hmap $Hwit $Hdw]").
    { exact Hinstr. }
    { exact Hvpc. }
    { by rewrite !dom_insert; set_solver+. }
    { exact Hmem_pc. }
    { intros p0 g0 b0 e0 ea0 Hallow.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hnot_shadow.
      destruct (is_revoker_address a); first done.
      eexists. exact Hmem_a. }
    { exact Hdom. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hmem & _ & Hwit & Hdw & Hmap)".
    iDestruct (memMap_resource_2gen_d_dq with "[Hmem]") as "[Hi Ha]".
    { iExists mem, dfracs. iSplitL; auto. }
    iAssert (a ↦ₐ{dq'} raw)%I with "[Ha Ha_aside]" as "Ha".
    { destruct (a =? pc_a)%a; iFrame. }
    destruct Hspec as [p0 g0 b0 e0 ea0 loadv actual Hallow Hsh Hlookup Hactual Hinc ->
                      |p0 g0 b0 e0 ea0 heap_a revoked Hallow Hsh _ Hlookup _
                      |p0 g0 b0 e0 ea0 Hallow Hrev Hlookup _
                      |Hfail -> ->].
    - destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      rewrite Hmem_a in Hlookup. injection Hlookup as <-.
      rewrite linsert_reg_not_cnull //.
      apply incrementPC_Some_inv in Hinc
        as (tpc & ppc & gpc & bpc & epc & apc & apc'' & πpc & HPC & Hapc & ->).
      injection HPC as <- <- <- <- <- <- <-.
      rewrite Hpca' in Hapc. injection Hapc as <-.
      rewrite (insert_insert_ne _ dst src) // insert_insert_eq.
      iDestruct (regs_of_map_2 with "Hmap") as "(Hsrc & Hdst)"; eauto.
      iApply "HΦ". by iFrame.
    - exfalso. by rewrite lookup_empty in Hlookup.
    - exfalso.
      destruct (reg_allows_load_offset_imm _ _ _ _ _ _ _ _ Hallow) as [a0 (Hsrc0 & Haddr & _)].
      destruct (llookup_reg_cap _ _ _ _ _ _ _ _ Hsrc0) as (_ & π0 & Hsrc0').
      rewrite lookup_insert_eq in Hsrc0'. injection Hsrc0' as <- <- <- <- <- <-.
      rewrite Hea in Haddr. injection Haddr as <-.
      by rewrite Hmem_a in Hlookup.
    - exfalso. eapply (load_failure_spec_impossible _ _ _ _ _ _ _ p g b e a_src a);
        eauto; try by simplify_map_eq.
      all: try (by intros ? Hv; rewrite llookup_reg_not_cnull // in Hv; simplify_map_eq).
      all: rewrite llookup_reg_not_cnull //; by simplify_map_eq.
  Qed.

  (** One word per iteration of the copy with a load accessor, from
      [copy_loop] with [i] words loaded: [ls], stored to the first [i]
      cells of the destination [wd]. *)
  #[local] Lemma copy_context_load_loop_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr) (π_s : option AId)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr)
    (wd ls : list LWord) (L : nat → list LWord → iProp Σ) (i : nat) (wscratch : LWord) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a →
    length wd = 15%nat →
    length ls = i →
    take i wd = lstore_word p_d <$> ls →
    (i < 15)%nat →
    readAllowed p_s = true →
    (b_s <= a_s)%a →
    is_Some (a_s + 15)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    disjoint_from_shadow a_d (a_d ^+ 15)%a →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ (WCap true p_s g_s b_s e_s (a_s ^+ i)%a @@? π_s) ∗
    dst ↦ᵣ WCap true p_d g_d b_d e_d (a_d ^+ i)%a ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ WInt (15 - i) ∗
    ([∗ list] k ↦ w ∈ wd, (a_d ^+ k)%a ↦ₐ w) ∗
    L i ls ∗
    cells_load_acc L p_s e_s a_s π_s 15 ∗
    ▷ ( ( ∀ (j : nat) (ls' wd' : list LWord),
          ⌜(j < 15)%nat⌝ -∗
          ⌜length ls' = j⌝ -∗
          ⌜length wd' = 15%nat⌝ -∗
          ⌜(e_s <= a_s + j)%Z⌝ -∗
          src ↦ᵣ (WCap true p_s g_s b_s e_s (a_s ^+ j)%a @@? π_s) -∗
          dst ↦ᵣ WCap true p_d g_d b_d e_d (a_d ^+ j)%a -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          ([∗ list] k ↦ w ∈ wd', (a_d ^+ k)%a ↦ₐ w) -∗
          L j ls' -∗
          trap_safe (WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a) ⊤ φ ) ∧
        ( ∀ (ls' : list LWord) (wscratch' : LWord),
          ⌜length ls' = 15%nat⌝ -∗
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a -∗
          src ↦ᵣ (WCap true p_s g_s b_s e_s (a_s ^+ 15)%a @@? π_s) -∗
          dst ↦ᵣ WCap true p_d g_d b_d e_d (a_d ^+ 15)%a -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          ([∗ list] k ↦ w ∈ lstore_word p_d <$> ls', (a_d ^+ k)%a ↦ₐ w) -∗
          L 15 ls' -∗
          WP Seq (Instr Executable) {{ φ }} ) )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen_wd Hlen_ls Htake Hi Hread Hb_s He_s Hwrite Hb_d He_d Hshadow_d
               Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hwd & HL & #Hacc & Hpost)".
    assert (dst ≠ cnull ∧ src ≠ cnull ∧ scratch ≠ cnull ∧ counter ≠ cnull)
      as (Hdst_null & Hsrc_null & Hscratch_null & Hcounter_null)
      by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    iLöb as "IH" forall (wd ls i wscratch Hlen_wd Hlen_ls Htake Hi).
    destruct (decide (a_s + i < e_s)%Z) as [Hin | Hout]; cycle 1.
    { (* CLoad scratch src 0 *)
      iInstrApply "Hcode" (wp_load_fail_not_withinbounds_imm _ scratch src)
        with "[$HPC $Hscratch $Hsrc]" as "(HPC & Hscratch & Hsrc)".
      { instantiate (1 := (a_s ^+ i)%a). rewrite /withinBounds; solve_addr. }
      { solve_addr. }
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! i ls wd with
                   "[//] [//] [//] [%] Hsrc Hdst [$Hscratch] Hcounter Hwd HL").
      solve_addr. }
    iMod ("Hacc" $! i ls with "[%] [%] HL") as (v dq wit dw) "(%Hsh_s & %Hπ & Hcell & Hwit & Hdw & Hclose)".
    { lia. }
    { solve_addr. }
    (* CLoad scratch src 0 *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_deref _ _ _ _ _ _ _ scratch src 0)
      with "[$HPC $Hscratch $Hsrc $Hcell $Hwit $Hdw]"
      as (v') "(%Hload & HPC & Hscratch & Hsrc & Hcell & Hwit & Hdw)".
    { solve_addr. }
    { destruct He_s as [? ?]. rewrite /withinBounds; solve_addr. }
    iMod ("Hclose" $! v' with "[//] Hcell Hwit Hdw") as "HL".
    destruct (lookup_lt_is_Some_2 wd i) as [wi Hwi]; first lia.
    iDestruct (big_sepL_insert_acc _ _ i with "Hwd") as "[Hwi Hwd]"; first exact Hwi.
    iPoseProof deref_res_none as "Hderef".
    (* Store dst scratch 0 *)
    iInstrApply "Hcode"
      (wp_store_success_reg_store_word_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0)
      with "[$HPC $Hscratch $Hdst $Hwi $Hderef]"
      as "(HPC & Hscratch & Hdst & Hwi & _)".
    { eapply disjoint_from_shadow_not_in; [exact Hshadow_d | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    { solve_addr. }
    iDestruct ("Hwd" with "Hwi") as "Hwd".
    (* Add counter counter (-1) *)
    iInstr "Hcode".
    (* Lea dst 1 *)
    iInstr "Hcode".
    { transitivity (Some (a_d ^+ S i)%a); solve_addr. }
    (* Lea src 1 *)
    iInstr "Hcode".
    { destruct He_s as [? ?]. transitivity (Some (a_s ^+ S i)%a); solve_addr. }
    assert (take (S i) (<[i:=lstore_word p_d v']> wd) = lstore_word p_d <$> ls ++ [v'])
      as Htake'.
    { rewrite (take_S_r _ _ (lstore_word p_d v')); last (apply list_lookup_insert_eq; lia).
      rewrite take_insert decide_False; last lia.
      by rewrite fmap_app Htake. }
    destruct (decide (i = 14)) as [-> | Hi14].
    - (* Jnz -5 counter *)
      iInstr "Hcode".
      iDestruct "Hpost" as "[_ Hpost]".
      rewrite take_ge in Htake'; last (rewrite length_insert; lia).
      iEval (rewrite Htake') in "Hwd".
      rewrite (_ : (15 - 14%nat + -1)%Z = 0%Z); last lia.
      iApply ("Hpost" with "[%] [HPC] Hsrc Hdst Hscratch Hcounter Hwd HL").
      { rewrite length_app /=; lia. }
      { iExact "HPC". }
    - (* Jnz -5 counter *)
      iInstr "Hcode".
      { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
      { transitivity (Some (pc_a ^+ 1)%a); solve_addr. }
      replace (15 - i + -1)%Z with (15 - S i)%Z by lia.
      iApply ("IH" $! (<[i:=lstore_word p_d v']> wd) (ls ++ [v']) (S i)
               with "[%] [%] [%] [%] HPC Hsrc Hdst Hscratch Hcounter Hwd HL Hpost").
      + by rewrite length_insert.
      + rewrite length_app /=; lia.
      + exact Htake'.
      + lia.
  Qed.

  (** [copy_context_asm dst src scratch counter] copies the 15 words at
      [a_s], loaded through the accessor of the source, to the region
      at [a_d]. A load past the end [e_s] of the source capability faults
      at [pc_a ^+ 1], with [j] words loaded. *)
  Lemma copy_context_load_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr) (π_s : option AId)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr)
    (wd : list LWord) (wscratch wcounter : LWord) (L : nat → list LWord → iProp Σ) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a →
    readAllowed p_s = true →
    (b_s <= a_s)%a →
    is_Some (a_s + 15)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    disjoint_from_shadow a_d (a_d ^+ 15)%a →
    length wd = 15%nat →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ WCap true pc_p pc_g pc_b pc_e pc_a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ (WCap true p_s g_s b_s e_s a_s @@? π_s) ∗
    dst ↦ᵣ WCap true p_d g_d b_d e_d a_d ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ wcounter ∗
    [[ a_d , (a_d ^+ 15)%a ]] ↦ₐ [[ wd ]] ∗
    L 0 [] ∗
    cells_load_acc L p_s e_s a_s π_s 15 ∗
    ▷ ( ( ∀ (j : nat) (ls wd' : list LWord),
          ⌜(j < 15)%nat⌝ -∗
          ⌜length ls = j⌝ -∗
          ⌜length wd' = 15%nat⌝ -∗
          ⌜(e_s <= a_s + j)%Z⌝ -∗
          src ↦ᵣ (WCap true p_s g_s b_s e_s (a_s ^+ j)%a @@? π_s) -∗
          dst ↦ᵣ WCap true p_d g_d b_d e_d (a_d ^+ j)%a -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          [[ a_d , (a_d ^+ 15)%a ]] ↦ₐ [[ wd' ]] -∗
          L j ls -∗
          trap_safe (WCap true pc_p pc_g pc_b pc_e (pc_a ^+ 1)%a) ⊤ φ ) ∧
        ( ∀ (ls : list LWord) (wscratch' : LWord),
          ⌜length ls = 15%nat⌝ -∗
          PC ↦ₚ WCap true pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter))%a -∗
          src ↦ᵣ (WCap true p_s g_s b_s e_s (a_s ^+ 15)%a @@? π_s) -∗
          dst ↦ᵣ WCap true p_d g_d b_d e_d (a_d ^+ 15)%a -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          [[ a_d , (a_d ^+ 15)%a ]] ↦ₐ [[ lstore_word p_d <$> ls ]] -∗
          L 15 ls -∗
          WP Seq (Instr Executable) {{ φ }} ) )
    ⊢ WP Seq (Instr Executable) {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hread Hb_s He_s Hwrite Hb_d He_d Hshadow_d Hlen Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hwd & HL & #Hacc & Hpost)".
    assert (counter ≠ cnull) as Hcounter_null by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    (* Mov counter 15 *)
    iInstr "Hcode".
    rewrite decide_False //.
    iEval (rewrite (region_pointsto_cells a_d); last (rewrite Hlen; solve_addr)) in "Hwd".
    assert ((a_s ^+ 0%nat)%a = a_s) as Ha_s0 by solve_addr.
    assert ((a_d ^+ 0%nat)%a = a_d) as Ha_d0 by solve_addr.
    iApply (copy_context_load_loop_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wd [] L 0
             with "[$HPC $Hcode $Hscratch $Hwd $HL $Hacc Hcounter Hsrc Hdst Hpost]").
    all: try (lia || done).
    rewrite Ha_s0 Ha_d0. iFrame "Hsrc Hdst".
    rewrite (_ : (15 - 0%nat)%Z = 15%Z); last lia. iFrame "Hcounter".
    iNext. iSplit.
    - iIntros (j ls wd' Hj Hls Hwd' Hout) "Hsrc Hdst Hscratch Hcounter Hwd HL".
      iDestruct "Hpost" as "[Hfailed _]".
      iApply ("Hfailed" with "[//] [//] [//] [//] Hsrc Hdst Hscratch Hcounter [Hwd] HL").
      rewrite (region_pointsto_cells a_d); last (rewrite Hwd'; solve_addr).
      iFrame.
    - iIntros (ls wscratch' Hls) "HPC Hsrc Hdst Hscratch Hcounter Hwd HL".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//] HPC Hsrc Hdst Hscratch Hcounter [Hwd] HL").
      rewrite (region_pointsto_cells a_d); last (rewrite length_fmap Hls; solve_addr).
      iFrame.
  Qed.

End CopyContextMacro.
