From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import clear_stack_spec.
From griotte Require Export copy_context.

(** * Specification of [copy_context_asm]

    The copy of CHERIoT's [copyContext]. In [copy_context_spec], the source
    is a region of memory owned by the caller; the destination is generic:
    each store goes through a per-cell accessor [cells_store_acc_cell], so that
    the destination may be owned by the caller or opened from an invariant,
    and a store past the end of the destination capability, or to an
    exposed device, faults. Each cell of the destination is a stack cell:
    a store to a cell of the zone lowers MSHWM to it, but not below MSHWMB.
    In [copy_context_load_spec], the source is generic: each load goes
    through a per-cell accessor [cells_load_acc], and a load past the end
    of the source capability faults; the destination is owned. *)

Section CopyContextMacro.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {th : Thread} {CL : CritLink Σ th}
    `{MP: MachineParameters} {CR : CritRoute Σ th CL}.

  #[local] Existing Instance elim_modal_cerise_fupd_wp.

  (** One word per iteration, from [copy_loop] with [i] words copied. *)
  #[local] Lemma copy_context_loop_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr) (π_d : option AId)
    (ws : list LWord) (D : nat → iProp Σ) (i : nat) (wscratch : LWord)
    (mshwmb_v : Addr) (mshwm_v mshwm_v0 : Z) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter)) →
    length ws = 15%nat →
    (i < 15)%nat →
    readAllowed p_s = true →
    isDL p_s = false →
    isDRO p_s = false →
    (b_s <= a_s)%a →
    (a_s + 15 <= e_s)%Z →
    disjoint_from_shadow a_s (a_s ^+ 15) →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    cnull ∉ [dst; src; scratch; counter] →
    (mshwmb_v <= mshwm_v)%Z →
    (mshwm_v <= mshwm_v0)%Z →

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1) ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ Cap p_s g_s b_s e_s (a_s ^+ i) ∗
    dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ i) @@? π_d) ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ WInt (15 - i) ∗
    ([∗ list] k ↦ w ∈ ws, (a_s ^+ k) ↦ₐ w) ∗
    D i ∗
    cells_store_acc_cell D p_d e_d a_d π_d ws ∗
    hwm_regs mshwmb_v mshwm_v ∗
    ▷ ( ( ∀ (j : nat) (mshwm_v' : Z),
          ⌜(j < 15)%nat⌝ -∗
          ⌜(e_d <= a_d + j)%Z ∨ is_exposed_mmio_address (a_d ^+ j) = true⌝ -∗
          src ↦ᵣ Cap p_s g_s b_s e_s (a_s ^+ j) -∗
          dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ j) @@? π_d) -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          ([∗ list] k ↦ w ∈ ws, (a_s ^+ k) ↦ₐ w) -∗
          D j -∗
          ⌜(mshwmb_v <= mshwm_v')%Z⌝ -∗
          ⌜(mshwm_v' <= mshwm_v0)%Z⌝ -∗
          hwm_regs mshwmb_v mshwm_v' -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 2) -∗
          WP Seq (Instr Faulted) {{ φ }} ) ∧
        ( ∀ (wscratch' : LWord) (mshwm_v' : Z),
          ⌜(a_d + 15 <= e_d)%Z⌝ -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter)) -∗
          src ↦ᵣ Cap p_s g_s b_s e_s (a_s ^+ 15) -∗
          dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ 15) @@? π_d) -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          ([∗ list] k ↦ w ∈ ws, (a_s ^+ k) ↦ₐ w) -∗
          D 15 -∗
          ⌜(mshwmb_v <= mshwm_v')%Z⌝ -∗
          ⌜(mshwm_v' <= mshwm_v0)%Z⌝ -∗
          hwm_regs mshwmb_v mshwm_v' -∗
          WP Exec {{ φ }} ) )
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen Hi Hread Hdl Hdro Hb_s He_s Hshadow_s Hwrite Hb_d Hnull Hhb Hhh0)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hws & HD & #Hacc & Hhwm & Hpost)".
    assert (dst ≠ cnull ∧ src ≠ cnull ∧ scratch ≠ cnull ∧ counter ≠ cnull)
      as (Hdst_null & Hsrc_null & Hscratch_null & Hcounter_null)
      by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    iLöb as "IH" forall (i wscratch mshwm_v Hi Hhb Hhh0).
    destruct (lookup_lt_is_Some_2 ws i) as [wi Hwi]; first lia.
    iDestruct (big_sepL_lookup_acc _ _ i with "Hws") as "[Hwi Hws]"; first exact Hwi.
    (* CLoad scratch src 0 *)
    iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_dq _ _ _ _ _ _ _ scratch src 0)
      with "[$HPC $Hscratch $Hsrc $Hwi]" as "(HPC & Hscratch & Hsrc & Hwi)".
    { solve_addr. }
    { eapply disjoint_from_shadow_not_in; [exact Hshadow_s | rewrite /withinBounds; solve_addr]. }
    { rewrite /withinBounds; solve_addr. }
    rewrite lload_word_no_dl_dro //.
    iDestruct ("Hws" with "Hwi") as "Hws".
    destruct (decide (a_d + i < e_d)%Z) as [Hin | Hout]; cycle 1.
    { (* Store dst scratch 0 *)
      iInstrApply "Hcode" (wp_store_fail_reg_imm _ 0 _ _ _ _ _ _ _ _ dst scratch _ _ _ _ _
                             (a_d ^+ i))
        with "[$HPC $Hscratch $Hdst]" as "(HPC & Hscratch & Hdst)".
      { solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      iDestruct "Hpost" as "[Hfailed _]".
      iApply ("Hfailed" $! i mshwm_v with "[//] [%] Hsrc Hdst [$Hscratch] Hcounter Hws HD [//] [//] Hhwm
                [HPC]").
      { solve_addr. }
      by rewrite (_ : pc_a ^+ Z.to_nat 2 = pc_a ^+ 2); last solve_addr. }
    (* The rest of the iteration: the fault at an exposed device, or the
       stored word. *)
    iAssert ((⌜is_exposed_mmio_address (a_d ^+ i) = true⌝ -∗
              dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ i) @@? π_d) -∗
              scratch ↦ᵣ - -∗
              D i -∗
              hwm_regs mshwmb_v mshwm_v -∗
              PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 2) -∗
              WP Seq (Instr Faulted) {{ φ }}) ∧
             (∀ mshwm_v1 : Z,
              ⌜(mshwmb_v <= mshwm_v1)%Z⌝ -∗
              ⌜(mshwm_v1 <= mshwm_v0)%Z⌝ -∗
              PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 3) -∗
              scratch ↦ᵣ wi -∗
              dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ i) @@? π_d) -∗
              D (S i) -∗
              hwm_regs mshwmb_v mshwm_v1 -∗
              WP Exec {{ φ }}))%I
      with "[Hsrc Hcounter Hws Hpost]" as "Hnext".
    { iSplit.
      { iIntros (Hexp) "Hdst Hscratch HD Hhwm HPC".
        iDestruct "Hpost" as "[Hfailed _]".
        iApply ("Hfailed" $! i mshwm_v with "[//] [] Hsrc Hdst Hscratch Hcounter Hws HD [//] [//] Hhwm
                  HPC").
        by iRight. }
      iIntros (mshwm_v1 Hhb1 Hh10) "HPC Hscratch Hdst HD Hhwm".
      (* Add counter counter (-1) *)
      iInstr "Hcode".
      (* Lea dst dst 1 *)
      iInstr "Hcode".
      { transitivity (Some (a_d ^+ S i)); solve_addr. }
      (* Lea src src 1 *)
      iInstr "Hcode".
      { transitivity (Some (a_s ^+ S i)); solve_addr. }
      destruct (decide (i = 14)) as [-> | Hi14].
      - (* Jne -5 counter 0 *)
        iInstr "Hcode".
        iDestruct "Hpost" as "[_ Hpost]".
        iApply ("Hpost" $! _ mshwm_v1 with "[%] HPC Hsrc Hdst Hscratch Hcounter Hws HD [//] [//] Hhwm").
        solve_addr.
      - (* Jne -5 counter 0 *)
        iInstr "Hcode".
        { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
        { transitivity (Some (pc_a ^+ 1)); solve_addr. }
        replace (15 - i + -1)%Z with (15 - S i)%Z by lia.
        iApply ("IH" $! (S i) _ mshwm_v1 with "[] [//] [//] HPC Hsrc Hdst Hscratch Hcounter Hws HD Hhwm
                  Hpost").
        iPureIntro; lia. }
    iMod ("Hacc" $! i with "[%] [%] HD")
      as "[ (%v & %q & %Hsh_d & Hcell & Hderef & Hclose) | (%Hexp & %Hπ_d & HD & Hclose) ]".
    { lia. }
    { done. }
    - (* Store dst scratch 0 *)
      iInstrApply "Hcode"
        (wp_store_stack_cell_reg_store_word_imm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0)
        with "[$HPC $Hscratch $Hdst $Hcell $Hhwm $Hderef]"
        as (mshwm_v1) "(%Hh1 & HPC & Hscratch & Hdst & Hcell & Hhwm & Hderef)".
      { rewrite /withinBounds; solve_addr. }
      { solve_addr. }
      pose proof (hwm_after_base _ _ _ _ Hhb Hh1) as Hhb1.
      assert (mshwm_v1 <= mshwm_v0)%Z as Hh10.
      { destruct Hh1 as [-> | ->]; first done.
        rewrite /hwm_after. case_decide; lia. }
      rewrite -(list_lookup_total_correct _ _ _ Hwi).
      iMod ("Hclose" with "Hcell Hderef") as "HD".
      rewrite (list_lookup_total_correct _ _ _ Hwi).
      iDestruct "Hnext" as "[_ Hnext]".
      iApply ("Hnext" with "[//] [//] HPC Hscratch Hdst HD Hhwm").
    - subst π_d.
      (* Store dst scratch 0 *)
      iInstrApply "Hcode" (wp_store_timedev_reg _ _ _ _ _ _ _ (pc_a ^+ 3))
        with "[$HPC $Hscratch $Hdst]"
        as (retv) "[(-> & HPC & Hscratch & Hdst) | (-> & HPC & Hscratch & Hdst)]".
      { rewrite /withinBounds; solve_addr. }
      + iDestruct "Hnext" as "[Hfailed _]".
        iApply ("Hfailed" with "[//] Hdst [$Hscratch] HD Hhwm [HPC]").
        by rewrite (_ : pc_a ^+ Z.to_nat 2 = pc_a ^+ 2); last solve_addr.
      + iMod ("Hclose" with "HD") as "HD".
        iDestruct "Hnext" as "[_ Hnext]".
        iApply ("Hnext" with "[//] [//] HPC Hscratch Hdst HD Hhwm").
  Qed.

  (** [copy_context_asm dst src scratch counter] copies the 15 words [ws]
      of the region at [a_s] to the cells from [a_d], through the
      accessor of the destination. A store past the end [e_d] of the
      destination capability, or to an exposed device (cell [j] in
      bounds), faults at [pc_a ^+ 2], with [j] words copied: the
      continuation receives the fault, before trap entry. *)
  Lemma copy_context_spec
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a : Addr)
    (dst src scratch counter : RegName)
    (p_s : Perm) (g_s : Locality) (b_s e_s a_s : Addr)
    (p_d : Perm) (g_d : Locality) (b_d e_d a_d : Addr) (π_d : option AId)
    (ws : list LWord) (wscratch wcounter : LWord) (D : nat → iProp Σ)
    (mshwmb_v : Addr) (mshwm_v : Z) φ :
    executeAllowed pc_p = true →
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter)) →
    length ws = 15%nat →
    readAllowed p_s = true →
    isDL p_s = false →
    isDRO p_s = false →
    (b_s <= a_s)%a →
    (a_s + 15 <= e_s)%Z →
    disjoint_from_shadow a_s (a_s ^+ 15) →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    cnull ∉ [dst; src; scratch; counter] →
    (mshwmb_v <= mshwm_v)%Z →

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ Cap p_s g_s b_s e_s a_s ∗
    dst ↦ᵣ (Cap p_d g_d b_d e_d a_d @@? π_d) ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ wcounter ∗
    [[ a_s , a_s ^+ 15 ]] ↦ₐ [[ ws ]] ∗
    D 0 ∗
    cells_store_acc_cell D p_d e_d a_d π_d ws ∗
    hwm_regs mshwmb_v mshwm_v ∗
    ▷ ( ( ∀ (j : nat) (mshwm_v' : Z),
          ⌜(j < 15)%nat⌝ -∗
          ⌜(e_d <= a_d + j)%Z ∨ is_exposed_mmio_address (a_d ^+ j) = true⌝ -∗
          src ↦ᵣ Cap p_s g_s b_s e_s (a_s ^+ j) -∗
          dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ j) @@? π_d) -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          [[ a_s , a_s ^+ 15 ]] ↦ₐ [[ ws ]] -∗
          D j -∗
          ⌜(mshwmb_v <= mshwm_v')%Z⌝ -∗
          ⌜(mshwm_v' <= mshwm_v)%Z⌝ -∗
          hwm_regs mshwmb_v mshwm_v' -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 2) -∗
          WP Seq (Instr Faulted) {{ φ }} ) ∧
        ( ∀ (wscratch' : LWord) (mshwm_v' : Z),
          ⌜(a_d + 15 <= e_d)%Z⌝ -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter)) -∗
          src ↦ᵣ Cap p_s g_s b_s e_s (a_s ^+ 15) -∗
          dst ↦ᵣ (Cap p_d g_d b_d e_d (a_d ^+ 15) @@? π_d) -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          [[ a_s , a_s ^+ 15 ]] ↦ₐ [[ ws ]] -∗
          D 15 -∗
          ⌜(mshwmb_v <= mshwm_v')%Z⌝ -∗
          ⌜(mshwm_v' <= mshwm_v)%Z⌝ -∗
          hwm_regs mshwmb_v mshwm_v' -∗
          WP Exec {{ φ }} ) )
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen Hread Hdl Hdro Hb_s He_s Hshadow_s Hwrite Hb_d Hnull Hhb)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hws & HD & #Hacc & Hhwm & Hpost)".
    assert (counter ≠ cnull) as Hcounter_null by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    (* Mov counter 15 *)
    iInstr "Hcode".
    iEval (rewrite (region_pointsto_cells a_s); last (rewrite Hlen; solve_addr)) in "Hws".
    assert (a_s ^+ 0%nat = a_s) as Ha_s0 by solve_addr.
    assert (a_d ^+ 0%nat = a_d) as Ha_d0 by solve_addr.
    iApply (copy_context_loop_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D 0 _ mshwmb_v mshwm_v mshwm_v
             with "[$HPC $Hcode $Hscratch $Hcounter $Hws $HD $Hacc $Hhwm Hsrc Hdst Hpost]").
    all: try (lia || done).
    rewrite Ha_s0 Ha_d0. iFrame "Hsrc Hdst".
    iNext. iSplit.
    - iIntros (j mshwm_v' Hj Hout) "Hsrc Hdst Hscratch Hcounter Hws HD %Hhb' %Hhh' Hhwm".
      iDestruct "Hpost" as "[Hfailed _]".
      iApply ("Hfailed" with "[//] [//] Hsrc Hdst Hscratch Hcounter [Hws] HD [//] [//] Hhwm").
      rewrite (region_pointsto_cells a_s); last (rewrite Hlen; solve_addr).
      iFrame.
    - iIntros (wscratch' mshwm_v' Hin) "HPC Hsrc Hdst Hscratch Hcounter Hws HD %Hhb' %Hhh' Hhwm".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//] HPC Hsrc Hdst Hscratch Hcounter [Hws] HD [//] [//] Hhwm").
      rewrite (region_pointsto_cells a_s); last (rewrite Hlen; solve_addr).
      iFrame.
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
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter)) →
    length wd = 15%nat →
    length ls = i →
    take i wd = lstore_word p_d <$> ls →
    (i < 15)%nat →
    readAllowed p_s = true →
    (b_s <= a_s)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    disjoint_from_shadow a_d (a_d ^+ 15) →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1) ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ i) @@? π_s) ∗
    dst ↦ᵣ Cap p_d g_d b_d e_d (a_d ^+ i) ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ WInt (15 - i) ∗
    ([∗ list] k ↦ w ∈ wd, (a_d ^+ k) ↦ₐ w) ∗
    L i ls ∗
    cells_load_acc L p_s e_s a_s π_s 15 ∗
    hwm_closed (kind_of th) ∗
    ▷ ( ( ∀ (j : nat) (ls' wd' : list LWord),
          ⌜(j < 15)%nat⌝ -∗
          ⌜length ls' = j⌝ -∗
          ⌜length wd' = 15%nat⌝ -∗
          ⌜(e_s <= a_s + j)%Z⌝ -∗
          src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ j) @@? π_s) -∗
          dst ↦ᵣ Cap p_d g_d b_d e_d (a_d ^+ j) -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          ([∗ list] k ↦ w ∈ wd', (a_d ^+ k) ↦ₐ w) -∗
          L j ls' -∗
          hwm_closed (kind_of th) -∗
          trap_safe (Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1)) ⊤ φ ) ∧
        ( ∀ (ls' : list LWord) (wscratch' : LWord),
          ⌜length ls' = 15%nat⌝ -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter)) -∗
          src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ 15) @@? π_s) -∗
          dst ↦ᵣ Cap p_d g_d b_d e_d (a_d ^+ 15) -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          ([∗ list] k ↦ w ∈ lstore_word p_d <$> ls', (a_d ^+ k) ↦ₐ w) -∗
          L 15 ls' -∗
          hwm_closed (kind_of th) -∗
          WP Exec {{ φ }} ) )
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hlen_wd Hlen_ls Htake Hi Hread Hb_s Hwrite Hb_d He_d Hshadow_d
               Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hwd & HL & #Hacc & Hclosed & Hpost)".
    assert (dst ≠ cnull ∧ src ≠ cnull ∧ scratch ≠ cnull ∧ counter ≠ cnull)
      as (Hdst_null & Hsrc_null & Hscratch_null & Hcounter_null)
      by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    iLöb as "IH" forall (wd ls i wscratch Hlen_wd Hlen_ls Htake Hi).
    destruct (decide (a_s + i < e_s)%Z) as [Hin | Hout]; cycle 1.
    { (* CLoad scratch src 0 *)
      iInstrApply "Hcode" (wp_load_fail_not_withinbounds_imm _ scratch src)
        with "[$HPC $Hscratch $Hsrc]" as "(HPC & Hscratch & Hsrc)".
      { instantiate (1 := a_s ^+ i). rewrite /withinBounds; solve_addr. }
      { solve_addr. }
      iDestruct "Hpost" as "[Hfailed _]".
      iTrap with ("Hfailed" $! i ls wd with
                   "[//] [//] [//] [%] Hsrc Hdst [$Hscratch] Hcounter Hwd HL").
      solve_addr. }
    (* The rest of the iteration, once the word [v'] is loaded. *)
    iAssert (∀ v' : LWord,
               PC ↦ₚ Cap pc_p pc_g pc_b pc_e (pc_a ^+ 2) -∗
               scratch ↦ᵣ v' -∗
               src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ i) @@? π_s) -∗
               L (S i) (ls ++ [v']) -∗
               WP Exec {{ φ }})%I
      with "[Hdst Hcounter Hwd Hclosed Hpost]" as "Hnext".
    { iIntros (v') "HPC Hscratch Hsrc HL".
      destruct (lookup_lt_is_Some_2 wd i) as [wi Hwi]; first lia.
      iDestruct (big_sepL_insert_acc _ _ i with "Hwd") as "[Hwi Hwd]"; first exact Hwi.
      (* Store dst scratch 0 *)
      iInstr "Hcode".
      { rewrite /withinBounds; solve_addr. }
      iDestruct ("Hwd" with "Hwi") as "Hwd".
      (* Add counter counter (-1) *)
      iInstr "Hcode".
      (* Lea dst dst 1 *)
      iInstr "Hcode".
      { transitivity (Some (a_d ^+ S i)); solve_addr. }
      (* Lea src src 1 *)
      iInstr "Hcode".
      { transitivity (Some (a_s ^+ S i)); solve_addr. }
      assert (take (S i) (<[i:=lstore_word p_d v']> wd) = lstore_word p_d <$> ls ++ [v'])
        as Htake'.
      { rewrite (take_S_r _ _ (lstore_word p_d v')); last (apply list_lookup_insert_eq; lia).
        rewrite take_insert decide_False; last lia.
        by rewrite fmap_app Htake. }
      destruct (decide (i = 14)) as [-> | Hi14].
      - (* Jne -5 counter 0 *)
        iInstr "Hcode".
        iDestruct "Hpost" as "[_ Hpost]".
        rewrite take_ge in Htake'; last (rewrite length_insert; lia).
        iEval (rewrite Htake') in "Hwd".
        rewrite (_ : (15 - 14%nat + -1)%Z = 0%Z); last lia.
        iApply ("Hpost" with "[%] [HPC] Hsrc Hdst Hscratch Hcounter Hwd HL Hclosed").
        { rewrite length_app /=; lia. }
        { iExact "HPC". }
      - (* Jne -5 counter 0 *)
        iInstr "Hcode".
        { apply negb_true_iff, Z.eqb_neq. cbn. lia. }
        { transitivity (Some (pc_a ^+ 1)); solve_addr. }
        replace (15 - i + -1)%Z with (15 - S i)%Z by lia.
        iApply ("IH" $! (<[i:=lstore_word p_d v']> wd) (ls ++ [v']) (S i)
                 with "[%] [%] [%] [%] HPC Hsrc Hdst Hscratch Hcounter Hwd HL Hclosed Hpost").
        + by rewrite length_insert.
        + rewrite length_app /=; lia.
        + exact Htake'.
        + lia. }
    iMod ("Hacc" $! i ls with "[%] [%] HL")
      as "[ (%v & %dq & %wit & %dw & %Hsh_s & %Hπ & Hcell & Hwit & Hdw & Hclose)
          | (%Hexp & %Hπ & Hclose) ]".
    { lia. }
    { solve_addr. }
    - (* CLoad scratch src 0 *)
      iInstrApply "Hcode" (wp_load_witness_imm_one_inbounds_deref _ _ _ _ _ _ _ scratch src 0)
        with "[$HPC $Hscratch $Hsrc $Hcell $Hwit $Hdw]"
        as (v') "(%Hload & HPC & Hscratch & Hsrc & Hcell & Hwit & Hdw)".
      { solve_addr. }
      { rewrite /withinBounds; solve_addr. }
      iMod ("Hclose" $! v' with "[//] Hcell Hwit Hdw") as "HL".
      iApply ("Hnext" with "HPC Hscratch Hsrc HL").
    - subst π_s.
      (* CLoad scratch src 0 *)
      iInstrApply "Hcode" (wp_load_success_from_timedev _ scratch src)
        with "[$HPC $Hscratch $Hsrc]"
        as (z) "(HPC & Hscratch & Hsrc)".
      { rewrite /withinBounds; split; [done | solve_addr]. }
      iMod ("Hclose" $! z) as "HL".
      iApply ("Hnext" with "HPC Hscratch Hsrc HL").
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
    SubBounds pc_b pc_e pc_a (pc_a ^+ length (copy_context_instrs dst src scratch counter)) →
    readAllowed p_s = true →
    (b_s <= a_s)%a →
    writeAllowed p_d = true →
    (b_d <= a_d)%a →
    (a_d + 15 <= e_d)%Z →
    disjoint_from_shadow a_d (a_d ^+ 15) →
    length wd = 15%nat →
    cnull ∉ [dst; src; scratch; counter] →

    PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a ∗
    codefrag_pers pc_a (copy_context_instrs dst src scratch counter) ∗
    src ↦ᵣ (Cap p_s g_s b_s e_s a_s @@? π_s) ∗
    dst ↦ᵣ Cap p_d g_d b_d e_d a_d ∗
    scratch ↦ᵣ wscratch ∗
    counter ↦ᵣ wcounter ∗
    [[ a_d , a_d ^+ 15 ]] ↦ₐ [[ wd ]] ∗
    L 0 [] ∗
    cells_load_acc L p_s e_s a_s π_s 15 ∗
    hwm_closed (kind_of th) ∗
    ▷ ( ( ∀ (j : nat) (ls wd' : list LWord),
          ⌜(j < 15)%nat⌝ -∗
          ⌜length ls = j⌝ -∗
          ⌜length wd' = 15%nat⌝ -∗
          ⌜(e_s <= a_s + j)%Z⌝ -∗
          src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ j) @@? π_s) -∗
          dst ↦ᵣ Cap p_d g_d b_d e_d (a_d ^+ j) -∗
          scratch ↦ᵣ - -∗
          counter ↦ᵣ WInt (15 - j) -∗
          [[ a_d , a_d ^+ 15 ]] ↦ₐ [[ wd' ]] -∗
          L j ls -∗
          hwm_closed (kind_of th) -∗
          trap_safe (Cap pc_p pc_g pc_b pc_e (pc_a ^+ 1)) ⊤ φ ) ∧
        ( ∀ (ls : list LWord) (wscratch' : LWord),
          ⌜length ls = 15%nat⌝ -∗
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e
                  (pc_a ^+ length (copy_context_instrs dst src scratch counter)) -∗
          src ↦ᵣ (Cap p_s g_s b_s e_s (a_s ^+ 15) @@? π_s) -∗
          dst ↦ᵣ Cap p_d g_d b_d e_d (a_d ^+ 15) -∗
          scratch ↦ᵣ wscratch' -∗
          counter ↦ᵣ WInt 0 -∗
          [[ a_d , a_d ^+ 15 ]] ↦ₐ [[ lstore_word p_d <$> ls ]] -∗
          L 15 ls -∗
          hwm_closed (kind_of th) -∗
          WP Exec {{ φ }} ) )
    ⊢ WP Exec {{ φ }}.
  Proof.
    iIntros (Hexec Hsub Hread Hb_s Hwrite Hb_d He_d Hshadow_d Hlen Hnull)
      "(HPC & #Hcode & Hsrc & Hdst & Hscratch & Hcounter & Hwd & HL & #Hacc & Hclosed & Hpost)".
    assert (counter ≠ cnull) as Hcounter_null by (clear -Hnull; set_solver).
    codefrag_facts "Hcode".
    (* Mov counter 15 *)
    iInstr "Hcode".
    iEval (rewrite (region_pointsto_cells a_d); last (rewrite Hlen; solve_addr)) in "Hwd".
    assert (a_s ^+ 0%nat = a_s) as Ha_s0 by solve_addr.
    assert (a_d ^+ 0%nat = a_d) as Ha_d0 by solve_addr.
    iApply (copy_context_load_loop_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wd [] L 0
             with "[$HPC $Hcode $Hscratch $Hwd $HL $Hacc $Hclosed Hcounter Hsrc Hdst Hpost]").
    all: try (lia || done).
    rewrite Ha_s0 Ha_d0. iFrame "Hsrc Hdst".
    rewrite (_ : (15 - 0%nat)%Z = 15%Z); last lia. iFrame "Hcounter".
    iNext. iSplit.
    - iIntros (j ls wd' Hj Hls Hwd' Hout) "Hsrc Hdst Hscratch Hcounter Hwd HL Hclosed".
      iDestruct "Hpost" as "[Hfailed _]".
      iApply ("Hfailed" with "[//] [//] [//] [//] Hsrc Hdst Hscratch Hcounter [Hwd] HL Hclosed").
      rewrite (region_pointsto_cells a_d); last (rewrite Hwd'; solve_addr).
      iFrame.
    - iIntros (ls wscratch' Hls) "HPC Hsrc Hdst Hscratch Hcounter Hwd HL Hclosed".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//] HPC Hsrc Hdst Hscratch Hcounter [Hwd] HL Hclosed").
      rewrite (region_pointsto_cells a_d); last (rewrite length_fmap Hls; solve_addr).
      iFrame.
  Qed.

End CopyContextMacro.
