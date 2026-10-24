From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics wp_rules_interp.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 4-7: prepare the callee's stack and unseal

    Block 4 restricts the stack capability to the callee's stack frame,
    below the spill area,
    block 5 clears it, block 6 loads the unsealing capability of the
    switcher, and the first instruction of block 7 unseals the entry point of
    the callee. *)

Section Switcher_Call_Blocks_3.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 4: the stack capability with its cursor [a] is cut at [a]: [ct2]
      gets the part [[b, a)] below the cursor with its cursor at the base,
      and [csp] the same part with its cursor at the top. *)
  Lemma switcher_call_block_4_spec
    pc_b pc_e pc_a
    b_stk e_stk a_stk
    wcs0 wcs1 wct2 :
    let switcher_instrs_4 := (switcher_instrs_n 4) in
    let len_switcher_4 := length switcher_instrs_4 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_4)%a ->
    (b_stk <= a_stk)%a ->
    (a_stk <= e_stk)%a ->
    disjoint_from_heap b_stk e_stk ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    codefrag_pers pc_a switcher_instrs_4 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_4)%a ∗
        cs0 ↦ᵣ WInt a_stk ∗
        cs1 ↦ᵣ WInt b_stk ∗
        ct2 ↦ᵣ WCap true RWL Local b_stk a_stk b_stk ∗
        csp ↦ᵣ WCap true RWL Local b_stk a_stk a_stk ∗
        codefrag_pers pc_a switcher_instrs_4 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_4 len_switcher_4; subst switcher_instrs_4 len_switcher_4.
    iIntros (Hsub_reg Hastk_b Hastk_e Hstk_heap) "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* GetA cs0 csp *)
    iInstr "Hcode".
    (* GetB cs1 csp *)
    iInstr "Hcode".
    (* SetA csp csp cs1 *)
    iInstr "Hcode".

    assert ((None : option AId) = None → (b_stk < a_stk)%a → is_heap_address b_stk = false)
      as Hnot_heap.
    { intros _ Hlt. eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      apply withinBounds_true_iff. solve_addr. }

    (* Subseg ct2 csp cs1 cs0 *)
    iInstr "Hcode".
    { rewrite /isWithin; solve_addr. }

    (* GetE cs0 ct2 *)
    iInstr "Hcode".
    (* SetA csp ct2 cs0 *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame "∗ Hcode".
  Qed.

  Lemma switcher_call_block_6_spec
    pc_b pc_e pc_a
    wcs0 wpc_b :
    let switcher_instrs_6 := (switcher_instrs_n 6) in
    let len_switcher_6 := length switcher_instrs_6 in
    is_shadow_address pc_b = false ->
    is_heap_cap wpc_b = false ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_6)%a ->
    (pc_b + asm_label switcher_asm ".Lswitch_after_zero")%a = Some pc_a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    pc_b ↦ₐ□ wpc_b ∗
    codefrag_pers pc_a switcher_instrs_6 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_6)%a ∗
        cs0 ↦ᵣ wpc_b ∗
        pc_b ↦ₐ□ wpc_b ∗
        codefrag_pers pc_a switcher_instrs_6 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_6 len_switcher_6; subst switcher_instrs_6 len_switcher_6.
    iIntros (Hpc_b_shadow Hwpc_b_nonheap Hsub_reg Hpc_a)
      "(HPC & Hcs0 & #Hpc_b & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    offsets_compute.

    (* Auipcc cs0 ".Lswitcher_unseal_key". *)
    iInstr "Hcode".
    { instantiate (1 := pc_b); solve_addr. }

    (* CLoad cs0 cs0 0. *)
    iInstr "Hcode".

    iApply "Hpost"; iFrame "∗ Hcode Hpc_b".
  Qed.


  (** First instruction of block 7: unseal the entry point. *)
  Lemma switcher_call_block_7_unseal_spec
    pc_a wct1 :
    let switcher_instrs_7 := switcher_instrs_n 7 in
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length switcher_instrs_7)%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    codefrag_pers pc_a switcher_instrs_7 ∗
    ( ▷ ( ∀ wsb π,
        ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
        ⌜ get_tag_sealable wsb = true ⌝ ∗
        PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a ∗
        cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb @@? π ∗
        codefrag_pers pc_a switcher_instrs_7 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      ) ∧
    ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ ∗
      cs0 ↦ᵣ WSealRange true (true, true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
      ct1 ↦ᵣ - -∗
      trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 1)%a) ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_7; subst switcher_instrs_7.
    iIntros (Hsub_reg) "(HPC & Hcs0 & Hct1 & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed _ _ _ _ _ _ (pc_a ^+ 1)%a
             with "[$HPC $Hi $Hcs0 $Hct1]"); try done; try solve_pure.
    { pose proof ot_switcher_size; solve_addr. }
    iIntros "!>" (ret)
      "[(-> & HPC & Hi & Hcs0 & Hct1 & %Hnot_sealed) |
       [(%o & %wsb & %π & -> & HPC & Hi & Hcs0 & Hct1 & %Hwct1 & %Htag & %Hrange)
       |(%ot & %sb & %π & -> & HPC & Hi & Hcs0 & Hct1 & %Hwct1 & %Hinvalid)]]".
    { (* The operand is not sealed: it loses its tag, and the next CLoad
         fails. *)
      wp_pure.
      iClear "Hi".
      (* --- CLoad cs0 ct1 --- *)
      iInstr_fail "Hcode".
      { intros r sr m st s1 s2 _ Hr.
        rewrite /exec /= /lookup_reg /= Hr.
        destruct wct1 as [w0 π0]. destruct_word w0; by destruct s2. }
      iDestruct "Hpost" as "[_ Hfailed]".
      iTrap with "Hfailed".
      iPureIntro; intros (wsb & π & -> & _); done. }
    2: {
      (* The unsealed entry point is invalid: the next CLoad fails. *)
      simplify_eq.
      wp_pure.
      iClear "Hi".
      (* --- CLoad cs0 ct1 --- *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[_ Hfailed]".
      iTrap with "Hfailed".
      iPureIntro; intros (wsb & π0 & Heq & Htag); simplify_eq.
      rewrite Htag /= in Hinvalid.
      rewrite /withinBounds in Hinvalid; pose proof ot_switcher_size; solve_addr. }
    simplify_eq.
    apply withinBounds_le_addr in Hrange.
    assert (o = ot_switcher) as -> by solve_addr.
    iEval (rewrite unseal_global) in "Hct1".
    wp_pure.
    iClear "Hi".
    iDestruct "Hpost" as "[Hpost _]".
    iApply "Hpost"; iFrame "∗ Hcode"; done.
  Qed.

  (** Blocks 4-7: restrict the stack capability to the callee's stack, below
      the spill area, clear it, load the unsealing capability, and unseal
      the entry point [wct1]. The block faults when [wct1] is not a valid
      entry point sealed by the switcher. *)
  Lemma switcher_call_blocks_3_spec
    (b e a : Addr) (stk_mem : list LWord) (wcs0 wcs1 wct1 wct2 : LWord) :
    switcher_stk_bounds b e a ->
    disjoint_from_mmio b e ->
    disjoint_from_heap b e ->

    PC ↦ₚ switcher_label_pc ".Lswitch_stack_chop" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
    [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ [[ stk_mem ]] ∗
    b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
    ct1 ↦ᵣ wct1 ∗
    switcher_code ∗
    ▷ ( ∀ wsb π,
        ⌜ wct1 = WSealed ot_switcher wsb @@? π ⌝ ∗
        ⌜ get_tag_sealable wsb = true ⌝ ∗
        PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_decode_entry") ∗
        cs0 ↦ᵣ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
        (∃ wct2', ct2 ↦ᵣ wct2') ∗
        csp ↦ᵣ callee_csp b e a ∗
        [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
          [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
        b_switcher ↦ₐ□ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
        ct1 ↦ᵣ WSealable wsb @@? π ∗
        switcher_code -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
    ( ⌜ ¬ ∃ wsb π, wct1 = WSealed ot_switcher wsb @@? π ∧ get_tag_sealable wsb = true ⌝ -∗
      cs0 ↦ᵣ WSealRange true (true,true) Global ot_switcher (ot_switcher ^+ 1)%ot ot_switcher ∗
      (∃ wcs1', cs1 ↦ᵣ wcs1') ∗
      (∃ wct2', ct2 ↦ᵣ wct2') ∗
      csp ↦ᵣ callee_csp b e a ∗
      [[ stk_callee_b b a , stk_callee_e e a ]] ↦ₐ
        [[ region_addrs_zeroes (stk_callee_b b a) (stk_callee_e e a) ]] ∗
      ct1 ↦ᵣ - -∗
      trap_safe (switcher_pc (switcher_label_offset ".Lswitch_unseal_entry" + 1)) ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros ((Hba & Hba3 & Ha4) Hstk_mmio Hstk_heap)
      "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & Hstk & #Hb_switcher & Hct1 & #Hswitcher & Hpost)".
    rewrite /callee_csp.
    stk_unfold. change (4 - 1)%Z with 3%Z in Hba3.
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 4: restrict the stack capability *)
    switcher_focus_block (switcher_block ".Lswitch_stack_chop") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_4_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct2 $Hcsp $Hcode]"); [done| | |done|iNext].
    { solve_addr+Hba Hba3 Ha4. }
    { solve_addr+Hba Hba3 Ha4. }
    iIntros "(HPC & Hcs0 & Hcs1 & Hct2 & Hcsp & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 5: clear the callee's stack frame *)
    switcher_focus_block (switcher_block ".Lswitcher_zero_callee_stack") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hct2 $Hcs0 $Hstk]");
      try solve_pure.
    all: try solve_addr+Hba Hba3 Ha4.
    { pose proof (disjoint_from_mmio_shadow _ _ Hstk_mmio) as Hstk_shadow.
      rewrite /disjoint_from_shadow elem_of_disjoint in Hstk_shadow |- *.
      intros x Hx HR. eapply Hstk_shadow; last exact HR.
      apply elem_of_finz_seq_between. apply elem_of_finz_seq_between in Hx.
      solve_addr. }
    iIntros "!> (HPC & Hct2 & Hcs0 & _ & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 6: load the unsealing capability *)
    switcher_focus_block (switcher_block ".Lswitch_after_zero") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_6_spec with
      "[- $HPC $Hcs0 $Hb_switcher $Hcode]");
      [apply switcher_base_not_shadow|done|done| |].
    { offsets_compute; solve_addr. }
    iNext; iIntros "(HPC & Hcs0 & _ & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.

    (* Block 7: unseal the entry point *)
    switcher_focus_block (switcher_block ".Lswitch_unseal_entry") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_7_unseal_spec with
      "[- $HPC $Hcs0 $Hct1 $Hcode]"); first done.
    iSplit; cycle 1.
    { iIntros "(%Hnot_entry & Hcs0 & Hct1)".
      iDestruct "Hpost" as "[_ Hfailed]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 7) ^+ 1)%a =
                   (a_switcher_call ^+ (switcher_label_offset ".Lswitch_unseal_entry" + 1))%a);
        last (offsets_compute; solve_addr).
      iApply ("Hfailed" with "[//]"); iFrame. }
    iDestruct "Hpost" as "[Hpost _]".
    iNext; iIntros (wsb π) "(-> & %Htag & HPC & Hcs0 & Hct1 & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_decode_entry").
    iApply "Hpost"; iFrame "∗ Hswitcher Hb_switcher"; done.
  Qed.

End Switcher_Call_Blocks_3.
