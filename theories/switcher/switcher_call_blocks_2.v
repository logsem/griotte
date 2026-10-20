From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import switcher_call_states.

(** * Call routine, blocks 2-3: spill and push on the trusted stack

    Block 2 spills the callee-save registers on the caller's stack, and
    block 3 pushes the caller's stack pointer on the trusted stack. When the
    trusted stack is exhausted, the execution jumps to block 17 (see
    [switcher_call_blocks_5]). *)

Section Switcher_Call_Blocks_2.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The stack is not a shadow-table address. *)
  #[local] Ltac stk_not_shadow H :=
    eapply disjoint_from_shadow_not_in;
    [exact (disjoint_from_mmio_shadow _ _ H) | rewrite /withinBounds; solve_addr].

  (** Block 2: spill the callee-save registers at [a_stk], ..., [a_stk + 3],
      the furthest cell first. When that first store faults, nothing is
      written. When it succeeds and the cursor is below the base, the store
      at [a_stk] faults, after [cgp] has been written at [a_stk + 3]. *)
  Lemma switcher_call_block_2_spec
    b_stk e_stk a_stk
    pc_b pc_e pc_a
    wcs0 wcs1 wcra wcgp
    stk_mem :
    let switcher_instrs_2 := (switcher_instrs_n 2) in
    let len_switcher_2 := length switcher_instrs_2 in
    disjoint_from_mmio b_stk e_stk ->
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_2)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
    [[a_stk,e_stk]]↦ₐ[[stk_mem]] ∗
    codefrag_pers pc_a switcher_instrs_2 ∗
    ( ▷ ( ∀ stk_mem',
          ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_2)%a ∗
            cs0 ↦ᵣ wcs0 ∗
            cs1 ↦ᵣ wcs1 ∗
            cra ↦ᵣ wcra ∗
            cgp ↦ᵣ wcgp ∗
            csp ↦ᵣ WCap true RWL Local b_stk e_stk (a_stk ^+ 4)%a ∗
            a_stk ↦ₐ wcs0 ∗
            (a_stk ^+ 1)%a ↦ₐ wcs1 ∗
            (a_stk ^+ 2)%a ↦ₐ wcra ∗
            (a_stk ^+ 3)%a ↦ₐ wcgp ∗
            [[(a_stk ^+ 4)%a,e_stk]]↦ₐ[[stk_mem']] ∗
            ⌜ (b_stk <= a_stk)%a ∧ (b_stk <= (a_stk ^+ 3)%a < e_stk)%a ∧ is_Some (a_stk + 4)%a ⌝ ∗
            ⌜ stk_mem' = drop 4 stk_mem ⌝ ∗
            codefrag_pers pc_a switcher_instrs_2 -∗
            WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
          )
      ) ∧
      ( ∀ a stk_mem',
        ⌜ (a = pc_a ∧ stk_mem' = stk_mem) ∨
          ((a_stk < b_stk)%a ∧ a = (pc_a ^+ 1)%a ∧ stk_mem' = <[3 := wcgp]> stk_mem) ⌝ -∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        [[a_stk,e_stk]]↦ₐ[[stk_mem']] -∗
        trap_safe (WCap true XSRW_ Local pc_b pc_e a) ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros switcher_instrs_2 len_switcher_2; subst switcher_instrs_2 len_switcher_2.
    iIntros (Hstk_shadow Hsub_reg) "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.

    (* The first store faults: nothing is written *)
    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk ∧ (a_stk + 3)%a = Some (a_stk ^+ 3)%a)%a)
      as [ [Hastk3_inbounds Hastk3] | Hastk3_out]; cycle 1.
    { iDestruct "Hpost" as "[_ Hfailed]".
      destruct (a_stk + 3)%a as [a_stk3|] eqn:Hastk3.
      - (* Store csp cgp 3 *)
        iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcgp $Hcsp]" as "(HPC & Hcgp & Hcsp)".
        { assert (¬ (b_stk <= a_stk3 < e_stk)%a) as Hastk3_out'
            by (intros ?; apply Hastk3_out; split; [solve_addr|f_equal; solve_addr]).
          rewrite /withinBounds; solve_addr. }
        iTrap with "Hfailed".
      - (* Store csp cgp 3 *)
        iInstrApply "Hcode" wp_store_fail_reg_overflow_imm with "[$HPC $Hcgp $Hcsp]" as "(HPC & Hcgp & Hcsp)".
        iTrap with "Hfailed". }

    (* Split the four cells off the stack *)
    destruct stk_mem as [|w0 [|w1 [|w2 [|w3 stk_mem] ] ] ];
      try (exfalso; cbn in Hstklen; rewrite /finz.dist in Hstklen; solve_addr).
    iDestruct (region_pointsto_cons _ (a_stk ^+ 1)%a with "Hstk") as "[Ha_stk Hstk]"; [solve_addr..|].
    iDestruct (region_pointsto_cons _ (a_stk ^+ 2)%a with "Hstk") as "[Ha_stk1 Hstk]"; [solve_addr..|].
    iDestruct (region_pointsto_cons _ (a_stk ^+ 3)%a with "Hstk") as "[Ha_stk2 Hstk]"; [solve_addr..|].
    iDestruct (region_pointsto_cons _ (a_stk ^+ 4)%a with "Hstk") as "[Ha_stk3 Hstk]"; [solve_addr..|].

    (* Store csp cgp 3 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_shadow. }
    { rewrite /withinBounds. solve_addr. }

    (* The cursor is below the base: the store at [a_stk] faults *)
    destruct (decide (b_stk <= a_stk)%a) as [Hastk_inbounds|Hastk_below]; cycle 1.
    { iDestruct "Hpost" as "[_ Hfailed]".
      (* Store csp cs0 0 *)
      iInstrApply "Hcode" wp_store_fail_reg with "[$HPC $Hcs0 $Hcsp]" as "(HPC & Hcs0 & Hcsp)".
      { rewrite /withinBounds; solve_addr. }
      repeat rewrite lstore_word_isWL; try reflexivity.
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr..|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr..|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr..|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr..|].
      iTrap with "Hfailed".
      right; split; [solve_addr|split; [solve_addr|done] ]. }

    (* Store csp cs0 0 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_shadow. }
    { rewrite /withinBounds. solve_addr. }

    assert ((a_stk + 1)%a = Some (a_stk ^+ 1)%a) as Hastk1 by solve_addr.
    assert ((a_stk + 2)%a = Some (a_stk ^+ 2)%a) as Hastk2 by solve_addr.
    assert ((a_stk + 4)%a = Some (a_stk ^+ 4)%a) as Hastk4 by solve_addr.

    (* Store csp cs1 1 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_shadow. }
    { rewrite /withinBounds. solve_addr. }

    (* Store csp cra 2 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_shadow. }
    { rewrite /withinBounds. solve_addr. }

    (* Lea csp 4 *)
    iInstr "Hcode".

    repeat rewrite lstore_word_isWL; try reflexivity.
    iDestruct "Hpost" as "[Hpost _]".
    iApply ("Hpost" $! stk_mem). iFrame "∗ Hcode".
    iPureIntro; repeat split; solve_addr.
  Qed.

  (** Block 3: when [frameoffset] is below the length of the trusted stack,
      push a frame at [frameoffset], holding the stack pointer [wstk] of the
      caller, and increment [frameoffset]. The call-stack has [d] frames,
      the topmost one at [a_tstk]. *)
  Lemma switcher_call_block_3_spec
    pc_b pc_e pc_a
    (d : nat) a_tstk tstk_next
    wcs0 wcs1 wctp wct2 wstk :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    let switcher_instrs_3 := (switcher_instrs_n 3) in
    let len_switcher_3 := length switcher_instrs_3 in
    (* The distance from this block to the block of the exhausted trusted stack. *)
    let off_exhausted :=
      asm_label_offset switcher_asm ".Lswitcher_trusted_stack_push" ".Lswitch_trusted_stack_exhausted" in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_3)%a ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->

    (pc_a ^+ 7 +
       asm_label_offset switcher_asm ".Lswitcher_trusted_stack_full"
         ".Lswitch_trusted_stack_exhausted")%a =
      Some (pc_a ^+ off_exhausted)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ wstk ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    codefrag_pers pc_a switcher_instrs_3 ∗
    ▷  (
        (∃ tstk_next',
            ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
            ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
            PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ len_switcher_3)%a ∗
            cs0 ↦ᵣ WInt (tstack_frameoffset (S d)) ∗
            cs1 ↦ᵣ WInt (tstack_frameoffset d) ∗
            ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_next ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            csp ↦ᵣ wstk ∗
            mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
            a_csp ↦ₐ wstk ∗
            a_export_table ↦ₐ WInt 0 ∗
            a_error_count ↦ₐ WInt 0 ∗
            [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]] ∗
            codefrag_pers pc_a switcher_instrs_3 ∗
            £ 2
        )
        ∨
          (
            PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ off_exhausted)%a ∗
            cs0 ↦ᵣ WInt 0 ∗
            cs1 ↦ᵣ WInt b_trusted_stack ∗
            ctp ↦ᵣ WInt (tstack_frameoffset d) ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            csp ↦ᵣ wstk ∗
            mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
            [[ a_next, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
            codefrag_pers pc_a switcher_instrs_3
          )
          -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    intros switcher_instrs_3 len_switcher_3 off_exhausted;
      subst switcher_instrs_3 len_switcher_3 off_exhausted.
    iIntros (Hsub_reg Ha_tstk Ha_tstk_e Hpc_fail)
      "(HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hmtdc & Hframeoffset & Htstk & #Hcode & Hpost)".
    (* Compute the distance to the block of the exhausted trusted stack. *)
    offsets_compute.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).

    (* ReadSR ct2 mtdc *)
    iInstr "Hcode".

    (* CLoad ctp ct2 15 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.

    (* GetE cs0 ct2 *)
    iInstr "Hcode".

    (* GetB cs1 ct2 *)
    iInstr "Hcode".

    (* Sub cs0 cs0 cs1 *)
    iInstr "Hcode".

    (* Lt cs0 ctp cs0 *)
    iInstr "Hcode".

    destruct (tstack_frameoffset d <? e_trusted_stack - b_trusted_stack)%Z eqn:Hroom
    ; iEval (cbn) in "Hcs0"
    ; cycle 1.
    {
      (* Jnz 2 cs0 *)
      iInstr "Hcode".
      (* Jmp 94 *)
      iInstr "Hcode".
      iApply "Hpost".
      iRight.
      iFrame "∗ Hcode".
    }
    apply Z.ltb_lt in Hroom.

    (* Jnz 2 cs0 *)
    iInstr "Hcode" with "Hlc".

    (* Mov cs1 ctp *)
    iInstr "Hcode" with "Hlc".

    (* Mov ctp ct2 *)
    iInstr "Hcode".

    (* Lea ctp cs1 *)
    iInstr "Hcode".
    { instantiate (1 := (a_tstk ^+ TrustedStackFrame_size)%a). tstack_unfold; solve_addr. }

    (* Split the new frame off the unused part of the trusted stack *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next as [|w0 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    destruct tstk_next as [|w1 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    destruct tstk_next as [|w2 tstk_next];
      first (exfalso; cbn in Hlen; rewrite /finz.dist in Hlen; tstack_unfold; solve_addr).
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_offset_calleeExportTable)%a
                 with "Htstk") as "[Hframe_csp Htstk]"; [tstack_unfold; solve_addr..|].
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_offset_errorHandlerCount)%a
                 with "Htstk") as "[Hframe_export_table Htstk]"; [tstack_unfold; solve_addr..|].
    iDestruct (region_pointsto_cons _
                 ((a_tstk ^+ TrustedStackFrame_size) ^+ TrustedStackFrame_size)%a
                 with "Htstk") as "[Hframe_error_count Htstk]"; [tstack_unfold; solve_addr..|].
    assert (((a_tstk ^+ TrustedStackFrame_size) + TrustedStackFrame_offset_calleeExportTable)%a
            = Some ((a_tstk ^+ TrustedStackFrame_size)
                    ^+ TrustedStackFrame_offset_calleeExportTable)%a)
      as Ha_export_table by (tstack_unfold; solve_addr).
    assert (((a_tstk ^+ TrustedStackFrame_size) + TrustedStackFrame_offset_errorHandlerCount)%a
            = Some ((a_tstk ^+ TrustedStackFrame_size)
                    ^+ TrustedStackFrame_offset_errorHandlerCount)%a)
      as Ha_error_count by (tstack_unfold; solve_addr).

    (* Store ctp csp 0 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }

    (* Store ctp 0 2 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }

    (* Store ctp 0 1 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }

    (* CLoad cs0 ct2 15 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.

    (* Add cs0 cs0 3 *)
    iInstr "Hcode".

    (* Store ct2 cs0 15 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }

    repeat rewrite lstore_word_isWL; try reflexivity.
    replace (tstack_frameoffset d + _)%Z with (tstack_frameoffset (S d))
      by (tstack_unfold; lia).
    iApply "Hpost"; iLeft; iExists tstk_next; iFrame "∗ Hcode".
    iPureIntro; tstack_unfold; split; solve_addr.
  Qed.


  (** Blocks 2-3: spill the callee-save registers on the caller's stack
      [[a, e)], and push a frame with the stack pointer on the trusted
      stack, whose topmost frame is at [a_tstk]. The spill faults when the
      four cells do not fit in [[a, e)]: at its first store, with nothing
      written, or, when the cursor is below the base, at its second store,
      with [cgp] written at [a + 3]. *)
  Lemma switcher_call_blocks_2_spec
    (b e a : Addr) (stk_mem : list LWord)
    (wcs0 wcs1 wcra wcgp wctp wct2 : LWord)
    (d : nat) (a_tstk : Addr) (tstk_next : list LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_next := (a_tstk ^+ TrustedStackFrame_size)%a in
    let a_free := (a_next ^+ TrustedStackFrame_size)%a in
    let a_csp := (a_next ^+ TrustedStackFrame_offset_csp)%a in
    let a_export_table := (a_next ^+ TrustedStackFrame_offset_calleeExportTable)%a in
    let a_error_count := (a_next ^+ TrustedStackFrame_offset_errorHandlerCount)%a in
    disjoint_from_mmio b e ->
    (b_trusted_stack + tstack_frame_offset d)%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_entry_first_spill" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    cra ↦ᵣ wcra ∗
    cgp ↦ᵣ wcgp ∗
    ctp ↦ᵣ wctp ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    [[ a , e ]] ↦ₐ [[ stk_mem ]] ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ∗
    switcher_code ∗
    ▷ ( ⌜ switcher_stk_bounds b e a ⌝ ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        csp ↦ᵣ WCap true RWL Local b e (a ^+ 4)%a ∗
        switcher_stk_cells a wcs0 wcs1 wcra wcgp ∗
        [[ (a ^+ 4)%a , e ]] ↦ₐ [[ drop 4 stk_mem ]] ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        switcher_code ∗
        ( ( ⌜ (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_next ⌝ ∗
            ⌜ (a_next + TrustedStackFrame_size <= e_trusted_stack)%Z ⌝ ∗
            PC ↦ₚ switcher_label_pc ".Lswitcher_chop_stack" ∗
            cs0 ↦ᵣ WInt (tstack_frameoffset (S d)) ∗
            cs1 ↦ᵣ WInt (tstack_frameoffset d) ∗
            ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_next ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
            a_csp ↦ₐ
              WCap true RWL Local b e (a ^+ 4)%a ∗
            a_export_table ↦ₐ WInt 0 ∗
            a_error_count ↦ₐ WInt 0 ∗
            (∃ tstk_next',
                [[ a_free, e_trusted_stack ]] ↦ₐ [[ tstk_next' ]]) ∗
            £ 2 )
          ∨
          ( PC ↦ₚ switcher_label_pc ".Lswitch_trusted_stack_exhausted" ∗
            cs0 ↦ᵣ WInt 0 ∗
            cs1 ↦ᵣ WInt b_trusted_stack ∗
            ctp ↦ᵣ WInt (tstack_frameoffset d) ∗
            ct2 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
            a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
            [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] ) )
        -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
    ( ∀ a_f stk_mem',
        ⌜ (a_f = (a_switcher_call ^+ switcher_label_offset ".Lswitcher_entry_first_spill")%a ∧
           stk_mem' = stk_mem) ∨
          ((a < b)%a ∧
           a_f = (a_switcher_call ^+ (switcher_label_offset ".Lswitcher_entry_first_spill" + 1))%a ∧
           stk_mem' = <[3 := wcgp]> stk_mem) ⌝ -∗
        cs0 ↦ᵣ wcs0 ∗
        cs1 ↦ᵣ wcs1 ∗
        cra ↦ᵣ wcra ∗
        cgp ↦ᵣ wcgp ∗
        ctp ↦ᵣ wctp ∗
        ct2 ↦ᵣ wct2 ∗
        csp ↦ᵣ WCap true RWL Local b e a ∗
        [[ a , e ]] ↦ₐ [[ stk_mem' ]] ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        [[ a_next , e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
        trap_safe (WCap true XSRW_ Local b_switcher e_switcher a_f) ⊤
          (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    subst a_frameoffset a_next a_free a_csp a_export_table a_error_count.
    iIntros (Hstk_mmio Ha_tstk Ha_tstk_e)
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hctp & Hct2 & Hcsp & Hstk
      & Hmtdc & Hframeoffset & Htstk & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".

    (* Block 2: spill the callee-save registers *)
    switcher_focus_block (switcher_block ".Lswitcher_entry_first_spill") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hcode]"); [done|done|].
    iSplit; cycle 1.
    { iIntros (a_f stk_mem' Ha_f) "(Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp & Hstk)".
      iDestruct "Hpost" as "[_ Hfailed]".
      iApply ("Hfailed" with "[] [$]").
      iPureIntro; offsets_compute.
      destruct Ha_f as [ [-> ->] | (? & -> & ->) ]; [left | right]; repeat split; solve_addr. }
    iDestruct "Hpost" as "[Hpost _]".
    iNext; iIntros (stk_mem')
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp
      & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hstk & %Hbounds & -> & _)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    destruct Hbounds as (Hba & Hba3 & [a4 Ha4]).
    assert ((a + 4)%a = Some (a ^+ 4)%a) as Ha4' by solve_addr.

    (* Block 3: push a frame on the trusted stack *)
    switcher_focus_block (switcher_block ".Lswitcher_trusted_stack_push") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_call_block_3_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hctp $Hct2 $Hcsp $Hmtdc $Hframeoffset $Htstk $Hcode]");
      [done|done|done|offsets_compute; solve_addr|].
    iNext.
    iIntros "[
      (%tstk_next' & %Ha_frame & %Ha_frame_e & HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hmtdc
        & Hframeoffset & Hframe_csp & Hframe_tbl & Hframe_cnt & Htstk & _ & Hlc)
      |
      (HPC & Hcs0 & Hcs1 & Hctp & Hct2 & Hcsp & Hmtdc & Hframeoffset & Htstk & _)
    ]"; unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    - switcher_change_pc (switcher_label_offset ".Lswitcher_chop_stack").
      iApply "Hpost"; iFrame "∗ Hswitcher".
      iSplit; first (iPureIntro; split; [solve_addr|split; [solve_addr|done] ]).
      iLeft; iFrame "∗ %".
    - switcher_change_pc (switcher_label_offset ".Lswitch_trusted_stack_exhausted").
      iApply "Hpost"; iFrame "∗ Hswitcher".
      iSplit; first (iPureIntro; split; [solve_addr|split; [solve_addr|done] ]).
      iRight; iFrame.
  Qed.

  (** Block 2 faults at its first store when the furthest cell of the spill
      is not within the bounds of the stack pointer: nothing is written. *)
  Lemma switcher_call_blocks_2_fail_spec (wcsp wcgp : LWord) :
    switcher_csp_checked wcsp ->
    (∀ b e a a3, wcsp.(lw) = WCap true RWL Local b e a -> (a + 3)%a = Some a3 ->
                 (a3 < b)%a ∨ (e <= a3)%a) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_entry_first_spill" ∗
    csp ↦ᵣ wcsp ∗
    cgp ↦ᵣ wcgp ∗
    switcher_code ∗
    ( csp ↦ᵣ wcsp ∗
      cgp ↦ᵣ wcgp -∗
      trap_safe (switcher_label_pc ".Lswitcher_entry_first_spill") ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hchecked Hnot_stk) "(HPC & Hcsp & Hcgp & #Hswitcher & Hfailed)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_entry_first_spill") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    destruct (is_cap wcsp.(lw)) eqn:Hcap; cycle 1.
    { (* Store csp cgp 3 *)
      iInstrApply "Hcode" wp_store_fail_reg_not_cap_lword_imm with "[$HPC $Hcgp $Hcsp]" as "(HPC & Hcgp & Hcsp)".
      iTrap with "Hfailed". }
    destruct wcsp as [ [| [t p g b e a|] | | ] π]; cbn in Hcap; try discriminate.
    destruct t.
    2: {
      (* Store csp cgp 3 *)
      iInstr_fail "Hcode".
      iTrap with "Hfailed". }
    destruct (switcher_csp_checked_cap _ _ _ _ _ _ Hchecked) as [-> ->].
    destruct (a + 3)%a as [a3|] eqn:Ha3.
    - specialize (Hnot_stk b e a a3 eq_refl Ha3).
      (* Store csp cgp 3 *)
      iInstrApply "Hcode" wp_store_fail_reg_imm with "[$HPC $Hcgp $Hcsp]" as "(HPC & Hcgp & Hcsp)".
      { destruct Hnot_stk; rewrite /withinBounds; solve_addr. }
      iTrap with "Hfailed".
    - (* Store csp cgp 3 *)
      iInstrApply "Hcode" wp_store_fail_reg_overflow_imm with "[$HPC $Hcgp $Hcsp]" as "(HPC & Hcgp & Hcsp)".
      iTrap with "Hfailed".
  Qed.

  (** Block 2 faults at its second store when the stack pointer is below its
      base and the furthest cell of the spill is within its bounds: [cgp] is
      written at [a + 3]. *)
  Lemma switcher_call_blocks_2_below_spec (b e a : Addr) (w3 wcs0 wcgp : LWord) :
    disjoint_from_mmio b e ->
    (a < b)%a ->
    (b <= a ^+ 3 < e)%a ->
    (a + 3)%a = Some (a ^+ 3)%a ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_entry_first_spill" ∗
    csp ↦ᵣ WCap true RWL Local b e a ∗
    cs0 ↦ᵣ wcs0 ∗
    cgp ↦ᵣ wcgp ∗
    (a ^+ 3)%a ↦ₐ w3 ∗
    switcher_code ∗
    ( csp ↦ᵣ WCap true RWL Local b e a ∗
      cs0 ↦ᵣ wcs0 ∗
      cgp ↦ᵣ wcgp ∗
      (a ^+ 3)%a ↦ₐ wcgp -∗
      trap_safe (switcher_pc (switcher_label_offset ".Lswitcher_entry_first_spill" + 1)) ⊤
        (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hstk_shadow Hab Ha3_inbounds Ha3) "(HPC & Hcsp & Hcs0 & Hcgp & Ha3 & #Hswitcher & Hfailed)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lswitcher_entry_first_spill") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    (* Store csp cgp 3 *)
    iInstr "Hcode".
    { stk_not_shadow Hstk_shadow. }
    { rewrite /withinBounds. solve_addr. }
    (* Store csp cs0 0 *)
    iInstrApply "Hcode" wp_store_fail_reg with "[$HPC $Hcs0 $Hcsp]" as "(HPC & Hcs0 & Hcsp)".
    { rewrite /withinBounds; solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.
    switcher_change_pc (switcher_label_offset ".Lswitcher_entry_first_spill" + 1)%Z.
    iTrap with "Hfailed".
  Qed.

End Switcher_Call_Blocks_2.
