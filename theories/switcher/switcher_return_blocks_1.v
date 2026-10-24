From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_return_states.

(** * Return routine, first part of block 13: pop the trusted stack

    Block 13 starts by reading [frameoffset] in the trusted stack. When the
    frame to pop is the entry frame of the thread, the thread exits (block
    19). Otherwise, it reads the topmost frame of the trusted stack, which
    contains the stack pointer of the caller, and pops it. *)

Section Switcher_Return_Blocks_1.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The test for a pushed frame, with [d] frames pushed above the entry
      frame: the thread exits when the frame to pop is the entry frame,
      i.e. when [d = 0]. *)
  Lemma switcher_return_block_13_load_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ)
    pc_b pc_e pc_a (d : nat)
    wctp wct0 wct2 :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    (* The distance from this block to the exit of the thread. *)
    let off_exit :=
      asm_label_offset switcher_asm "switcher_after_compartment_call"
        ".Lcommon_defer_irqs_and_thread_exit" in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (pc_a ^+ 6 + (off_exit - 6))%a = Some (pc_a ^+ off_exit)%a ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e pc_a ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
    ▷ ( ( ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 7)%a ∗
              ⌜ (0 < d)%nat ⌝ ∗
              ct0 ↦ᵣ WInt 1 )
            ∨
            ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ off_exit)%a ∗
              ⌜ d = 0 ⌝ ∗
              ct0 ↦ᵣ WInt 0 ) ) ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct2 ↦ᵣ WInt (tstack_frame_offset d) ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        codefrag_pers pc_a switcher_instrs_13 -∗
        WP Seq (Instr Executable) @ E {{ Φ }}
      )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    intros switcher_instrs_13 len_switcher_13 off_exit.
    subst switcher_instrs_13 len_switcher_13 off_exit.
    iIntros (Hsub_reg Hpc_exit)
      "(HPC & Hctp & Hct0 & Hct2 & Hmtdc & Hframeoffset & #Hcode & Hpost)".
    (* Compute the distance to the exit of the thread. *)
    offsets_compute.
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    pose proof trusted_stack_frames_fit as [n Hfit].
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).

    (* ReadSR ctp mtdc *)
    iInstr "Hcode".

    (* CLoad ct2 ctp 15 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { done. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.

    (* Mov ct0 16 *)
    iInstr "Hcode".

    (* Add ct2 ct2 (-3) *)
    iInstr "Hcode".

    (* Lt ct0 ct0 ct2 *)
    iInstr "Hcode".
    replace (tstack_frameoffset d + _)%Z with (tstack_frame_offset d) by (tstack_unfold; lia).
    destruct (_ <? tstack_frame_offset d)%Z eqn:Hnonempty; iEval (cbn) in "Hct0";
      destruct (decide (ct0 = cnull)) as [Hct0_null|_] in Hnonempty; [done| |done|].
    - assert (0 < d)%nat as Hd
        by (apply Z.ltb_lt in Hnonempty; tstack_unfold; lia).
      (* Jne 2 ct0 0 *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
      iLeft; iFrame; done.
    - assert (d = 0) as ->
        by (apply Z.ltb_ge in Hnonempty; tstack_unfold; lia).
      (* Jne 2 ct0 0 *)
      iInstr "Hcode".
      (* Jmp .Lcommon_defer_irqs_and_thread_exit *)
      iInstr "Hcode".
      iApply "Hpost"; iFrame "∗ Hcode".
      iRight; iFrame; done.
  Qed.

  (** Pop the topmost frame, at [a_tstk]: load the stack pointer of the
      caller, and decrement [frameoffset]. *)
  Lemma switcher_return_block_13_pop_spec
    pc_b pc_e pc_a
    (d : nat) a_tstk
    wct1 wcsp
    b_stk e_stk a_stk :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    let switcher_instrs_13 := switcher_instrs_n 13 in
    let len_switcher_13 := length switcher_instrs_13 in
    SubBounds pc_b pc_e pc_a (pc_a ^+ len_switcher_13)%a ->
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    is_heap_address b_stk = false ->

    PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 7)%a ∗
    ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt (tstack_frame_offset (S d)) ∗
    csp ↦ᵣ wcsp ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    a_csp ↦ₐ WCap true RWL Local b_stk e_stk a_stk ∗
    codefrag_pers pc_a switcher_instrs_13 ∗
    ▷ ( PC ↦ₚ WCap true XSRW_ Local pc_b pc_e (pc_a ^+ 10)%a ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct1 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
        ct2 ↦ᵣ WInt (tstack_frame_offset (S d)) ∗
        csp ↦ᵣ WCap true RWL Local b_stk e_stk a_stk ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        a_csp ↦ₐ WCap true RWL Local b_stk e_stk a_stk ∗
        codefrag_pers pc_a switcher_instrs_13 ∗
        £ 1
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
      )
    ⊢ WP Seq (Instr Executable)
        {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    intros switcher_instrs_13 len_switcher_13.
    subst switcher_instrs_13 len_switcher_13.
    iIntros (Hsub_reg Ha_tstk Ha_tstk_e Hb_stk_heap)
      "(HPC & Hctp & Hct1 & Hct2 & Hcsp & Hframeoffset & Ha_tstk & #Hcode & Hpost)".
    codefrag_facts "Hcode". clear H0.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    pose proof trusted_stack_disjoint_from_shadow as Hts_shadow.
    iEval (rewrite /TrustedStackFrame_offset_csp finz_add_0_default) in "Ha_tstk Hpost".
    assert ((b_trusted_stack + TrustedStack_offset_frameoffset)%a
            = Some (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a) as Hfo
      by (tstack_unfold; solve_addr).
    assert (is_heap_cap (WCap true RWL Local b_stk e_stk a_stk) = false) as Hwtstk_nonheap.
    { rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= Hb_stk_heap //. }

    (* Lea ct1 ctp ct2 *)
    iInstr "Hcode".

    (* CLoad csp ct1 0 *)
    iInstr "Hcode".
    { tstk_not_shadow Hts_shadow. }
    { split; auto. rewrite /withinBounds. tstack_unfold; solve_addr. }
    rewrite lload_word_RWL.

    (* Store ctp ct2 21 *)
    iInstr "Hcode" with "Hlc".
    { tstk_not_shadow Hts_shadow. }
    { rewrite /withinBounds; tstack_unfold; solve_addr. }
    rewrite lstore_word_isWL; last reflexivity.

    assert (tstack_frame_offset (S d) = tstack_frameoffset d) as Hpopped
      by (tstack_unfold; lia).
    iEval (rewrite Hpopped) in "Hframeoffset".
    iApply "Hpost". iFrame "∗ Hcode".
  Qed.

  (** Pop the topmost frame of the trusted stack, at [a_tstk], which
      contains the stack pointer [WCap true RWL Local b e (stk_saved_a a)] of
      the caller, above [d] frames. *)
  Lemma switcher_return_blocks_1_spec
    (d : nat) (a_tstk b e a : Addr) (wctp wct0 wct1 wct2 wcsp : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    let a_csp := (a_tstk ^+ TrustedStackFrame_offset_csp)%a in
    (b_trusted_stack + tstack_frame_offset (S d))%a = Some a_tstk ->
    (a_tstk + TrustedStackFrame_size <= e_trusted_stack)%Z ->
    is_heap_address b = false ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    csp ↦ᵣ wcsp ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset (S d)) ∗
    a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_pc (switcher_label_offset ".Lswitcher_restore_spill") ∗
        ctp ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        ct0 ↦ᵣ WInt 1 ∗
        ct1 ↦ᵣ WCap true RWL Global b_trusted_stack e_trusted_stack a_tstk ∗
        ct2 ↦ᵣ WInt (tstack_frame_offset (S d)) ∗
        csp ↦ᵣ WCap true RWL Local b e (stk_saved_a a) ∗
        mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset d) ∗
        a_csp ↦ₐ WCap true RWL Local b e (stk_saved_a a) ∗
        switcher_code ∗
        £ 1 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    intros a_frameoffset a_csp; subst a_frameoffset a_csp.
    iIntros (Ha_tstk Ha_tstk_e Hb_heap)
      "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Ha_tstk
      & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_13.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_return_block_13_load_spec with
      "[- $HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hcode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "([(HPC & _ & Hct0) | (_ & %Hcontra & _)]
                    & Hctp & Hct2 & Hmtdc & Hframeoffset & _)"; last done.
    iApply (switcher_return_block_13_pop_spec with
      "[- $HPC $Hctp $Hct1 $Hct2 $Hcsp $Hframeoffset $Ha_tstk $Hcode]");
      [done|done|done|done|].
    iNext; iIntros "(HPC & Hctp & Hct1 & Hct2 & Hcsp & Hframeoffset & Ha_tstk & _ & Hlc)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lswitcher_restore_spill").
    iApply "Hpost"; iFrame "∗ Hswitcher".
  Qed.

  (** Block 19: the thread exits, with interrupts disabled. *)
  Lemma switcher_exit_block_spec (E : coPset) (Φ : griotte_lang.val → iProp Σ) :
    PC ↦ₚ switcher_label_pc ".Lcommon_defer_irqs_and_thread_exit" ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lcommon_thread_exit"
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    iIntros "(HPC & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lcommon_defer_irqs_and_thread_exit") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    codefrag_facts "Hcode".
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    (* Halt *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lcommon_thread_exit").
    iApply wp_value_fupd.
    by iMod ("Hpost" with "HPC").
  Qed.

  (** When the frame to pop is the entry frame, the thread exits. *)
  Lemma switcher_return_blocks_1_exit_spec
    (E : coPset) (Φ : griotte_lang.val → iProp Σ) (wctp wct0 wct2 : LWord) :
    let a_frameoffset := (b_trusted_stack ^+ TrustedStack_offset_frameoffset)%a in
    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    ctp ↦ᵣ wctp ∗
    ct0 ↦ᵣ wct0 ∗
    ct2 ↦ᵣ wct2 ∗
    mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
    a_frameoffset ↦ₐ WInt (tstack_frameoffset 0) ∗
    switcher_code ∗
    ▷ ( mtdc ↦ₛᵣ WCap true RWL Global b_trusted_stack e_trusted_stack b_trusted_stack ∗
        a_frameoffset ↦ₐ WInt (tstack_frameoffset 0)
        ={E}=∗
        Φ HaltedV )
    ⊢ WP Seq (Instr Executable) @ E {{ Φ }}.
  Proof.
    intros a_frameoffset; subst a_frameoffset.
    iIntros "(HPC & Hctp & Hct0 & Hct2 & Hmtdc & Hframeoffset & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size. pose proof switcher_call_entry_point.
    rewrite switcher_return_block_13.
    iAssert switcher_code as "Hswitcher_code"; first iFrame "Hswitcher".
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block "switcher_after_compartment_call") "Hswitcher" as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_return_block_13_load_spec with
      "[- $HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hcode]");
      [done|offsets_compute; solve_addr|].
    iNext; iIntros "([(_ & %Hcontra & _) | (HPC & _ & Hct0)]
                    & Hctp & Hct2 & Hmtdc & Hframeoffset & _)"; first lia.
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    switcher_change_pc (switcher_label_offset ".Lcommon_defer_irqs_and_thread_exit").
    iApply (switcher_exit_block_spec with "[$HPC $Hswitcher_code Hpost Hmtdc Hframeoffset]").
    iIntros "!> _".
    iApply ("Hpost" with "[$Hmtdc $Hframeoffset]").
  Qed.

End Switcher_Return_Blocks_1.
