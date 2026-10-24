From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_handler
  clear_registers_spec.

(** * Exception path, blocks 33-34: the invocation of a handler and its return

    Block 33 ([.Lhandle_error_handler_invoke]) enables interrupts, clears
    every register but the handler's return sentry, stack, globals and
    three arguments ([zero_all_registers_except_asm], [cnull] included),
    and calls the handler's PC in [cra] with [cjalr cra, cra]
    ([.Lhandle_error_handler_cjalr]): the link is the return sentry of the
    handler, [handler_return_sentry]. The [cjalr] faults when the computed
    word is not a valid target.

    Block 34 ([.Lhandle_error_handler_return]), the handler's return,
    disables interrupts; a request to unwind ([ca0] not zero) forces the
    unwind. Otherwise, the switcher continues at block 35
    ([.Lhandle_error_install_context]), which installs the context of the
    handler. *)

Section Switcher_Exception_Blocks_6.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** Block 33: the invocation. *)
  Lemma switcher_instrs_33_split :
    switcher_instrs_n 33 =
      encodeInstrsW [SetMIE InterruptEnabled] ++
      rclear_instrs' registers_handler_invoke ++
      encodeInstrsW [Jalr cra cra].
  Proof. reflexivity. Qed.

  #[local] Lemma switcher_exception_block_33_spec_aux
    (pc_a : Addr) (wcra : LWord) (rmap : LReg) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 33))%a ->
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    cra ↦ᵣ wcra ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    codefrag_pers pc_a (switcher_instrs_n 33) ∗
    ▷ ( ( ⌜jalr_target_ok cra cra wcra.(lw) = true⌝ -∗
          ∀ (mie : InterruptStatus) (rmap' : LReg),
          ⌜dom rmap' = dom rmap⌝ -∗
          PC ↦ₚ lupdatePcPerm wcra ∗
          cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher (pc_a ^+ 12)%a ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
          codefrag_pers pc_a (switcher_instrs_n 33) -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜jalr_target_ok cra cra wcra.(lw) = false⌝ -∗
          ∀ rmap' : LReg,
          ⌜dom rmap' = dom rmap⌝ -∗
          cra ↦ᵣ wcra ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) -∗
          trap_safe (WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ 11)%a) ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hdom) "(HPC & Hcra & Hrmap & #Hcode & Hpost)".
    iPoseProof "Hcode" as "Hcode_all".
    iEval (rewrite switcher_instrs_33_split) in "Hcode_all".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hclear _]".
    codefrag_facts "Hcode".
    assert (length (switcher_instrs_n 33) = 12%nat) as Hlen33 by reflexivity.
    rewrite Hlen33 in Hsub.
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* SetMIE InterruptEnabled *)
    iInstr "Hcode".
    (* The clearing of the registers *)
    rewrite (_ : (pc_a ^+ length (encodeInstrsW [SetMIE InterruptEnabled]))%a = (pc_a ^+ 1)%a);
      last (cbn; solve_addr).
    rewrite -registers_except_handler_invoke.
    iApply (zero_all_registers_except_spec with "[- $HPC $Hrmap $Hclear]").
    { by rewrite registers_except_handler_invoke. }
    { done. }
    { rewrite registers_except_handler_invoke /=. revert Hsub. rewrite /SubBounds. solve_addr. }
    { exact Hdom. }
    iNext; iIntros "(%rmap' & %Hdom' & HPC & Hrmap & _)".
    rewrite registers_except_handler_invoke.
    rewrite (_ : ((pc_a ^+ 1) ^+ length (rclear_instrs' registers_handler_invoke))%a =
                 (pc_a ^+ 11)%a); last (cbn; solve_addr).
    destruct (jalr_target_ok cra cra wcra.(lw)) eqn:Htgt.
    - (* Jalr cra cra *)
      iInstr "Hcode".
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" $! eq_refl mie rmap' with "[] [-]");
        first (iPureIntro; by rewrite Hdom' Hdom).
      iFrame "∗ Hcode".
    - (* Jalr cra cra *)
      iInstr_fail "Hcode".
      iDestruct "Hpost" as "[_ Hfailed]".
      iSpecialize ("Hfailed" $! eq_refl rmap' with "[]");
        first (iPureIntro; by rewrite Hdom' Hdom).
      iTrap with "Hfailed".
  Qed.

  (** Block 34: the handler's return. *)
  #[local] Lemma switcher_exception_block_34_spec_aux (pc_a : Addr) (wca0 : LWord) :
    SubBounds b_switcher e_switcher pc_a (pc_a ^+ length (switcher_instrs_n 34))%a ->
    (pc_a + (-144))%a = Some (pc_a ^+ (-144))%a ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher pc_a ∗
    ca0 ↦ᵣ wca0 ∗
    codefrag_pers pc_a (switcher_instrs_n 34) ∗
    ▷ ( ∀ off : Z,
        ⌜(nonZero wca0.(lw) = true ∧ off = (-144)%Z) ∨
         (nonZero wca0.(lw) = false ∧ off = 2%Z)⌝ -∗
        PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher (pc_a ^+ off)%a ∗
        ca0 ↦ᵣ wca0 -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hsub Hunwind) "(HPC & Hca0 & #Hcode & Hpost)".
    codefrag_facts "Hcode".
    rewrite /switcher_instrs_n /assembled_switcher_n.
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    destruct (nonZero wca0.(lw)) eqn:Hnz.
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hca0]" as "(HPC & Hca0)".
      { transitivity (Some (pc_a ^+ (-144))%a); solve_addr. }
      iApply ("Hpost" $! (-144)%Z with "[] [$]"). iPureIntro. by left.
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" wp_jnez_success_next_any with "[$HPC $Hca0]" as "(HPC & Hca0)".
      iApply ("Hpost" $! 2%Z with "[] [$]"). iPureIntro. by right.
  Qed.

  (** Block 33, from [.Lhandle_error_handler_invoke]: with interrupts
      enabled, the registers of [rmap] (all but [cra], [csp], [cgp], [ca0],
      [ca1] and [ca2]) are cleared, and the [cjalr] calls the word in [cra]
      with the handler's return sentry as link, or faults. *)
  Lemma switcher_handler_invoke_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] ->

    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_invoke" ∗
    cra ↦ᵣ wcra ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) ∗
    switcher_code ∗
    ▷ ( ( ⌜jalr_target_ok cra cra wcra.(lw) = true⌝ -∗
          ∀ (mie : InterruptStatus) (rmap' : LReg),
          ⌜dom rmap' = dom rmap⌝ -∗
          PC ↦ₚ lupdatePcPerm wcra ∗
          cra ↦ᵣ handler_return_sentry mie ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜jalr_target_ok cra cra wcra.(lw) = false⌝ -∗
          ∀ rmap' : LReg,
          ⌜dom rmap' = dom rmap⌝ -∗
          cra ↦ᵣ wcra ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜w = WInt 0⌝) ∗
          switcher_code -∗
          trap_safe (switcher_label_pc ".Lhandle_error_handler_cjalr") ⊤
            (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error_handler_invoke") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_33_spec_aux with "[- $HPC $Hcra $Hrmap $Hcode]");
      [done | done |].
    iNext; iSplit.
    - iIntros (Htgt mie rmap' Hdom') "(HPC & Hcra & Hrmap & _)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[Hpost _]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 33) ^+ 12)%a =
                   (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_handler_return")%a);
        last (offsets_compute; solve_addr+Hsize).
      iApply ("Hpost" with "[//] [//] [-]"). iFrame "∗ Hswitcher".
    - iIntros (Htgt rmap' Hdom') "(Hcra & Hrmap)".
      unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
      iDestruct "Hpost" as "[_ Hfailed]".
      rewrite (_ : ((a_switcher_call ^+ switcher_block_offset 33) ^+ 11)%a =
                   (a_switcher_call ^+ switcher_label_offset ".Lhandle_error_handler_cjalr")%a);
        last (offsets_compute; solve_addr+Hsize).
      iApply ("Hfailed" with "[//] [//]"). iFrame "∗ Hswitcher".
  Qed.

  (** Block 34, from [.Lhandle_error_handler_return]: a request to unwind
      ([ca0] not zero) forces the unwind; otherwise the switcher installs
      the context of the handler, at [.Lhandle_error_install_context]. *)
  Lemma switcher_handler_return_block_spec (wca0 : LWord) :
    PC ↦ₚ switcher_label_pc ".Lhandle_error_handler_return" ∗
    ca0 ↦ᵣ wca0 ∗
    switcher_code ∗
    ▷ ( ( ⌜nonZero wca0.(lw) = true⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lcommon_force_unwind" ∗
          ca0 ↦ᵣ wca0 ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) ∧
        ( ⌜nonZero wca0.(lw) = false⌝ -∗
          PC ↦ₚ switcher_label_pc ".Lhandle_error_install_context" ∗
          ca0 ↦ᵣ wca0 ∗
          switcher_code -∗
          WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} ) )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hca0 & #Hswitcher & Hpost)".
    pose proof switcher_SubBounds as Hsub.
    pose proof switcher_size as Hsize; cbn in Hsize.
    switcher_unfold_code "Hswitcher".
    switcher_focus_block (switcher_block ".Lhandle_error_handler_return") "Hswitcher"
      as "Hcode" "Hcls"; iHide "Hswitcher" as hswitcher.
    iApply (switcher_exception_block_34_spec_aux with "[- $HPC $Hca0 $Hcode]");
      [done | offsets_compute; solve_addr+Hsize |].
    iNext; iIntros (off Hoff) "(HPC & Hca0)".
    unfocus_block "Hcode" "Hcls" as "Hswitcher"; subst hswitcher.
    destruct Hoff as [(Hnz & ->) | (Hnz & ->)].
    - switcher_change_pc (switcher_label_offset ".Lcommon_force_unwind").
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[//]"). iFrame "∗ Hswitcher".
    - switcher_change_pc (switcher_label_offset ".Lhandle_error_install_context").
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//]"). iFrame "∗ Hswitcher".
  Qed.

End Switcher_Exception_Blocks_6.
