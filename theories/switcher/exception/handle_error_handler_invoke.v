From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state
  clear_registers_spec.

(** * Exception path: the invocation of a handler and its return

    [.Lhandle_error_handler_invoke] enables interrupts (the posture goes
    into the link of the thread), clears every
    register but the handler's return sentry, stack, globals and three
    arguments ([zero_all_registers_except_asm]; [cnull] reads 0), and
    calls the handler's PC in [cra] with [cjalr cra, cra]
    ([.Lhandle_error_handler_cjalr]): the link is the return sentry of the
    handler, [handler_return_sentry]. The [cjalr] faults when the computed
    word is not a valid target.

    [.Lhandle_error_handler_return], the handler's return, entered with
    interrupts enabled, disables them (the posture comes back from the
    link); a request to unwind ([ca0] not zero) forces the unwind.
    Otherwise, the switcher continues at [.Lhandle_error_install_context],
    which installs the context of the handler. *)

Section Handle_Error_Handler_Invoke.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The code of [.Lhandle_error_handler_invoke], around the clearing of
      the registers. *)
  #[local] Definition handle_error_handler_invoke_instrs : list Word :=
    encodeInstrsW [SetMIE InterruptEnabled] ++
    rclear_instrs' registers_handler_invoke ++
    encodeInstrsW [Jalr cra cra].

  (** From [.Lhandle_error_handler_invoke], at InterruptDisabled with the
      posture: interrupts are enabled (the posture goes into the link), the
      registers of [rmap] (all but [cra], [csp], [cgp], [ca0], [ca1] and
      [ca2]) are cleared, and the [cjalr] calls the word in [cra] with the
      handler's return sentry as link, at the posture of the target, or
      faults. *)
  Lemma handle_error_handler_invoke_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] ->
    route_pre th InterruptEnabled ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_invoke" ∗
    cra ↦ᵣ[th] wcra ∗
    regs[th] rmap ∗
    switcher_code ∗
    MIE ↦ₜ[th] InterruptDisabled ∗
    held (th := th) InterruptDisabled ∗
    ▷ ( ( ⌜jalr_target_ok cra cra wcra.(lw) = true⌝ -∗
          ∀ rmap' : LReg,
          ⌜dom rmap' = dom rmap⌝ -∗
          PC ↦ₚ[th] lupdatePcPerm wcra ∗
          cra ↦ᵣ[th] handler_return_sentry InterruptEnabled ∗
          regs₀[th] rmap' ∗
          MIE ↦ₜ[th] default InterruptEnabled (jalr_target_mie wcra.(lw)) ∗
          held (th := th) (default InterruptEnabled (jalr_target_mie wcra.(lw))) ∗
          £ 1 -∗
          safe[th] ) ∧
        ( ⌜jalr_target_ok cra cra wcra.(lw) = false⌝ -∗
          ∀ rmap' : LReg,
          ⌜dom rmap' = dom rmap⌝ -∗
          cra ↦ᵣ[th] wcra ∗
          regs₀[th] rmap' ∗
          MIE ↦ₜ[th] InterruptEnabled -∗
          trap_safe (switcher_label_pc ".Lhandle_error_handler_cjalr") ⊤
            (HO th) ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hdom Hpre) "(HPC & Hcra & Hrmap & #Hswitcher & Hmie & Hheld & Hpost)".
    switcher_open_label ".Lhandle_error_handler_invoke" "Hswitcher" as "Hcode" pc_a Hpc_a.
    iAssert (codefrag_pers pc_a handle_error_handler_invoke_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hclear _]".
    (* SetMIE InterruptEnabled *)
    iInstrApply "Hcode"
      (wp_setmie_success_posture _ _ _ _ _ _ _ _ _ InterruptEnabled InterruptDisabled)
      with "[$HPC $Hmie $Hheld]" as "(HPC & Hmie & _)"; [done..|].
    (* The clearing of the registers *)
    rewrite (_ : pc_a ^+ length (encodeInstrsW [SetMIE InterruptEnabled]) = pc_a ^+ 1);
      last (cbn; solve_addr).
    rewrite -registers_except_handler_invoke.
    iApply (zero_all_registers_except_spec with "[- $HPC $Hrmap $Hclear]").
    { by rewrite registers_except_handler_invoke. }
    { done. }
    { rewrite registers_except_handler_invoke /=. solve_addr. }
    { exact Hdom. }
    iNext; iIntros "(%rmap' & %Hdom' & HPC & Hrmap & _)".
    rewrite registers_except_handler_invoke.
    switcher_set_pc_in_block ".Lhandle_error_handler_invoke" ".Lhandle_error_handler_cjalr".
    destruct (jalr_target_ok cra cra wcra.(lw)) eqn:Htgt.
    - (* At InterruptEnabled, the thread holds nothing besides MIE *)
      iAssert (held (th := th) InterruptEnabled) as "Hen"; first done.
      (* Jalr cra cra *)
      iInstrApply "Hcode" with "Hlc"
        (wp_jalr_success_call_same_posture _ _ _ _ _ _ _ _ _ wcra InterruptEnabled)
        with "[$HPC $Hcra $Hmie]" as "(HPC & Hcra & Hmie & Hheld)".
      1: { intros _ Hc. by specialize (Hpre Hc). }
      1: done.
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" $! eq_refl rmap' with "[] [-]");
        first (iPureIntro; by rewrite Hdom' Hdom).
      rewrite /handler_return_sentry.
      switcher_label_in_block ".Lhandle_error_handler_invoke" ".Lhandle_error_handler_return"
        as Hreturn.
      rewrite Hreturn.
      iFrame "HPC Hcra Hrmap Hmie Hheld Hlc".
    - (* The fault continuation at [.Lhandle_error_handler_cjalr], stated
         from the start of the block, as the PC *)
      iDestruct "Hpost" as "[_ Hfailed]".
      switcher_pc_in_block ".Lhandle_error_handler_invoke" ".Lhandle_error_handler_cjalr"
        "Hfailed".
      clear Hpc_a.
      (* Jalr cra cra *)
      iInstrApply "Hcode" wp_jalr_fail_target_same with "[$HPC $Hcra]" as "(HPC & Hcra)".
      iSpecialize ("Hfailed" $! eq_refl rmap' with "[]");
        first (iPureIntro; by rewrite Hdom' Hdom).
      iSpecialize ("Hfailed" with "[$Hcra $Hrmap $Hmie]").
      iTrap with "Hfailed".
  Qed.

  (** From [.Lhandle_error_handler_return], at InterruptEnabled: interrupts
      are disabled (the posture comes back from the link); a request to
      unwind ([ca0] not zero) forces the unwind; otherwise the switcher
      installs the context of the handler, at
      [.Lhandle_error_install_context]. *)
  Lemma handle_error_handler_return_spec (wca0 : LWord) :
    route_pre th InterruptEnabled ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" ∗
    ca0 ↦ᵣ[th] wca0 ∗
    switcher_code ∗
    MIE ↦ₜ[th] InterruptEnabled ∗
    ▷ ( ( ⌜nonZero wca0.(lw) = true⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          ca0 ↦ᵣ[th] wca0 ∗
          MIE ↦ₜ[th] InterruptDisabled ∗
          held (th := th) InterruptDisabled -∗
          safe[th] ) ∧
        ( ⌜nonZero wca0.(lw) = false⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_install_context" ∗
          ca0 ↦ᵣ[th] wca0 ∗
          MIE ↦ₜ[th] InterruptDisabled ∗
          held (th := th) InterruptDisabled ∗
          £ 2 -∗
          safe[th] ) )
    ⊢ safe[th].
  Proof.
    iIntros (Hpre) "(HPC & Hca0 & #Hswitcher & Hmie & Hpost)".
    switcher_open_label ".Lhandle_error_handler_return" "Hswitcher" as "Hcode".
    (* At InterruptEnabled, the thread holds nothing besides MIE *)
    iAssert (held (th := th) InterruptEnabled) as "Hen"; first done.
    (* SetMIE InterruptDisabled *)
    iInstrApply "Hcode" with "Hlc0"
      (wp_setmie_success_posture _ _ _ _ _ _ _ _ _ InterruptDisabled InterruptEnabled)
      with "[$HPC $Hmie]" as "(HPC & Hmie & Hheld)"; [done..|].
    destruct (nonZero wca0.(lw)) eqn:Hnz.
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hca0]" as "(HPC & Hca0)".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[//]"). iFrame "HPC Hca0 Hmie Hheld".
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" with "Hlc1" wp_jnez_success_next_any with "[$HPC $Hca0]"
        as "(HPC & Hca0)".
      switcher_change_pc_label ".Lhandle_error_install_context".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//]"). iFrame "HPC Hca0 Hmie Hheld".
      iApply (lc_split 1 1). iFrame "Hlc0 Hlc1".
  Qed.

End Handle_Error_Handler_Invoke.
