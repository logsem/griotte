From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import register_tactics.
From griotte Require Import call_stack switcher_exception_states switcher_error_state
  clear_registers_spec.

(** * Exception path: the invocation of a handler and its return

    [.Lhandle_error_handler_invoke] enables interrupts, clears every
    register but the handler's return sentry, stack, globals and three
    arguments ([zero_all_registers_except_asm]; [cnull] reads 0), and
    calls the handler's PC in [cra] with [cjalr cra, cra]
    ([.Lhandle_error_handler_cjalr]): the link is the return sentry of the
    handler, [handler_return_sentry]. The [cjalr] faults when the computed
    word is not a valid target.

    [.Lhandle_error_handler_return], the handler's return, disables
    interrupts; a request to unwind ([ca0] not zero) forces the unwind.
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

  (** From [.Lhandle_error_handler_invoke]: with interrupts enabled, the
      registers of [rmap] (all but [cra], [csp], [cgp], [ca0], [ca1] and
      [ca2]) are cleared, and the [cjalr] calls the word in [cra] with the
      handler's return sentry as link, or faults. *)
  Lemma handle_error_handler_invoke_spec (wcra : LWord) (rmap : LReg) :
    dom rmap = all_registers_s ∖ list_to_set [cra; csp; cgp; ca0; ca1; ca2] ->

    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_invoke" ∗
    cra ↦ᵣ[th] wcra ∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ[th] w) ∗
    switcher_code ∗
    ▷ ( ( ⌜jalr_target_ok cra cra wcra.(lw) = true⌝ -∗
          ∀ (mie : InterruptStatus) (rmap' : LReg),
          ⌜dom rmap' = dom rmap⌝ -∗
          PC ↦ₚ[th] lupdatePcPerm wcra ∗
          cra ↦ᵣ[th] handler_return_sentry mie ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜w = WInt 0⌝) -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜jalr_target_ok cra cra wcra.(lw) = false⌝ -∗
          ∀ rmap' : LReg,
          ⌜dom rmap' = dom rmap⌝ -∗
          cra ↦ᵣ[th] wcra ∗
          ([∗ map] r↦w ∈ rmap', r ↦ᵣ[th] w ∗ ⌜w = WInt 0⌝) -∗
          trap_safe (switcher_label_pc ".Lhandle_error_handler_cjalr") ⊤
            (HO th) ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcra & Hrmap & #Hswitcher & Hpost)".
    switcher_open_label ".Lhandle_error_handler_invoke" "Hswitcher" as "Hcode" pc_a Hpc_a.
    iAssert (codefrag_pers pc_a handle_error_handler_invoke_instrs) as "Hcode_all";
      first iExact "Hcode".
    iDestruct (codefrag_app_pers with "Hcode_all") as "[_ Hcode_rest]".
    iDestruct (codefrag_app_pers with "Hcode_rest") as "[#Hclear _]".
    (* SetMIE InterruptEnabled *)
    iInstr "Hcode".
    (* The clearing of the registers *)
    rewrite (_ : (pc_a ^+ length (encodeInstrsW [SetMIE InterruptEnabled]))%a = (pc_a ^+ 1)%a);
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
    - (* Jalr cra cra *)
      iInstr "Hcode".
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" $! eq_refl mie rmap' with "[] [-]");
        first (iPureIntro; by rewrite Hdom' Hdom).
      rewrite /handler_return_sentry.
      switcher_label_in_block ".Lhandle_error_handler_invoke" ".Lhandle_error_handler_return"
        as Hreturn.
      rewrite Hreturn.
      iFrame "HPC Hcra Hrmap".
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
      iTrap with "Hfailed".
  Qed.

  (** From [.Lhandle_error_handler_return]: a request to unwind ([ca0] not
      zero) forces the unwind; otherwise the switcher installs the context
      of the handler, at [.Lhandle_error_install_context]. *)
  Lemma handle_error_handler_return_spec (wca0 : LWord) :
    PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_handler_return" ∗
    ca0 ↦ᵣ[th] wca0 ∗
    switcher_code ∗
    ▷ ( ( ⌜nonZero wca0.(lw) = true⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lcommon_force_unwind" ∗
          ca0 ↦ᵣ[th] wca0 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) ∧
        ( ⌜nonZero wca0.(lw) = false⌝ -∗
          PC ↦ₚ[th] switcher_label_pc ".Lhandle_error_install_context" ∗
          ca0 ↦ᵣ[th] wca0 -∗
          WP Seq (Instr Executable) @[th] {{ HO th }} ) )
    ⊢ WP Seq (Instr Executable) @[th] {{ HO th }}.
  Proof.
    iIntros "(HPC & Hca0 & #Hswitcher & Hpost)".
    switcher_open_label ".Lhandle_error_handler_return" "Hswitcher" as "Hcode".
    (* SetMIE InterruptDisabled *)
    iInstr "Hcode".
    destruct (nonZero wca0.(lw)) eqn:Hnz.
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" wp_jnez_success_jmp_z with "[$HPC $Hca0]" as "(HPC & Hca0)".
      { jump_to (a_switcher_call ^+ switcher_label_offset ".Lcommon_force_unwind")%a
          by switcher_addr_eq. }
      iDestruct "Hpost" as "[Hpost _]".
      iApply ("Hpost" with "[//]"). iFrame "HPC Hca0".
    - (* Jne .Lcommon_force_unwind ca0 0 *)
      iInstrApply "Hcode" wp_jnez_success_next_any with "[$HPC $Hca0]" as "(HPC & Hca0)".
      switcher_change_pc_label ".Lhandle_error_install_context".
      iDestruct "Hpost" as "[_ Hpost]".
      iApply ("Hpost" with "[//]"). iFrame "HPC Hca0".
  Qed.

End Handle_Error_Handler_Invoke.
