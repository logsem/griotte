From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states switcher_macros_spec clear_registers_spec.

(** * Call routine: clear the registers and jump to the callee

    [.Lswitch_load_zero_arguments_start] clears the argument registers that
    the entry point does not use, by a jump into the zeroing of
    [.Lswitch_zero_arguments_start], and enables interrupts, unless the
    entry point asks for them disabled, in which case it jumps to
    [.Lswitch_skip_interrupt_enable]. [.Lswitch_skip_interrupt_enable]
    clears the registers that are not arguments
    ([clear_registers_pre_call_asm]), and [.Lswitch_callee_call] jumps to
    the callee, with the return sentry of the switcher as link. *)

Section Switcher_Clear_Unused_Args.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** From [.Lswitch_skip_interrupt_enable]: clear the registers that are
      not arguments, and jump to the callee. *)
  Lemma switch_skip_interrupt_enable_spec
    (wcs0 wcs1 wct1 wct2 wctp : LWord) (bpcc epcc a_tgt : Addr) (rmap : LReg) :
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_skip_interrupt_enable" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] wctp ∗
    cra ↦ᵣ[th] Cap RX Global bpcc epcc a_tgt ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        regs₀[th] rmap' -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hdom) "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_call"; first iFrame "Hswitcher".

    (* [.Lswitch_skip_interrupt_enable] *)
    switcher_open_label ".Lswitch_skip_interrupt_enable" "Hswitcher" as "Hcode_skip".
    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs"; [iFrame "Hctp"|].
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs"; [iFrame "Hct2"|].
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs"; [iFrame "Hcs1"|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs"; [iFrame "Hcs0"|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs"; [iFrame "Hct1"|].
    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode_skip $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. clear. set_solver. }
    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & _)".

    (* [.Lswitch_callee_call] *)
    switcher_open_label ".Lswitch_callee_call" "Hswitcher_call" as "Hcode_call" a_call Ha_call.
    (* Jalr cra cra *)
    iInstr "Hcode_call".
    rewrite (_ : a_call ^+ 1 = a_switcher_return);
      last (rewrite switcher_return_offset; switcher_addr_eq).
    iApply ("Hpost" $! _ rmap'); iFrame "HPC Hcra Hregs"; done.
  Qed.

  (** From [.Lswitch_load_zero_arguments_start], up to the jump into the
      zeroing of the arguments, at [.Lswitch_zero_arguments_start]. *)
  #[local] Lemma switch_load_zero_arguments_codefrag (a : Addr) :
    codefrag_pers a
      (encodeInstrsW
         ([machine_instructions.Auipcc cs0 4%Z;
           machine_instructions.LAnd ct2 (inr ctp) (inl 7%Z);
           machine_instructions.Lea cs0 cs0 (inr ct2);
           machine_instructions.Jalr cnull cs0] ++
          clear_registers_pre_call_skip ++
          [machine_instructions.LAnd ct1 (inr ctp) (inl ExportEntryInterruptStatusSwitcherMask);
           machine_instructions.Jne (inl 2%Z) (inr ct1) (inl 0%Z);
           machine_instructions.SetMIE InterruptEnabled])) -∗
    codefrag_pers (a ^+ 4) clear_registers_pre_call_skip_instrs.
  Proof.
    iIntros "Hcode".
    rewrite /encodeInstrsW !map_app.
    iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode]".
    iDestruct (codefrag_app_pers with "Hcode") as "[Hcode _]".
    done.
  Qed.

  (** From [.Lswitch_load_zero_arguments_start]: clear the argument
      registers that the [nargs] arguments of the callee do not use, enable
      interrupts if its posture asks for it, clear the other registers and
      jump to the callee. *)
  Lemma switcher_clear_unused_args_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct1 wct2 : LWord) (posture : InterruptStatus) (nargs : nat)
    (bpcc epcc a_tgt : Addr) (arg_rmap rmap : LReg) :
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_load_zero_arguments_start" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] WInt (entry_point_flags posture (Z.of_nat nargs)) ∗
    cra ↦ᵣ[th] Cap RX Global bpcc epcc a_tgt ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
        regs₀[th] rmap' -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hnargs Hargs Hdom)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_skip"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_load_zero_arguments_start" "Hswitcher" as "Hcode" a_zero Ha_zero.
    (* Auipcc cs0 .Lswitch_zero_arguments_start *)
    iInstr "Hcode".
    (* LAnd ct2 ctp 7 *)
    iInstr "Hcode".
    rewrite entry_point_flags_nargs; last lia.
    (* Lea cs0 cs0 ct2 *)
    iInstr "Hcode".
    { instantiate (1 := (a_zero ^+ 4) ^+ nargs). solve_addr. }
    (* Jalr cnull cs0 *)
    iInstr "Hcode".
    iDestruct (switch_load_zero_arguments_codefrag with "Hcode") as "Hcode_args".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ (a_zero ^+ 4) arg_rmap nargs
             with "[- $HPC $Hcode_args $Hargs]"); try solve_pure.
    { rewrite length_clear_registers_pre_call_skip_instrs; solve_addr. }
    iIntros "(%arg_rmap' & %Harg_rmap' & HPC & Hargs & _)".
    rewrite length_clear_registers_pre_call_skip_instrs.
    rewrite (_ : (a_zero ^+ 4) ^+ 7%nat = a_zero ^+ 11); last solve_addr.
    (* LAnd ct1 ctp ExportEntryInterruptStatusSwitcherMask *)
    iInstr "Hcode".
    rewrite entry_point_flags_posture.
    destruct posture; cbn [entry_point_posture].
    (* Jne .Lswitch_skip_interrupt_enable ct1 0 *)
    all: iInstr "Hcode".
    (* SetMIE InterruptEnabled, interrupts enabled *)
    1: iInstr "Hcode".
    all: switcher_change_pc_label ".Lswitch_skip_interrupt_enable".
    all: iApply (switch_skip_interrupt_enable_spec with
           "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip]"); first done.
    all: iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs)".
    all: iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs"; done.
  Qed.

  (** Variant of [switcher_clear_unused_args_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_clear_unused_args_known_spec
    (wcs0 wcs1 wct1 wct2 : LWord) (posture : InterruptStatus) (nargs : nat)
    (bpcc epcc a_tgt : Addr) (arg_rmap rmap : LReg) :
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_load_zero_arguments_start" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] WInt (entry_point_flags posture (Z.of_nat nargs)) ∗
    cra ↦ᵣ[th] Cap RX Global bpcc epcc a_tgt ∗
    regs[th] arg_rmap ∗
    regs[th] rmap ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry (ret_kind mie) XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs)
                     then ⌜ arg_rmap !! r = Some w ⌝
                     else ⌜ w = WInt 0 ⌝ ) ∗
        regs₀[th] rmap' -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hnargs Hargs Hdom)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_skip"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_load_zero_arguments_start" "Hswitcher" as "Hcode" a_zero Ha_zero.
    (* Auipcc cs0 .Lswitch_zero_arguments_start *)
    iInstr "Hcode".
    (* LAnd ct2 ctp 7 *)
    iInstr "Hcode".
    rewrite entry_point_flags_nargs; last lia.
    (* Lea cs0 cs0 ct2 *)
    iInstr "Hcode".
    { instantiate (1 := (a_zero ^+ 4) ^+ nargs). solve_addr. }
    (* Jalr cnull cs0 *)
    iInstr "Hcode".
    iDestruct (switch_load_zero_arguments_codefrag with "Hcode") as "Hcode_args".
    iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    iApply (clear_registers_pre_call_skip_spec_known _ _ _ _ (a_zero ^+ 4) arg_rmap nargs
             with "[- $HPC $Hcode_args $Hargs]"); try solve_pure.
    { rewrite length_clear_registers_pre_call_skip_instrs; solve_addr. }
    iIntros "(%arg_rmap' & %Harg_rmap' & HPC & Hargs & _)".
    rewrite length_clear_registers_pre_call_skip_instrs.
    rewrite (_ : (a_zero ^+ 4) ^+ 7%nat = a_zero ^+ 11); last solve_addr.
    (* LAnd ct1 ctp ExportEntryInterruptStatusSwitcherMask *)
    iInstr "Hcode".
    rewrite entry_point_flags_posture.
    destruct posture; cbn [entry_point_posture].
    (* Jne .Lswitch_skip_interrupt_enable ct1 0 *)
    all: iInstr "Hcode".
    (* SetMIE InterruptEnabled, interrupts enabled *)
    1: iInstr "Hcode".
    all: switcher_change_pc_label ".Lswitch_skip_interrupt_enable".
    all: iApply (switch_skip_interrupt_enable_spec with
           "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip]"); first done.
    all: iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs)".
    all: iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs"; done.
  Qed.

End Switcher_Clear_Unused_Args.
