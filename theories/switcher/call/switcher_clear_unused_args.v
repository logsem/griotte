From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states switcher_macros_spec clear_registers_spec.

(** * Call routine: clear the registers and jump to the callee

    [.Lswitcher_clear_unused_args] clears the argument registers that the
    entry point does not use ([clear_registers_pre_call_skip_asm]).
    [.Lswitcher_enable_interrupts] enables interrupts, unless the entry
    point asks for them disabled, in which case it jumps to
    [.Lswitch_skip_interrupt_enable]. [.Lswitch_skip_interrupt_enable]
    clears the registers that are not arguments
    ([clear_registers_pre_call_asm]), and [.Lswitch_callee_call] jumps to
    the callee, with the return sentry of the switcher as link. *)

Section Switcher_Clear_Unused_Args.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The interrupt posture of [.Lswitcher_enable_interrupts]: interrupts
      are enabled unless the posture of the callee, in [ctp], asks for them
      disabled. *)
  #[local] Lemma switcher_enable_interrupts_posture_spec (posture : InterruptStatus) :
    PC ↦ₚ switcher_label_pc ".Lswitcher_enable_interrupts" ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    switcher_code ∗
    ▷ ( PC ↦ₚ switcher_label_pc ".Lswitch_skip_interrupt_enable" ∗
        ctp ↦ᵣ WInt (entry_point_posture posture) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros "(HPC & Hctp & #Hswitcher & Hpost)".
    switcher_open_label ".Lswitcher_enable_interrupts" "Hswitcher" as "Hcode".
    destruct posture; cbn [entry_point_posture].
    - (* Jne .Lswitch_skip_interrupt_enable ctp 0 *)
      iInstr "Hcode".
      (* SetMIE InterruptEnabled *)
      iInstr "Hcode".
      switcher_change_pc_label ".Lswitch_skip_interrupt_enable".
      iApply "Hpost"; iFrame "HPC Hctp".
    - (* Jne .Lswitch_skip_interrupt_enable ctp 0 *)
      iInstr "Hcode".
      switcher_change_pc_label ".Lswitch_skip_interrupt_enable".
      iApply "Hpost"; iFrame "HPC Hctp".
  Qed.

  (** From [.Lswitcher_enable_interrupts]: enable interrupts if the posture
      of the callee asks for it, clear the registers that are not
      arguments, and jump to the callee. *)
  Lemma switcher_enable_interrupts_spec
    (wcs0 wcs1 wct1 wct2 : LWord) (posture : InterruptStatus)
    (bpcc epcc a_tgt : Addr) (rmap : LReg) :
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_enable_interrupts" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ wct2 ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    cra ↦ᵣ WCap true RX Global bpcc epcc a_tgt ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hdom) "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_skip"; first iFrame "Hswitcher".
    iAssert switcher_code as "Hswitcher_call"; first iFrame "Hswitcher".
    iApply (switcher_enable_interrupts_posture_spec with "[- $HPC $Hctp $Hswitcher]").
    iIntros "!> (HPC & Hctp)".

    (* [.Lswitch_skip_interrupt_enable] *)
    switcher_open_label ".Lswitch_skip_interrupt_enable" "Hswitcher_skip" as "Hcode_skip".
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
    rewrite (_ : (a_call ^+ 1)%a = a_switcher_return);
      last (rewrite switcher_return_offset; switcher_addr_eq).
    iApply ("Hpost" $! _ rmap'); iFrame "HPC Hcra Hregs"; done.
  Qed.

  (** From [.Lswitcher_clear_unused_args]: clear the argument registers that
      the [nargs] arguments of the callee do not use, enable interrupts if
      its posture asks for it, clear the other registers and jump to the
      callee. *)
  Lemma switcher_clear_unused_args_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct1 : LWord) (posture : InterruptStatus) (nargs : nat)
    (bpcc epcc a_tgt : Addr) (arg_rmap rmap : LReg) :
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_clear_unused_args" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    cra ↦ᵣ WCap true RX Global bpcc epcc a_tgt ∗
    ( [∗ map] r↦w ∈ arg_rmap,
        r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else True ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hnargs Hargs Hdom)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_irq"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitcher_clear_unused_args" "Hswitcher" as "Hcode".
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ arg_rmap (nargs + 1)
             with "[- $HPC $Hcode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hargs".
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & _)".
    switcher_change_pc_label ".Lswitcher_enable_interrupts".
    iApply (switcher_enable_interrupts_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_irq]"); first done.
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs"; done.
  Qed.

  (** Variant of [switcher_clear_unused_args_spec] for a known callee, whose
      arguments are not required to be valid: the argument registers that
      are not cleared keep their initial values. *)
  Lemma switcher_clear_unused_args_known_spec
    (wcs0 wcs1 wct1 : LWord) (posture : InterruptStatus) (nargs : nat)
    (bpcc epcc a_tgt : Addr) (arg_rmap rmap : LReg) :
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->

    PC ↦ₚ switcher_label_pc ".Lswitcher_clear_unused_args" ∗
    cs0 ↦ᵣ wcs0 ∗
    cs1 ↦ᵣ wcs1 ∗
    ct1 ↦ᵣ wct1 ∗
    ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) ∗
    ctp ↦ᵣ WInt (entry_point_posture posture) ∗
    cra ↦ᵣ WCap true RX Global bpcc epcc a_tgt ∗
    ( [∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w ) ∗
    ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w ) ∗
    switcher_code ∗
    ▷ ( ∀ (mie : InterruptStatus) (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ WCap true RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ WSentry (ret_kind mie) true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ w ∗ if decide (r ∈ dom_arg_rmap nargs)
                     then ⌜ arg_rmap !! r = Some w ⌝
                     else ⌜ w = WInt 0 ⌝ ) ∗
        ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ ) -∗
        WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }} )
    ⊢ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (Hnargs Hargs Hdom)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hswitcher & Hpost)".
    iAssert switcher_code as "Hswitcher_irq"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitcher_clear_unused_args" "Hswitcher" as "Hcode".
    iApply (clear_registers_pre_call_skip_spec_known _ _ _ _ _ arg_rmap (nargs + 1)
             with "[- $HPC $Hcode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hargs".
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & _)".
    switcher_change_pc_label ".Lswitcher_enable_interrupts".
    iApply (switcher_enable_interrupts_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_irq]"); first done.
    iNext; iIntros (mie rmap') "(%Hrmap' & HPC & Hcra & Hregs)".
    iApply ("Hpost" $! mie arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs"; done.
  Qed.

End Switcher_Clear_Unused_Args.
