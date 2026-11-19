From iris.proofmode Require Import proofmode.
From griotte Require Import memory_region rules proofmode.
From griotte Require Import map_simpl register_tactics.
From griotte Require Import switcher_call_states switcher_macros_spec clear_registers_spec.

(** * Call routine: clear the registers and jump to the callee

    [.Lswitch_load_zero_arguments_start] clears the argument registers that
    the entry point does not use, by a jump into the zeroing of
    [.Lswitch_zero_arguments_start]. The switcher runs with interrupts
    enabled: if the entry point asks for them disabled, it seals the
    callee's capability in [cra] into an interrupt-disabling sentry, with
    the key of [.sealing_key_interrupt_sentries]; otherwise it jumps to
    [.Lswitch_skip_interrupt_disable]. [.Lswitch_skip_interrupt_disable]
    clears the registers that are not arguments
    ([clear_registers_pre_call_asm]), and [.Lswitch_callee_call] jumps to
    the callee, with the return sentry of the switcher as link, which
    enables interrupts. *)

Section Switcher_Clear_Unused_Args.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ}
    {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  (** The callee's capability in [cra] at the jump to the callee, for the
      posture of its entry: sealed into an interrupt-disabling sentry, or
      as it is. *)
  #[local] Definition callee_target (posture : InterruptStatus) (bpcc epcc a_tgt : Addr) : Word :=
    if posture is InterruptDisabled
    then Sentry FwdDisable RX Global bpcc epcc a_tgt
    else Cap RX Global bpcc epcc a_tgt.

  (** From [.Lswitch_skip_interrupt_disable]: clear the registers that are
      not arguments, and jump to the callee. *)
  Lemma switch_skip_interrupt_disable_spec
    (wcs0 wcs1 wct1 wct2 wctp : LWord) (bpcc epcc a_tgt : Addr) (rmap : LReg)
    (posture : InterruptStatus) :
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->
    th ≠ CtxSwitch ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_skip_interrupt_disable" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] wctp ∗
    cra ↦ᵣ[th] callee_target posture bpcc epcc a_tgt ∗
    regs[th] rmap ∗
    switcher_code ∗
    MIE ↦ₜ[th] InterruptEnabled ∗
    held (th := th) InterruptEnabled ∗
    ▷ ( ∀ (rmap' : LReg),
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry RetEnable XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        regs₀[th] rmap' ∗
        MIE ↦ₜ[th] posture ∗
        held (th := th) posture -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hdom Hth)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hregs & #Hswitcher & Hmie & Hheld & Hpost)".
    iAssert switcher_code as "Hswitcher_call"; first iFrame "Hswitcher".

    (* [.Lswitch_skip_interrupt_disable] *)
    switcher_open_label ".Lswitch_skip_interrupt_disable" "Hswitcher" as "Hcode_skip".
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
    rewrite /callee_target.
    destruct posture.
    (* Jalr cra cra *)
    all: iInstr "Hcode_call".
    all: try (intros Hcs; by destruct Hth).
    all: iEval (cbn [jalr_target_mie default sentry_kind_mie lw id]) in "Hmie Hheld".
    all: rewrite (_ : a_call ^+ 1 = a_switcher_return);
      last (rewrite switcher_return_offset; switcher_addr_eq).
    all: iEval (rewrite /lupdatePcPerm /lift_word /=) in "HPC".
    all: iApply ("Hpost" $! rmap'); iFrame; done.
  Qed.

  (** From [.Lswitch_load_zero_arguments_start], up to the jump into the
      zeroing of the arguments, at [.Lswitch_zero_arguments_start]. *)
  #[local] Lemma switch_load_zero_arguments_codefrag (a : Addr) (z : Z) :
    codefrag_pers a
      (encodeInstrsW
         ([machine_instructions.Auipcc cs0 4%Z;
           machine_instructions.LAnd ct2 (inr ctp) (inl 7%Z);
           machine_instructions.Lea cs0 cs0 (inr ct2);
           machine_instructions.Jalr cnull cs0] ++
          clear_registers_pre_call_skip ++
          [machine_instructions.LAnd ct1 (inr ctp) (inl ExportEntryInterruptStatusSwitcherMask);
           machine_instructions.Jeq (inl 4%Z) (inr ct1) (inl 0%Z);
           machine_instructions.Auipcc ctp z;
           machine_instructions.CLoad ctp ctp 0;
           machine_instructions.Seal cra ctp cra])) -∗
    codefrag_pers (a ^+ 4) clear_registers_pre_call_skip_instrs.
  Proof.
    iIntros "Hcode".
    rewrite /encodeInstrsW !map_app.
    iDestruct (codefrag_app_pers with "Hcode") as "[_ Hcode]".
    iDestruct (codefrag_app_pers with "Hcode") as "[Hcode _]".
    done.
  Qed.

  (** From [.Lswitch_load_zero_arguments_start]: clear the argument
      registers that the [nargs] arguments of the callee do not use, seal
      the callee into an interrupt-disabling sentry if its posture asks for
      it, clear the other registers and jump to the callee. *)
  Lemma switcher_clear_unused_args_spec
    (W : WORLD) (C : CmptName)
    (wcs0 wcs1 wct1 wct2 : LWord) (posture : InterruptStatus) (nargs : nat)
    (bpcc epcc a_tgt : Addr) (arg_rmap rmap : LReg) :
    (nargs <= 7) ->
    is_arg_rmap arg_rmap 8 ->
    dom rmap = all_registers_s ∖ ({[ cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ; ct2 ; ctp ]} ∪ dom_arg_rmap 8) ->
    th ≠ CtxSwitch ->

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
    (b_switcher ^+ 5) ↦ₐ□ SealRange (true,false) Local ot_interrupt_sentries
      (ot_interrupt_sentries ^+ 1) ot_interrupt_sentries ∗
    switcher_code ∗
    MIE ↦ₜ[th] InterruptEnabled ∗
    held (th := th) InterruptEnabled ∗
    ▷ ( ∀ (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry RetEnable XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs) then interp W C w else ⌜ w = WInt 0 ⌝ ) ∗
        regs₀[th] rmap' ∗
        MIE ↦ₜ[th] posture ∗
        held (th := th) posture ∗
        £ 1 -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hnargs Hargs Hdom Hth)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hsentries_key
      & #Hswitcher & Hmie & Hheld & Hpost)".
    iAssert switcher_code as "Hswitcher_skip"; first iFrame "Hswitcher".
    switcher_open_label ".Lswitch_load_zero_arguments_start" "Hswitcher" as "Hcode" a_zero Ha_zero.
    (* Auipcc cs0 .Lswitch_zero_arguments_start *)
    iInstr "Hcode" with "Hlc".
    (* LAnd ct2 ctp 7 *)
    iInstr "Hcode".
    rewrite entry_point_flags_nargs; last lia.
    (* Lea cs0 cs0 ct2 *)
    iInstr "Hcode".
    { instantiate (1 := (a_zero ^+ 4) ^+ nargs). solve_addr. }
    (* Jalr cnull cs0 *)
    iInstr "Hcode".
    { intros Hcs; by destruct Hth. }
    iEval (cbn [jalr_target_mie default lw]) in "Hmie Hheld".
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
    (* Jeq .Lswitch_skip_interrupt_disable ct1 0 *)
    all: iInstr "Hcode".
    2: { (* Auipcc ctp .sealing_key_interrupt_sentries *)
         iInstr "Hcode".
         { instantiate (1 := b_switcher ^+ 5). switcher_addr_eq. }
         (* CLoad ctp ctp 0 *)
         iInstr "Hcode".
         { apply withinBounds_true_iff.
           pose proof switcher_call_entry_point; pose proof switcher_size; solve_addr. }
         (* Seal cra ctp cra *)
         iInstr "Hcode" using seal_sentry_next_ok_tagged.
         all: try done.
         all: try (apply withinBounds_true_iff; solve_finz).
         all: try reflexivity.
         switcher_change_pc_label ".Lswitch_skip_interrupt_disable".
         iApply (switch_skip_interrupt_disable_spec _ _ _ _ _ _ _ _ _ InterruptDisabled with
           "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip $Hmie $Hheld]");
           [done|done|].
         iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hregs & Hmie & Hheld)".
         iApply ("Hpost" $! arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs Hmie"; iFrame; done. }
    switcher_change_pc_label ".Lswitch_skip_interrupt_disable".
    iApply (switch_skip_interrupt_disable_spec _ _ _ _ _ _ _ _ _ InterruptEnabled with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip $Hmie $Hheld]");
      [done|done|].
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hregs & Hmie & Hheld)".
    iApply ("Hpost" $! arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs Hmie"; iFrame; done.
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
    th ≠ CtxSwitch ->

    PC ↦ₚ[th] switcher_label_pc ".Lswitch_load_zero_arguments_start" ∗
    cs0 ↦ᵣ[th] wcs0 ∗
    cs1 ↦ᵣ[th] wcs1 ∗
    ct1 ↦ᵣ[th] wct1 ∗
    ct2 ↦ᵣ[th] wct2 ∗
    ctp ↦ᵣ[th] WInt (entry_point_flags posture (Z.of_nat nargs)) ∗
    cra ↦ᵣ[th] Cap RX Global bpcc epcc a_tgt ∗
    regs[th] arg_rmap ∗
    regs[th] rmap ∗
    (b_switcher ^+ 5) ↦ₐ□ SealRange (true,false) Local ot_interrupt_sentries
      (ot_interrupt_sentries ^+ 1) ot_interrupt_sentries ∗
    switcher_code ∗
    MIE ↦ₜ[th] InterruptEnabled ∗
    held (th := th) InterruptEnabled ∗
    ▷ ( ∀ (arg_rmap' rmap' : LReg),
        ⌜ is_arg_rmap arg_rmap' 8 ⌝ ∗
        ⌜ dom rmap' = all_registers_s ∖ (dom_arg_rmap 8 ∪ {[ cra ; cgp ; csp ]}) ⌝ ∗
        PC ↦ₚ[th] Cap RX Global bpcc epcc a_tgt ∗
        cra ↦ᵣ[th] Sentry RetEnable XSRW_ Local b_switcher e_switcher a_switcher_return ∗
        ( [∗ map] r↦w ∈ arg_rmap',
            r ↦ᵣ[th] w ∗ if decide (r ∈ dom_arg_rmap nargs)
                     then ⌜ arg_rmap !! r = Some w ⌝
                     else ⌜ w = WInt 0 ⌝ ) ∗
        regs₀[th] rmap' ∗
        MIE ↦ₜ[th] posture ∗
        held (th := th) posture -∗
        safe[th] )
    ⊢ safe[th].
  Proof.
    iIntros (Hnargs Hargs Hdom Hth)
      "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hctp & Hcra & Hargs & Hregs & #Hsentries_key
      & #Hswitcher & Hmie & Hheld & Hpost)".
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
    { intros Hcs; by destruct Hth. }
    iEval (cbn [jalr_target_mie default lw]) in "Hmie Hheld".
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
    (* Jeq .Lswitch_skip_interrupt_disable ct1 0 *)
    all: iInstr "Hcode".
    2: { (* Auipcc ctp .sealing_key_interrupt_sentries *)
         iInstr "Hcode".
         { instantiate (1 := b_switcher ^+ 5). switcher_addr_eq. }
         (* CLoad ctp ctp 0 *)
         iInstr "Hcode".
         { apply withinBounds_true_iff.
           pose proof switcher_call_entry_point; pose proof switcher_size; solve_addr. }
         (* Seal cra ctp cra *)
         iInstr "Hcode" using seal_sentry_next_ok_tagged.
         all: try done.
         all: try (apply withinBounds_true_iff; solve_finz).
         all: try reflexivity.
         switcher_change_pc_label ".Lswitch_skip_interrupt_disable".
         iApply (switch_skip_interrupt_disable_spec _ _ _ _ _ _ _ _ _ InterruptDisabled with
           "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip $Hmie $Hheld]");
           [done|done|].
         iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hregs & Hmie & Hheld)".
         iApply ("Hpost" $! arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs Hmie"; iFrame; done. }
    switcher_change_pc_label ".Lswitch_skip_interrupt_disable".
    iApply (switch_skip_interrupt_disable_spec _ _ _ _ _ _ _ _ _ InterruptEnabled with
      "[- $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hctp $Hcra $Hregs $Hswitcher_skip $Hmie $Hheld]");
      [done|done|].
    iNext; iIntros (rmap') "(%Hrmap' & HPC & Hcra & Hregs & Hmie & Hheld)".
    iApply ("Hpost" $! arg_rmap' rmap'); iFrame "HPC Hcra Hargs Hregs Hmie"; iFrame; done.
  Qed.

End Switcher_Clear_Unused_Args.
