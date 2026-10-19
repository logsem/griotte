From griotte Require Import machine_parameters assembler.
From griotte Require Export clear_stack clear_registers.

Class switcherLayout : Type :=
  mkSwitcherLayout {
      b_switcher : Addr ;
      e_switcher : Addr ;
      a_switcher_call : Addr ;
      a_switcher_return : Addr ;

      ot_switcher : OType ;

      b_trusted_stack : Addr;
      e_trusted_stack : Addr;
    }.

Section Switcher.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  #[local] Coercion Z.of_nat : nat >-> Z.

  Definition ECOMPARTMENTFAIL : Z := -1.
  Definition ENOTENOUGHTRUSTEDSTACK : Z := -141.

  (** The layout of the trusted stack, with CHERIoT's names (with
      [CONFIG_MSHWM]), counted in words: each field takes one word, including
      the 32-bit fields that CHERIoT packs in pairs. mtdc holds a capability
      to the base of the trusted stack, which starts with the register save
      area: [mepcc], the registers x1 to x15 (register xi at word i),
      [hazardPointers], [mstatus], [mcause], [mshwm] and [mshwmb]. It is
      followed by the header ([frameoffset], the offset from the base of the
      next free frame, and [threadID]) and by the frames. A frame holds the
      stack pointer of the caller, the export table of the callee and the
      number of error handlers invoked. The first frame, [frames[0]], is the
      entry frame of the thread, which the return path never pops. *)
  Definition TrustedStack_offset_mepcc : Z := 0.
  Definition TrustedStack_offset_cra : Z := 1.
  Definition TrustedStack_offset_csp : Z := 2.
  Definition TrustedStack_offset_cgp : Z := 3.
  Definition TrustedStack_offset_ctp : Z := 4.
  Definition TrustedStack_offset_ct0 : Z := 5.
  Definition TrustedStack_offset_ct1 : Z := 6.
  Definition TrustedStack_offset_ct2 : Z := 7.
  Definition TrustedStack_offset_cs0 : Z := 8.
  Definition TrustedStack_offset_cs1 : Z := 9.
  Definition TrustedStack_offset_ca0 : Z := 10.
  Definition TrustedStack_offset_ca1 : Z := 11.
  Definition TrustedStack_offset_ca2 : Z := 12.
  Definition TrustedStack_offset_ca3 : Z := 13.
  Definition TrustedStack_offset_ca4 : Z := 14.
  Definition TrustedStack_offset_ca5 : Z := 15.
  Definition TrustedStack_offset_hazardPointers : Z := 16.
  Definition TrustedStack_offset_mstatus : Z := 17.
  Definition TrustedStack_offset_mcause : Z := 18.
  Definition TrustedStack_offset_mshwm : Z := 19.
  Definition TrustedStack_offset_mshwmb : Z := 20.
  Definition TSTACK_REGFRAME_SZ : Z := 21.
  Definition TSTACK_HEADER_SZ : Z := 2.
  Definition TrustedStack_offset_frameoffset : Z := TSTACK_REGFRAME_SZ.
  Definition TrustedStack_offset_threadID : Z := TSTACK_REGFRAME_SZ + 1.
  Definition TrustedStack_offset_frames : Z := TSTACK_REGFRAME_SZ + TSTACK_HEADER_SZ.
  Definition TrustedStackFrame_offset_csp : Z := 0.
  Definition TrustedStackFrame_offset_calleeExportTable : Z := 1.
  Definition TrustedStackFrame_offset_errorHandlerCount : Z := 2.
  Definition TrustedStackFrame_size : Z := 3.

  (** The offset of [frames[d]] from the base of the trusted stack. *)
  Definition tstack_frame_offset (d : nat) : Z :=
    TrustedStack_offset_frames + TrustedStackFrame_size * Z.of_nat d.

  (** The value of [frameoffset] when the call-stack has [d] frames: the
      offset of the frame after the topmost one, the entry frame being
      below the [d] frames. *)
  Definition tstack_frameoffset (d : nat) : Z :=
    TrustedStack_offset_frames + TrustedStackFrame_size * (Z.of_nat d + 1).

  (** An entry point packs the number of arguments in bits 0-2, the
      interrupt posture in bits 3-4 and the offset from bit 5, as CHERIoT's
      export entries do. Bit 4 is set when the callee runs with interrupts
      disabled; bit 3 (inherited posture) is never set, since export entries
      cannot inherit. *)
  Definition entry_point_irq_disabled_mask : Z := 16.

  Definition entry_point_posture (mie : InterruptStatus) : Z :=
    match mie with
    | InterruptEnabled => 0
    | InterruptDisabled => entry_point_irq_disabled_mask
    end.

  Definition encode_entry_point (mie : InterruptStatus) (nargs entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 5 in
    (Z.lor off (Z.lor (entry_point_posture mie) args)).

  Definition decode_entry_point (entry_point : Z) : (Z * Z) :=
    ( Z.land entry_point 7, Z.shiftr entry_point 5).

  Definition switcher_call_asm : list (list asm_code) :=
    (* Call *)
    [
      (* Check permissions of the stack *)
      [ (* The sealing key, one word before the first instruction. *)
        #@".Lswitcher_unseal_key";
        #".Lswitcher_csp_check_perm";
        getp ct2 csp;
        mov ctp (encodePerm RWL);
        sub ct2 ct2 ctp;
        jnz (".Lcommon_force_unwind")%asm ct2
      ]
      ; (* Check permissions of the stack *)
      [ #".Lswitcher_csp_check_loc";
        getl ct2 csp;
        mov ctp (encodeLoc Local);
        sub ct2 ct2 ctp;
        jnz (".Lcommon_force_unwind")%asm ct2
      ]
      ; (* Save the callee registers *)
      [ #".Lswitcher_entry_first_spill";
        store csp cs0;
        lea csp 1;
        store csp cs1;
        lea csp 1;
        store csp cra;
        lea csp 1;
        store csp cgp;
        lea csp 1
      ]
      ; (* Check that the trusted stack has room for a frame, and push it *)
      [ #".Lswitcher_trusted_stack_push";
        readsr ct2 mtdc;
        load_imm ctp ct2 TrustedStack_offset_frameoffset;
        (* The length of the trusted stack *)
        gete cs0 ct2;
        getb cs1 ct2;
        sub cs0 cs0 cs1;
        lt cs0 ctp cs0; (* if (frameoffset < length) then (cs0 := 1) else (cs0 := 0) *)
        jnz 2 cs0;
        #".Lswitcher_trusted_stack_full";
        jmp (".Lswitch_trusted_stack_exhausted")%asm;
        (* ctp points to the new frame *)
        mov cs1 ctp;
        mov ctp ct2;
        lea ctp cs1;
        store_imm ctp csp TrustedStackFrame_offset_csp;
        store_imm ctp 0 TrustedStackFrame_offset_errorHandlerCount;
        store_imm ctp 0 TrustedStackFrame_offset_calleeExportTable;
        (* Increment the frame offset *)
        load_imm cs0 ct2 TrustedStack_offset_frameoffset;
        add cs0 cs0 TrustedStackFrame_size;
        store_imm ct2 cs0 TrustedStack_offset_frameoffset
      ]
      ; (* Chop off the stack *)
      [ #".Lswitcher_chop_stack";
        gete cs0 csp;
        geta cs1 csp;
        subseg csp cs1 cs0
      ]
      ; (* Zero out the callee's stack frame *)
      (#".Lswitcher_zero_callee_stack" :: clear_stack_asm cs0 cs1)
      ; (* Fetch (unsealing capability and unseal entry point *)
      [ #".Lswitcher_fetch_unseal_key";
        auipcc cs0 (".Lswitcher_unseal_key")%asm;
        load cs0 cs0
      ]
      ; (* CLoad and decode entry point nargs and offset *)
      [ #".Lswitcher_unseal_entry";
        unseal ct1 cs0 ct1;
        #".Lswitcher_decode_entry";
        load cs0 ct1;
        (* Store the export table of the callee in the new frame *)
        store_imm ctp ct1 TrustedStackFrame_offset_calleeExportTable;
        land ct2 cs0 7;
        land ctp cs0 entry_point_irq_disabled_mask;
        lshiftr cs0 cs0 5
      ]
      ; (* Prepare callee's PCC in cra, and callee's CGP in cgp *)
      [ #".Lswitcher_prepare_callee";
        getb cgp ct1;
        geta cs1 ct1;
        sub cs1 cgp cs1;
        lea ct1 cs1;
        load cra ct1;
        lea ct1 1;
        load cgp ct1;
        lea cra cs0;
        add ct2 ct2 1
      ]
      ; (* Clear ununsed arguments registers *)
      (#".Lswitcher_clear_unused_args" :: clear_registers_pre_call_skip_asm)
      ; (* Enable interrupts, unless the entry point asks for them disabled *)
      [ #".Lswitcher_enable_interrupts";
        jnz (".Lswitcher_clear_registers")%asm ctp;
        csrsi mstatus (Z.shiftl 1 MIE_BIT)
      ]
      ; (* Clear non-arguments registers  *)
      (#".Lswitcher_clear_registers" :: clear_registers_pre_call_asm)
      ; (* Jump to callee *)
      [ #".Lswitcher_call_callee";
        jalr cra cra ]
    ].

  Definition switcher_callback_asm : list (list asm_code) :=
    (* Callback *)
    [
      (* Return from the callee *)
      [
        #".Lswitcher_after_compartment_call";
        readsr ctp mtdc;
        (* The offset of the frame to pop *)
        load_imm ct2 ctp TrustedStack_offset_frameoffset;
        mov ct0 TrustedStack_offset_frames;
        add ct2 ct2 (- TrustedStackFrame_size)%Z;
        (* Exit the thread when the frame to pop is the entry frame *)
        lt ct0 ct0 ct2;
        jnz 2 ct0;
        jmp (".Lcommon_defer_irqs_and_thread_exit")%asm;
        (* Restore the caller's stack pointer and pop the frame *)
        mov ct1 ctp;
        lea ct1 ct2;
        load_imm csp ct1 TrustedStackFrame_offset_csp;
        store_imm ctp ct2 TrustedStack_offset_frameoffset;

        (* Restores the caller's saved registers *)
        lea csp (-1)%Z;
        #".Lswitcher_restore_cgp";
        load cgp csp;
        lea csp (-1)%Z;
        load cra csp;
        lea csp (-1)%Z;
        load cs1 csp;
        lea csp (-1)%Z;
        load cs0 csp;

        (* Zero out the callee stack frame *)
        gete ct0 csp;
        geta ct1 csp
      ]
      ; (* Clear the callee's stack frame  *)
      (#".Lswitcher_zero_callee_frame" :: clear_stack_asm ct0 ct1)
      ; (* Clear the register file *)
      (#".Lswitch_callee_dead_zeros"::clear_registers_post_call_asm)
      ; (* Return to caller  *)
      [ #".Lswitcher_return_to_caller";
        ret ]
    ].

  Definition switcher_failure_asm : list (list asm_code) :=
    (* Failure *)
    [ (* Trusted stack is exhausted: return to caller *)
      [ #".Lswitch_trusted_stack_exhausted";
        lea csp (-1)%Z;
        load cgp csp;
        lea csp (-1)%Z;
        load cra csp;
        lea csp (-1)%Z;
        load cs1 csp;
        lea csp (-1)%Z;
        load cs0 csp;
        mov ca0 ENOTENOUGHTRUSTEDSTACK;
        mov ca1 0;
        #".Lswitch_trusted_stack_exhausted_return";
        jmp (".Lswitch_callee_dead_zeros")%asm
      ]
      ; (* Force unwind: return to caller's caller *)
      [ #".Lcommon_force_unwind";
        mov ca0 ECOMPARTMENTFAIL;
        mov ca1 0;
        #".Lcommon_force_unwind_return";
        jmp (".Lswitcher_after_compartment_call")%asm
      ]
      ; (* Exit the thread, with interrupts disabled *)
      [ #".Lcommon_defer_irqs_and_thread_exit";
        csrci mstatus (Z.shiftl 1 MIE_BIT);
        #".Lcommon_thread_exit";
        halt
      ]
    ].

  Definition switcher_asm : list (list asm_code) :=
    switcher_call_asm ++
    switcher_callback_asm ++
    switcher_failure_asm.

  Definition assembled_switcher :=
    Eval compute in assemble_block switcher_asm.
  Lemma switcher_assembles : asm_ok (assemble_block_check switcher_asm).
  Proof. asm_check. Qed.
  Definition assembled_switcher_n (n : nat) :=
    Eval compute in
      (match assembled_switcher !! n with | Some l => l | None => [] end).
  Definition switcher_instrs : list Word :=
   concat (encodeInstrsW <$> assembled_switcher).
  Definition switcher_instrs_n (n : nat) :=
   encodeInstrsW (assembled_switcher_n n).

  Definition switcher_call_instrs :=
      Eval compute in
      let blocks_call_asm := length switcher_call_asm in
      concat (firstn blocks_call_asm assembled_switcher).


  Class switcherLayoutWf `{!switcherLayout} : Type :=
    mkSwitcherLayoutWf {
        switcher_size :
        (a_switcher_call + length switcher_instrs)%a = Some e_switcher ;

        switcher_call_entry_point :
        (b_switcher + 1)%a = Some a_switcher_call ;

        switcher_return_entry_point :
        (b_switcher + (1 + length switcher_call_instrs) )%a = Some a_switcher_return ;

        ot_switcher_size :
        (ot_switcher < ot_switcher ^+ 1)%ot;

        trusted_stack_disjoint_from_shadow :
        disjoint_from_shadow b_trusted_stack e_trusted_stack;

        switcher_base_not_shadow : is_shadow_address b_switcher = false;
        switcher_not_heap_range : not_heap_range b_switcher e_switcher;
        (* The register save area of the trusted stack is not in the heap. *)
        trusted_stack_not_heap :
        not_heap_range b_trusted_stack (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a;
        (* The trusted stack holds its header, the entry frame and a whole
           number of frames. *)
        trusted_stack_frames_fit :
        ∃ n : nat,
          (b_trusted_stack + tstack_frame_offset (S n))%a = Some e_trusted_stack
      }.

  Lemma switcher_base_not_heap
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf} :
    is_heap_address b_switcher = false.
  Proof. exact (proj1 switcher_not_heap_range). Qed.

  Lemma switcher_disjoint_from_heap
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf} :
    disjoint_from_heap b_switcher e_switcher.
  Proof. exact (proj2 switcher_not_heap_range). Qed.

  Lemma switcher_call_sentry_not_heap
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf} :
    is_heap_cap (WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_switcher_call) = false.
  Proof.
    rewrite /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=.
    reflexivity.
  Qed.

End Switcher.

(** Unfold the constants of the layout of the trusted stack, everywhere. *)
Ltac tstack_unfold :=
  unfold tstack_frame_offset, tstack_frameoffset,
    TrustedStack_offset_frameoffset, TrustedStack_offset_threadID, TrustedStack_offset_frames,
    TSTACK_REGFRAME_SZ, TSTACK_HEADER_SZ, TrustedStackFrame_offset_csp,
    TrustedStackFrame_offset_calleeExportTable,
    TrustedStackFrame_offset_errorHandlerCount, TrustedStackFrame_size in *.
