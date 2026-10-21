From griotte Require Import machine_parameters assembler.
From griotte Require Import griotte_opsem.
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
  Definition ENOTENOUGHSTACK : Z := -140.
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

  (** The word of the register save area of the register xi: word i. *)
  Definition TrustedStack_offset_reg (r : RegName) : Z :=
    match r with registers.R n _ => Z.of_nat n end.

  (** CHERIoT's [trustedSpillRegisters]: spill the registers [regs], in
      order, to the register save area of the trusted stack in [csp]. *)
  Definition trusted_spill_registers_asm (regs : list RegName) : list asm_code :=
    macro: ((λ r : RegName, store_imm csp r (TrustedStack_offset_reg r)) <$> regs).

  (** CHERIoT's [trustedReloadRegisters]: reload the registers [regs], in
      order, from the register save area of the trusted stack in [csp]. *)
  Definition trusted_reload_registers_asm (regs : list RegName) : list asm_code :=
    macro: ((λ r : RegName, load_imm r csp (TrustedStack_offset_reg r)) <$> regs).

  Definition trusted_spill_registers (regs : list RegName) : list instr :=
    (λ r : RegName, machine_instructions.Store csp (inr r) (TrustedStack_offset_reg r)) <$> regs.
  Definition trusted_spill_registers_instrs (regs : list RegName) : list Word :=
    encodeInstrsW (trusted_spill_registers regs).
  Definition trusted_reload_registers (regs : list RegName) : list instr :=
    (λ r : RegName, machine_instructions.CLoad r csp (TrustedStack_offset_reg r)) <$> regs.
  Definition trusted_reload_registers_instrs (regs : list RegName) : list Word :=
    encodeInstrsW (trusted_reload_registers regs).

  (** The registers of the interrupted context that the exception entry
      spills first: all but [csp], which is still in mtdc. *)
  Definition exception_spill_regs : list RegName :=
    [cra; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5].

  Lemma trusted_spill_registers_assembles :
    asm_ok (assemble_check (trusted_spill_registers_asm exception_spill_regs)).
  Proof. asm_check. Qed.

  Lemma trusted_reload_registers_assembles :
    asm_ok (assemble_check (trusted_reload_registers_asm exception_spill_regs)).
  Proof. asm_check. Qed.

  (** The layout of an export table, counted in words: the PCC and the CGP
      of the compartment, the offsets of its stackful and stackless error
      handlers ([0xffff] for none; one word each, where CHERIoT has 16-bit
      fields), then the export entries. *)
  Definition ExportTable_offset_pcc : Z := 0.
  Definition ExportTable_offset_cgp : Z := 1.
  Definition ExportTable_offset_errorHandler : Z := 2.
  Definition ExportTable_offset_errorHandlerStackless : Z := 3.
  Definition ExportTable_offset_entries : Z := 4.

  (** The handler offset of a compartment that declares no handler. *)
  Definition ExportTable_no_handler : Z := 0xffff.

  (** [w] is a readable capability to the export table at [b], whose bounds
      cover the header of the table and avoid the shadow table: the switcher
      reads the header through it, from its base. *)
  Definition exp_tbl_cap (b : Addr) (w : Word) : Prop :=
    ∃ p g e a, w = WCap true p g b e a ∧ readAllowed p = true ∧
               (b ^+ ExportTable_offset_errorHandlerStackless < e)%a ∧
               disjoint_from_shadow b e.

  (** The unsealed export entry, as the call path stores it. *)
  Lemma exp_tbl_cap_entry g b e a :
    (b ^+ ExportTable_offset_errorHandlerStackless < a)%a →
    (a < e)%a →
    disjoint_from_shadow b e →
    exp_tbl_cap b (WCap true RO g b e a).
  Proof.
    intros Hb Ha Hshadow. eexists _, _, _, _.
    split_and!; [done | done | | done].
    unfold ExportTable_offset_errorHandlerStackless in *; solve_addr.
  Qed.

  (** The offset of the [k]-th export entry in an export table. *)
  Definition ExportTable_offset_entry (k : nat) : Z := ExportTable_offset_entries + Z.of_nat k.

  (** The offset of [frames[d]] from the base of the trusted stack. *)
  Definition tstack_frame_offset (d : nat) : Z :=
    TrustedStack_offset_frames + TrustedStackFrame_size * Z.of_nat d.

  (** The value of [frameoffset] when the call-stack has [d] frames: the
      offset of the frame after the topmost one, the entry frame being
      below the [d] frames. *)
  Definition tstack_frameoffset (d : nat) : Z :=
    TrustedStack_offset_frames + TrustedStackFrame_size * (Z.of_nat d + 1).

  (** An entry point packs, as CHERIoT's export entries do, the flags in
      bits 0-7, the minimum stack size of the callee in bits 8-15 and the
      offset from bit 16. The flags hold the number of arguments in bits 0-2
      and the interrupt posture in bits 3-4. Bit 4 is set when the callee runs
      with interrupts disabled; bit 3 (inherited posture) is never set, since
      export entries cannot inherit. The minimum stack size is counted in
      words, one word being one CHERIoT stack slot of 8 bytes. *)
  Definition entry_point_irq_disabled_mask : Z := 16.

  Definition entry_point_posture (mie : InterruptStatus) : Z :=
    match mie with
    | InterruptEnabled => 0
    | InterruptDisabled => entry_point_irq_disabled_mask
    end.

  Definition encode_entry_point
    (mie : InterruptStatus) (nargs minstk entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let stk := Z.shiftl (Z.land minstk 255) 8 in
    let off := Z.shiftl entry_point_offset 16 in
    (Z.lor off (Z.lor stk (Z.lor (entry_point_posture mie) args))).

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
      ; (* Save the callee registers. The first spill goes to the cell
           furthest from the cursor: if it fits, the stack is long enough
           for the others. A cursor below the base can still make a later
           store fault. *)
      [ #".Lswitcher_entry_first_spill";
        store_imm csp cgp 3;
        store_imm csp cs0 0;
        store_imm csp cs1 1;
        store_imm csp cra 2;
        lea csp 4
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
      ; (* CLoad and decode entry point nargs, minimum stack size and offset;
           check the size of the callee's stack *)
      [ #".Lswitcher_unseal_entry";
        unseal ct1 cs0 ct1;
        #".Lswitcher_decode_entry";
        load cs0 ct1;
        (* Store the export table of the callee in the new frame *)
        store_imm ctp ct1 TrustedStackFrame_offset_calleeExportTable;
        land ct2 cs0 7;
        land ctp cs0 entry_point_irq_disabled_mask;
        (* Check that the callee's stack, already truncated, is at least
           the minimum stack size of the entry point. CHERIoT also requires
           room for the unwind state of error handlers, which is not
           modelled. *)
        lshiftr cs1 cs0 8;
        land cs1 cs1 255;
        gete cgp csp;
        getb cra csp;
        sub cgp cgp cra;
        lt cra cgp cs1;
        #".Lswitch_stack_too_small_branch";
        jnz (".Lswitch_stack_too_small")%asm cra;
        lshiftr cs0 cs0 16
      ]
      ; (* Prepare callee's PCC in cra, and callee's CGP in cgp *)
      [ #".Lswitcher_prepare_callee";
        getb cgp ct1;
        geta cs1 ct1;
        sub cs1 cgp cs1;
        lea ct1 cs1;
        load cra ct1;
        lea ct1 ExportTable_offset_cgp;
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
      ; (* The callee's stack is smaller than the minimum stack size of the
           entry point: the frame is already pushed, so the return routine
           pops it and returns to the caller. *)
      [ #".Lswitch_stack_too_small";
        mov ca0 ENOTENOUGHSTACK;
        mov ca1 0;
        #".Lswitch_stack_too_small_return";
        jmp (".Lswitcher_after_compartment_call")%asm
      ]
    ].

  Definition switcher_exception_asm : list (list asm_code) :=
    [ (* Exception entry: swap the trusted stack in from mtdc. A null
         mtdc means that the exception entry was re-entered. *)
      [ #"exception_entry_asm";
        specialrw csp mtdc csp;
        jnz 2 csp;
        jmp (".Lexception_reentered")%asm
      ]
      ; (* Spill the registers of the interrupted context in the register
           save area, but the stack pointer *)
      (#".Lexception_spill_registers" :: trusted_spill_registers_asm exception_spill_regs)
      ; (* Spill the interrupted stack pointer, from mtdc, which is
           cleared, then the PC, mstatus and the cause of the trap. A cause
           handled by the compartments (a CHERI fault or a cause below 8)
           goes to [.Lhandle_error]; any other goes to the scheduler. *)
      [ #".Lexception_exiting_threads_rejoin";
        mov ct1 0;
        specialrw ct1 mtdc ct1;
        store_imm csp ct1 TrustedStack_offset_csp;
        readsr ct0 mepcc;
        store_imm csp ct0 TrustedStack_offset_mepcc;
        csrr ct1 mstatus;
        store_imm csp ct1 TrustedStack_offset_mstatus;
        csrr ct1 mcause;
        store_imm csp ct1 TrustedStack_offset_mcause;
        mov ca0 MCAUSE_CHERI;
        sub ca0 ca0 ct1;
        jnz 2 ca0;
        jmp (".Lhandle_error")%asm;
        mov ca0 8;
        lt ca0 ct1 ca0;
        jnz (".Lhandle_error")%asm ca0;
        jmp (".Lexception_scheduler_call")%asm
      ]
      ; (* A trap to be handled by the compartments: restore mtdc, then force
         the unwind of the faulting compartment's call. A fault of the
         switcher (whose PC has the base of the switcher's PC) goes to
         [.Lhandle_error_in_switcher]. With no frame on the trusted stack,
         the thread exits. *)
      [ #".Lhandle_error";
        writesr mtdc csp;
        auipcc ct0 0;
        load_imm ct1 csp TrustedStack_offset_mepcc;
        getb ct0 ct0;
        getb ctp ct1;
        sub ct0 ct0 ctp;
        jnz 2 ct0;
        jmp (".Lhandle_error_in_switcher")%asm;
        load_imm ct0 csp TrustedStack_offset_csp;
        load_imm ctp csp TrustedStack_offset_frameoffset;
        mov ct1 TrustedStack_offset_frames;
        sub ct1 ctp ct1;
        jnz 2 ct1;
        jmp (".Lcommon_thread_exit")%asm;
        jmp (".Lcommon_force_unwind")%asm
      ]
      ; (* A fault of the switcher: force the unwind *)
      [ #".Lhandle_error_in_switcher";
        jmp (".Lcommon_force_unwind")%asm
      ]
      ; (* The exception entry was re-entered: stop the machine *)
      [ #".Lexception_reentered";
        halt
      ]
      ; (* A trap for the scheduler: stop the machine *)
      [ #".Lexception_scheduler_call";
        halt
      ]
    ].

  Definition switcher_asm : list (list asm_code) :=
    switcher_call_asm ++
    switcher_callback_asm ++
    switcher_failure_asm ++
    switcher_exception_asm.

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
          (b_trusted_stack + tstack_frame_offset (S n))%a = Some e_trusted_stack;
        (* The trusted stack is not at address 0: mtdc is never null. *)
        trusted_stack_base_nonzero : (b_trusted_stack : Z) ≠ 0
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

(** Unfold the constants of the layout of an export table, everywhere. *)
Ltac exptbl_unfold :=
  unfold ExportTable_offset_entry, ExportTable_offset_pcc, ExportTable_offset_cgp,
    ExportTable_offset_errorHandler, ExportTable_offset_errorHandlerStackless,
    ExportTable_offset_entries in *.

(** [solve_addr] sees through the layout of export tables. The hook has a
    single definition: any later redefinition of [solve_addr_prepare] (for
    instance in [kvs.v]) must also call [exptbl_unfold]. *)
#[global] Ltac solve_addr.solve_addr_prepare ::= try exptbl_unfold.
