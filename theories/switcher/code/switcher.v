From griotte Require Import machine_parameters assembler.
From griotte Require Import griotte_opsem.
From griotte Require Export clear_stack copy_context clear_registers export_table_layout.
From griotte Require Export trusted_stack_layout.
From griotte Require Export clear_hazard_slots.

(** The trusted stack and the two hazard slots of a user thread. *)
Class threadLayout : Type :=
  mkThreadLayout {
      b_trusted_stack : Addr;
      e_trusted_stack : Addr;

      (* The two hazard slots of the thread. *)
      b_hazard_slots : Addr;
      e_hazard_slots : Addr;
    }.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

Class switcherLayout : Type :=
  mkSwitcherLayout {
      b_switcher : Addr ;
      e_switcher : Addr ;
      a_switcher_call : Addr ;
      a_switcher_return : Addr ;

      ot_switcher : OType ;

      (* The layout of the user thread [i]. *)
      swl_thread : nat → threadLayout;
    }.

(** The sentry of the switcher's call entry point. *)
Definition switcher_entry_call `{switcherLayout} : Word :=
  Sentry FwdDisable XSRW_ Local b_switcher e_switcher a_switcher_call.

Section Switcher.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  #[local] Coercion Z.of_nat : nat >-> Z.

  (* [deviation] negated: CHERIoT's constants are positive *)
  Definition ECOMPARTMENTFAIL : Z := -1.
  Definition ENOTENOUGHSTACK : Z := -140.
  Definition ENOTENOUGHTRUSTEDSTACK : Z := -141.

  Definition COMPARTMENT_STACK_PERMISSIONS : Z := encodePerm RWL.
  (* [deviation] Griotte's locality is not a permission bit *)
  Definition COMPARTMENT_STACK_LOCALITY : Z := encodeLoc Local.

  (** The number of faults after which the switcher stops invoking the
      handlers of a compartment call, and forces the unwind. *)
  Definition MAX_FAULTS_PER_COMPARTMENT_CALL : Z := 1024.

  (** The size of CHERIoT's [ErrorState] (compartment.h): the PCC and the 15
      registers, one word each. The exception path writes it on the faulting
      stack, just below the faulting cursor. *)
  Definition ErrorState_size : Z := 16.

  (** The word of the register save area of the register xi: word i. *)
  Definition TrustedStack_offset_reg (r : RegName) : Z :=
    match r with registers.R n _ => Z.of_nat n end.

  Lemma TrustedStack_offset_reg_named :
    TrustedStack_offset_reg cra = TrustedStack_offset_cra ∧
    TrustedStack_offset_reg csp = TrustedStack_offset_csp ∧
    TrustedStack_offset_reg cgp = TrustedStack_offset_cgp ∧
    TrustedStack_offset_reg ctp = TrustedStack_offset_ctp ∧
    TrustedStack_offset_reg ct0 = TrustedStack_offset_ct0 ∧
    TrustedStack_offset_reg ct1 = TrustedStack_offset_ct1 ∧
    TrustedStack_offset_reg ct2 = TrustedStack_offset_ct2 ∧
    TrustedStack_offset_reg cs0 = TrustedStack_offset_cs0 ∧
    TrustedStack_offset_reg cs1 = TrustedStack_offset_cs1 ∧
    TrustedStack_offset_reg ca0 = TrustedStack_offset_ca0 ∧
    TrustedStack_offset_reg ca1 = TrustedStack_offset_ca1 ∧
    TrustedStack_offset_reg ca2 = TrustedStack_offset_ca2 ∧
    TrustedStack_offset_reg ca3 = TrustedStack_offset_ca3 ∧
    TrustedStack_offset_reg ca4 = TrustedStack_offset_ca4 ∧
    TrustedStack_offset_reg ca5 = TrustedStack_offset_ca5.
  Proof. done. Qed.

  (** CHERIoT's [trustedSpillRegisters]: spill the registers [regs], in
      order, to the register save area of the trusted stack in [csp]. *)
  Definition trusted_spill_registers_asm (regs : list RegName) : list asm_code :=
    macro: ((λ r : RegName,
               (* csc cr, TrustedStack_offset_cr(csp) *)
               store_imm csp r (TrustedStack_offset_reg r)) <$> regs).

  (** CHERIoT's [trustedReloadRegisters]: reload the registers [regs], in
      order, from the register save area of the trusted stack in [csp]. *)
  Definition trusted_reload_registers_asm (regs : list RegName) : list asm_code :=
    macro: ((λ r : RegName,
               (* clc cr, TrustedStack_offset_cr(csp) *)
               load_imm r csp (TrustedStack_offset_reg r)) <$> regs).

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

  (** [w] is a readable capability to the export table at [b], whose bounds
      cover the header of the table and avoid the shadow table: the switcher
      reads the header through it, from its base. It is neither deep-local
      nor deep-read-only: a load through it gives the word in memory. *)
  Definition exp_tbl_cap (b : Addr) (w : Word) : Prop :=
    ∃ p g e a, w = Cap p g b e a ∧ readAllowed p = true ∧
               (b ^+ ExportTable_offset_errorHandlerStackless < e)%a ∧
               disjoint_from_shadow b e ∧
               isDL p = false ∧ isDRO p = false.

  (** The unsealed export entry, as the call path stores it. *)
  Lemma exp_tbl_cap_entry g b e a :
    (b ^+ ExportTable_offset_errorHandlerStackless < a)%a →
    (a < e)%a →
    disjoint_from_shadow b e →
    exp_tbl_cap b (Cap RO g b e a).
  Proof.
    intros Hb Ha Hshadow. eexists _, _, _, _.
    split_and!; [done | done | | done | done | done].
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
  Definition ExportEntryInterruptStatusSwitcherMask : Z := 16.

  (** [deviation] The fields are packed in one word, not stored at byte
      offsets: the switcher extracts them with these shifts and mask. *)
  Definition ExportEntry_functionStart_shift : Z := 16.
  Definition ExportEntry_minimumStackSize_shift : Z := 8.
  Definition ExportEntry_byte_mask : Z := 255.

  Definition entry_point_posture (mie : InterruptStatus) : Z :=
    match mie with
    | InterruptEnabled => 0
    | InterruptDisabled => ExportEntryInterruptStatusSwitcherMask
    end.

  (** The flags of an entry point, its low byte. *)
  Definition entry_point_flags (mie : InterruptStatus) (nargs : Z) : Z :=
    Z.lor (entry_point_posture mie) (Z.land nargs 7).

  Definition encode_entry_point
    (mie : InterruptStatus) (nargs minstk entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let stk := Z.shiftl (Z.land minstk 255) 8 in
    let off := Z.shiftl entry_point_offset 16 in
    (Z.lor off (Z.lor stk (Z.lor (entry_point_posture mie) args))).

  (** The fields of an export entry word, as [encode_entry_point] packs them
      and as the switcher reads them. *)
  Definition export_entry_flags (z : Z) : Z := Z.land z ExportEntry_byte_mask.
  Definition export_entry_nargs (z : Z) : Z := Z.land z 7.
  Definition export_entry_posture (z : Z) : InterruptStatus :=
    if (Z.land z ExportEntryInterruptStatusSwitcherMask =? 0)%Z
    then InterruptEnabled else InterruptDisabled.
  Definition export_entry_min_stack (z : Z) : Z :=
    Z.land (Z.shiftr z ExportEntry_minimumStackSize_shift) ExportEntry_byte_mask.
  Definition export_entry_offset (z : Z) : Z := Z.shiftr z ExportEntry_functionStart_shift.

  Definition switcher_call_asm : list (list asm_code) :=
    [
      [ #@".sealing_key_trusted_stacks";
        #@".unsealing_key_import_tables";
        #@".scheduler_entry_pcc";
        #@".scheduler_entry_cgp";
        #@".scheduler_entry_csp" ]
      ++
      [ #".Lswitch_csp_check";
        (* cgetperm t2, csp *)
        getp ct2 csp;
        (* li tp, COMPARTMENT_STACK_PERMISSIONS *)
        mov ctp COMPARTMENT_STACK_PERMISSIONS;
        (* bne tp, t2, .Lcommon_force_unwind *)
        jne (".Lcommon_force_unwind")%asm ctp ct2;
        (* [deviation] the locality is not a permission bit: a second test *)
        getl ct2 csp;
        mov ctp COMPARTMENT_STACK_LOCALITY;
        jne (".Lcommon_force_unwind")%asm ctp ct2
        (* [deviation] word memory: no alignment check *)
      ]
      ; [ #".Lswitch_entry_first_spill";
        (* csc cs0, (SPILL_SLOT_cs0-SPILL_SLOT_SIZE)(csp) *)
        store_imm csp cs0 (SpillSlot_cs0 - SpillSlot_size)%Z;
        (* cincoffset csp, csp, -SPILL_SLOT_SIZE *)
        lea csp csp (- SpillSlot_size)%Z;
        (* csc cs1, SPILL_SLOT_cs1(csp) *)
        store_imm csp cs1 SpillSlot_cs1;
        (* csc cgp, SPILL_SLOT_cgp(csp) *)
        store_imm csp cgp SpillSlot_cgp;
        (* csc cra, SPILL_SLOT_pcc(csp) *)
        store_imm csp cra SpillSlot_pcc
      ]
      ; [ #".Lswitch_trusted_stack_load";
        (* cspecialr ct2, mtdc *)
        readsr ct2 mtdc ] ++
      (* clear_hazard_slots ct2, ctp *)
      clear_hazard_slots_asm ct2 ctp
      ; [ #".Lswitch_trusted_stack_push";
        (* clhu tp, TrustedStack_offset_frameoffset(ct2) *)
        load_imm ctp ct2 TrustedStack_offset_frameoffset;
        (* cgetlen s0, ct2 *)
        getlen cs0 ct2;
        (* bgeu tp, s0, .Lswitch_trusted_stack_exhausted *)
        jge (".Lswitch_trusted_stack_exhausted")%asm ctp cs0;
        (* cincoffset ctp, ct2, tp *)
        lea ctp ct2 ctp;
        (* csc csp, TrustedStackFrame_offset_csp(ctp) *)
        store_imm ctp csp TrustedStackFrame_offset_csp;
        (* csh zero, TrustedStackFrame_offset_errorHandlerCount(ctp) *)
        store_imm ctp 0 TrustedStackFrame_offset_errorHandlerCount;
        (* csc cnull, TrustedStackFrame_offset_calleeExportTable(ctp) *)
        store_imm ctp 0 TrustedStackFrame_offset_calleeExportTable;
        (* clhu s1, TrustedStack_offset_frameoffset(ct2) *)
        load_imm cs1 ct2 TrustedStack_offset_frameoffset;
        (* addi s1, s1, TrustedStackFrame_size *)
        add cs1 cs1 TrustedStackFrame_size;
        (* csh s1, TrustedStack_offset_frameoffset(ct2) *)
        store_imm ct2 cs1 TrustedStack_offset_frameoffset
      ]
      ; [ #".Lswitch_stack_chop";
        (* cgetaddr s0, csp *)
        geta cs0 csp;
        (* cgetbase s1, csp *)
        getb cs1 csp;
        (* csetaddr csp, csp, s1 *)
        seta csp csp cs1;
        (* [deviation] Subseg takes the bounds: one instruction for two *)
        (* sub s1, s0, s1; csetboundsrounddown ct2, csp, s1 *)
        subseg ct2 csp cs1 cs0;
        (* cgettop s0, ct2 *)
        gete cs0 ct2;
        (* [deviation] word memory: no andi s0, s0, 0xfffffff0 *)
        (* csetaddr csp, ct2, s0 *)
        seta csp ct2 cs0;
        (* [deviation] MSHWM is not rounded down to 16 bytes *)
        (* csrr gp, CSR_MSHWM *)
        csrr cgp mshwm;
        (* bge gp, sp, .Lswitch_after_zero *)
        jge (".Lswitch_after_zero")%asm cgp csp;
        (* csetaddr ct2, csp, gp *)
        seta ct2 csp cgp
      ] ++
      (* zero_stack t2, s0, gp *)
      clear_stack_asm ct2 cs0
      ; [ #".Lswitch_after_zero";
        (* LoadCapPCC cs0, .Lunsealing_key_import_tables *)
        auipcc cs0 (".unsealing_key_import_tables")%asm;
        load cs0 cs0
      ]
      ; [ #".Lswitch_unseal_entry";
        (* cunseal ct1, ct1, cs0 *)
        unseal ct1 cs0 ct1;
        #".Lswitcher_decode_entry";
        (* [deviation] one packed entry word: each field is loaded and extracted *)
        (* clhu s0, ExportEntry_offset_functionStart(ct1) *)
        load cs0 ct1;
        lshiftr cs0 cs0 ExportEntry_functionStart_shift;
        (* csc ct1, TrustedStackFrame_offset_calleeExportTable(ctp) *)
        store_imm ctp ct1 TrustedStackFrame_offset_calleeExportTable;
        #".Lswitch_stack_check_length";
        (* clbu tp, ExportEntry_offset_minimumStackSize(ct1) *)
        load ctp ct1;
        lshiftr ctp ctp ExportEntry_minimumStackSize_shift;
        land ctp ctp ExportEntry_byte_mask;
        (* [deviation] minimum stack size in words: no slli tp, tp, 3 *)
        (* cgetlen t2, csp *)
        getlen ct2 csp;
        (* addi tp, tp, STACK_ENTRY_RESERVED_SPACE *)
        add ctp ctp StackEntry_reserved_space;
        (* bgtu tp, t2, .Lswitch_stack_too_small *)
        jgt (".Lswitch_stack_too_small")%asm ctp ct2;
        (* cincoffset csp, csp, -STACK_ENTRY_RESERVED_SPACE *)
        lea csp csp (- StackEntry_reserved_space)%Z;
        (* csrw CSR_MSHWM, sp *)
        csrw mshwm csp;
        (* clbu tp, ExportEntry_offset_flags(ct1) *)
        load ctp ct1;
        land ctp ctp ExportEntry_byte_mask;
        (* cgetbase s1, ct1 *)
        getb cs1 ct1;
        (* csetaddr ct1, ct1, s1 *)
        seta ct1 ct1 cs1
      ]
      ; [ #".Lswitch_callee_load";
        (* clc cgp, ExportTable_offset_cgp(ct1) *)
        load_imm cgp ct1 ExportTable_offset_cgp;
        (* clc cra, ExportTable_offset_pcc(ct1) *)
        load_imm cra ct1 ExportTable_offset_pcc;
        (* cincoffset cra, cra, s0 *)
        lea cra cra cs0
      ]
      ; [ #".Lswitch_load_zero_arguments_start";
        (* auipcc cs0, %cheriot_compartment_hi(.Lswitch_zero_arguments_start) *)
        (* cincoffset cs0, cs0, %cheriot_compartment_lo_i(.Lswitch_load_zero_arguments_start) *)
        auipcc cs0 (".Lswitch_zero_arguments_start")%asm;
        (* andi t2, tp, 0x7 *)
        land ct2 ctp 7;
        (* [deviation] one word per instruction: no sll t2, t2, 1 *)
        (* cincoffset cs0, cs0, t2 *)
        lea cs0 cs0 ct2;
        (* cjr cs0 *)
        jalr cnull cs0;
        #".Lswitch_zero_arguments_start"
      ] ++
      (* zeroRegisters a0, a1, a2, a3, a4, a5, t0 *)
      rclear_asm registers_pre_call_skip ++
      [ (* andi t1, tp, ExportEntryInterruptStatusSwitcherMask *)
        land ct1 ctp ExportEntryInterruptStatusSwitcherMask;
        (* bnez t1, .Lswitch_skip_interrupt_enable *)
        jnez (".Lswitch_skip_interrupt_enable")%asm ct1;
        (* csrsi mstatus, 0x8 *)
        csrsi mstatus (Z.shiftl 1 MIE_BIT)
      ]
      ; (#".Lswitch_skip_interrupt_enable" ::
       #".Lswitch_caller_dead_zeros" ::
       (* zeroRegisters tp, t1, t2, s0, s1 *)
       clear_registers_pre_call_asm)
      ; [ #".Lswitch_callee_call";
        (* cjalr cra *)
        jalr cra cra ]
    ].

  Definition switcher_callback_asm : list (list asm_code) :=
    [
      [ #"switcher_after_compartment_call";
        (* cspecialr ctp, mtdc *)
        readsr ctp mtdc ] ++
      (* clear_hazard_slots ctp, ct2 *)
      clear_hazard_slots_asm ctp ct2 ++
      [ (* clhu t2, TrustedStack_offset_frameoffset(ctp) *)
        load_imm ct2 ctp TrustedStack_offset_frameoffset;
        (* li t0, TrustedStack_offset_frames *)
        mov ct0 TrustedStack_offset_frames;
        (* addi t2, t2, -TrustedStackFrame_size *)
        add ct2 ct2 (- TrustedStackFrame_size)%Z;
        (* bgeu t0, t2, .Lcommon_defer_irqs_and_thread_exit *)
        jge (".Lcommon_defer_irqs_and_thread_exit")%asm ct0 ct2;
        (* cincoffset ct1, ctp, t2 *)
        lea ct1 ctp ct2;
        (* clc csp, TrustedStackFrame_offset_csp(ct1) *)
        load_imm csp ct1 TrustedStackFrame_offset_csp;
        (* csh t2, TrustedStack_offset_frameoffset(ctp) *)
        store_imm ctp ct2 TrustedStack_offset_frameoffset;
        #".Lswitch_callee_save_restore";
        (* clc cs0, SPILL_SLOT_cs0(csp) *)
        load_imm cs0 csp SpillSlot_cs0;
        (* clc cs1, SPILL_SLOT_cs1(csp) *)
        load_imm cs1 csp SpillSlot_cs1;
        (* clc cra, SPILL_SLOT_pcc(csp) *)
        load_imm cra csp SpillSlot_pcc;
        (* clc cgp, SPILL_SLOT_cgp(csp) *)
        load_imm cgp csp SpillSlot_cgp;
        (* cincoffset csp, csp, SPILL_SLOT_SIZE *)
        lea csp csp SpillSlot_size;
        #".Lswitch_callee_stack_zero";
        (* csrr tp, CSR_MSHWM *)
        csrr ctp mshwm;
        (* cgetaddr t1, csp *)
        geta ct1 csp;
        (* csetaddr ct2, csp, tp *)
        seta ct2 csp ctp
      ] ++
      (* zero_stack t2, t1, tp *)
      clear_stack_asm ct2 ct1 ++
      [ (* csrw CSR_MSHWM, sp *)
        csrw mshwm csp ]
      ; (#".Lswitch_callee_dead_zeros" ::
       (* zeroAllRegistersExcept ra, sp, gp, s0, s1, a0, a1 *)
       clear_registers_post_call_asm)
      ; [ #".Lswitch_just_return";
        (* cret *)
        ret ]
      ; [ #".Lswitch_stack_too_small";
        (* li a0, -ENOTENOUGHSTACK *)
        mov ca0 ENOTENOUGHSTACK;
        (* li a1, 0 *)
        mov ca1 0;
        (* j switcher_after_compartment_call *)
        jmp ("switcher_after_compartment_call")%asm
      ]
      ; [ #".Lswitch_trusted_stack_exhausted";
        (* clc cs0, SPILL_SLOT_cs0(csp) *)
        load_imm cs0 csp SpillSlot_cs0;
        (* clc cs1, SPILL_SLOT_cs1(csp) *)
        load_imm cs1 csp SpillSlot_cs1;
        (* clc cra, SPILL_SLOT_pcc(csp) *)
        load_imm cra csp SpillSlot_pcc;
        (* clc cgp, SPILL_SLOT_cgp(csp) *)
        load_imm cgp csp SpillSlot_cgp;
        (* cincoffset csp, csp, SPILL_SLOT_SIZE *)
        lea csp csp SpillSlot_size;
        (* li a0, -ENOTENOUGHTRUSTEDSTACK *)
        mov ca0 ENOTENOUGHTRUSTEDSTACK;
        (* zeroOne a1 *)
        mov ca1 0;
        (* j .Lswitch_callee_dead_zeros *)
        jmp (".Lswitch_callee_dead_zeros")%asm
      ]
    ].

  Definition switcher_exception_asm : list (list asm_code) :=
    [ [ #"exception_entry_asm";
        (* cspecialrw csp, mtdc, csp *)
        specialrw csp mtdc csp;
        (* beqz sp, .Lexception_reentered *)
        jeqz (".Lexception_reentered")%asm csp
      ] ++
      (* trustedSpillRegisters cra, cgp, ctp, ct0, ct1, ct2, cs0, cs1, ca0, ca1, ca2, ca3, ca4, ca5 *)
      trusted_spill_registers_asm exception_spill_regs
      ; [ #".Lexception_exiting_threads_rejoin";
        (* zeroOne t1 *)
        mov ct1 0;
        (* cspecialrw ct1, mtdc, ct1 *)
        specialrw ct1 mtdc ct1;
        (* csc ct1, TrustedStack_offset_csp(csp) *)
        store_imm csp ct1 TrustedStack_offset_csp;
        (* cspecialr ct0, mepcc *)
        readsr ct0 mepcc;
        (* csc ct0, TrustedStack_offset_mepcc(csp) *)
        store_imm csp ct0 TrustedStack_offset_mepcc;
        (* csrr t1, mstatus *)
        csrr ct1 mstatus;
        (* csw t1, TrustedStack_offset_mstatus(csp) *)
        store_imm csp ct1 TrustedStack_offset_mstatus;
        (* csrr t1, CSR_MSHWM *)
        csrr ct1 mshwm;
        (* csw t1, TrustedStack_offset_mshwm(csp) *)
        store_imm csp ct1 TrustedStack_offset_mshwm;
        (* csrr t1, CSR_MSHWMB *)
        csrr ct1 mshwmb;
        (* csw t1, TrustedStack_offset_mshwmb(csp) *)
        store_imm csp ct1 TrustedStack_offset_mshwmb;
        (* csrr t1, mcause *)
        csrr ct1 mcause;
        (* csw t1, TrustedStack_offset_mcause(csp) *)
        store_imm csp ct1 TrustedStack_offset_mcause;
        #".Lexception_might_handle";
        (* li a0, MCAUSE_CHERI *)
        mov ca0 MCAUSE_CHERI;
        (* beq a0, t1, .Lhandle_error *)
        jeq (".Lhandle_error")%asm ca0 ct1;
        (* li a0, 0x8 *)
        mov ca0 8;
        (* bltu t1, a0, .Lhandle_error *)
        jlt (".Lhandle_error")%asm ct1 ca0
      ]
      ; [ #".Lexception_scheduler_call";
        (* [deviation] no scheduler: halt *)
        halt
      ]
      ; (#".Lcommon_context_install" ::
         (* clw ra, TrustedStack_offset_mstatus(csp) *)
         load_imm cra csp TrustedStack_offset_mstatus ::
         (* csrw mstatus, ra *)
         csrw mstatus cra ::
         (* clw ra, TrustedStack_offset_mshwm(csp) *)
         load_imm cra csp TrustedStack_offset_mshwm ::
         (* csrw CSR_MSHWM, ra *)
         csrw mshwm cra ::
         (* clw ra, TrustedStack_offset_mshwmb(csp) *)
         load_imm cra csp TrustedStack_offset_mshwmb ::
         (* csrw CSR_MSHWMB, ra *)
         csrw mshwmb cra ::
         (* cspecialw mepcc, ct2 *)
         writesr mepcc ct2 ::
         (* trustedReloadRegisters cra, cgp, ctp, ct0, ct1, ct2, cs0, cs1, ca0, ca1, ca2, ca3, ca4, ca5, csp *)
         trusted_reload_registers_asm (exception_spill_regs ++ [csp]) ++
         [ (* mret *)
           mret ])
      ; [ #".Lcommon_force_unwind";
        (* li a0, -ECOMPARTMENTFAIL *)
        mov ca0 ECOMPARTMENTFAIL;
        (* li a1, 0 *)
        mov ca1 0;
        (* j switcher_after_compartment_call *)
        jmp ("switcher_after_compartment_call")%asm
      ]
      ; [ #".Lhandle_error";
        (* cspecialw mtdc, csp *)
        writesr mtdc csp;
        #".Lhandle_error_switcher_pcc";
        (* auipcc ct0, 0 *)
        auipcc ct0 0;
        (* clc ct1, TrustedStack_offset_mepcc(csp) *)
        load_imm ct1 csp TrustedStack_offset_mepcc;
        (* cgetbase t0, ct0 *)
        getb ct0 ct0;
        (* cgetbase tp, ct1 *)
        getb ctp ct1;
        (* beq t0, tp, .Lhandle_error_in_switcher *)
        jeq (".Lhandle_error_in_switcher")%asm ct0 ctp;
        #".Lhandle_error_not_switcher";
        (* clc ct0, TrustedStack_offset_csp(csp) *)
        load_imm ct0 csp TrustedStack_offset_csp;
        (* clhu tp, TrustedStack_offset_frameoffset(csp) *)
        load_imm ctp csp TrustedStack_offset_frameoffset;
        (* li t1, TrustedStack_offset_frames *)
        mov ct1 TrustedStack_offset_frames;
        (* beq tp, t1, .Lcommon_thread_exit *)
        jeq (".Lcommon_thread_exit")%asm ctp ct1;
        (* addi tp, tp, -TrustedStackFrame_size *)
        add ctp ctp (- TrustedStackFrame_size)%Z;
        (* cincoffset ctp, csp, tp *)
        lea ctp csp ctp;
        (* li a0, 0 *)
        mov ca0 0;
        (* cincoffset ct0, ct0, -(16*8) *)
        lea ct0 ct0 (- ErrorState_size)%Z
      ]
      ; [ #".Lhandle_error_stack_oob";
        (* cgettag t1, ct0 *)
        gettag ct1 ct0;
        (* li s1, 0xffff *)
        mov cs1 ExportTable_no_handler;
        (* beqz t1, .Lhandle_error_try_stackless *)
        jeqz (".Lhandle_error_try_stackless")%asm ct1;
        (* [deviation] Lea keeps the tag below the base: explicit base check *)
        getb ct2 ct0;
        jlt (".Lhandle_error_try_stackless")%asm ct0 ct2
      ]
      ; [ (* [deviation] CHERIoT's label is at the bne *)
        #".Lhandle_error_try_stackful";
        (* clc ct1, TrustedStackFrame_offset_calleeExportTable(ctp) *)
        load_imm ct1 ctp TrustedStackFrame_offset_calleeExportTable;
        (* cgetbase s0, ct1 *)
        getb cs0 ct1;
        (* csetaddr ct1, ct1, s0 *)
        seta ct1 ct1 cs0;
        (* clhu s0, ExportTable_offset_errorHandler(ct1) *)
        load_imm cs0 ct1 ExportTable_offset_errorHandler;
        (* bne s0, s1, .Lhandle_error_found *)
        jne (".Lhandle_error_found")%asm cs0 cs1
      ]
      ; [ #".Lhandle_error_try_stackless";
        (* clc ct1, TrustedStackFrame_offset_calleeExportTable(ctp) *)
        load_imm ct1 ctp TrustedStackFrame_offset_calleeExportTable;
        (* cgetbase s0, ct1 *)
        getb cs0 ct1;
        (* csetaddr ct1, ct1, s0 *)
        seta ct1 ct1 cs0;
        (* clhu s0, ExportTable_offset_errorHandlerStackless(ct1) *)
        load_imm cs0 ct1 ExportTable_offset_errorHandlerStackless;
        (* beq s0, s1, .Lcommon_force_unwind *)
        jeq (".Lcommon_force_unwind")%asm cs0 cs1;
        (* clc ct0, TrustedStackFrame_offset_csp(ctp) *)
        load_imm ct0 ctp TrustedStackFrame_offset_csp;
        (* cincoffset cs1, csp, TrustedStack_offset_frames *)
        lea cs1 csp TrustedStack_offset_frames;
        (* beq s1, tp, .Lhandle_stack_recovered *)
        jeq (".Lhandle_stack_recovered")%asm cs1 ctp
      ]
      ; [ #".Lhandle_stack_rebound";
        (* cgetaddr a1, ct0 *)
        geta ca1 ct0;
        (* cgetbase a2, ct0 *)
        getb ca2 ct0;
        (* csetaddr ct0, ct0, a2 *)
        seta ct0 ct0 ca2;
        (* [deviation] Subseg takes the bounds: one instruction for two *)
        (* sub a1, a1, a2; csetboundsexact ct0, ct0, a1 *)
        subseg ct0 ct0 ca2 ca1
      ]
      ; [ #".Lhandle_stack_recovered";
        (* li a0, 1 *)
        mov ca0 1
      ]
      ; [ #".Lhandle_error_found";
        (* clhu s1, TrustedStackFrame_offset_errorHandlerCount(ctp) *)
        load_imm cs1 ctp TrustedStackFrame_offset_errorHandlerCount;
        (* addi s1, s1, 1 *)
        add cs1 cs1 1;
        (* csh s1, TrustedStackFrame_offset_errorHandlerCount(ctp) *)
        store_imm ctp cs1 TrustedStackFrame_offset_errorHandlerCount;
        #".Lhandle_error_test_double_fault";
        (* andi ra, s1, 1 *)
        land cra cs1 1;
        (* beqz ra, .Lcommon_force_unwind *)
        jeqz (".Lcommon_force_unwind")%asm cra;
        #".Lhandle_error_test_too_many";
        (* li ra, MAX_FAULTS_PER_COMPARTMENT_CALL *)
        mov cra MAX_FAULTS_PER_COMPARTMENT_CALL;
        (* bgtu s1, ra, .Lcommon_force_unwind *)
        jgt (".Lcommon_force_unwind")%asm cs1 cra;
        (* clc cra, ExportTable_offset_pcc(ct1) *)
        load_imm cra ct1 ExportTable_offset_pcc;
        (* clc cgp, ExportTable_offset_cgp(ct1) *)
        load_imm cgp ct1 ExportTable_offset_cgp;
        (* cgetbase s1, cra *)
        getb cs1 cra;
        (* csetaddr ra, ra, s1 *)
        seta cra cra cs1;
        (* cincoffset cra, cra, s0 *)
        lea cra cra cs0;
        #".Lhandle_error_test_stackful";
        (* beqz a0, .Lhandle_error_stack_setup *)
        jeqz (".Lhandle_error_stack_setup")%asm ca0
      ]
      ; [ #".Lhandle_error_stackless_setup";
        (* clw a0, TrustedStack_offset_mcause(csp) *)
        load_imm ca0 csp TrustedStack_offset_mcause;
        (* csrr a1, mtval *)
        csrr ca1 mtval;
        (* li a2, 0 *)
        mov ca2 0;
        (* cmove csp, ct0 *)
        mov csp ct0;
        (* j .Lhandle_error_handler_invoke *)
        jmp (".Lhandle_error_handler_invoke")%asm
      ]
      ; ([ #".Lhandle_error_stack_setup";
         (* clc cs1, TrustedStack_offset_mepcc(csp) *)
         load_imm cs1 csp TrustedStack_offset_mepcc;
         (* ccleartag cs1, cs1 *)
         cleartag cs1 cs1;
         (* csc cs1, TrustedStack_offset_mepcc(ct0) *)
         store_imm ct0 cs1 TrustedStack_offset_mepcc;
         (* cincoffset ca2, csp, TrustedStack_offset_cra *)
         lea ca2 csp TrustedStack_offset_cra;
         (* cincoffset ca3, ct0, TrustedStack_offset_cra *)
         lea ca3 ct0 TrustedStack_offset_cra
       ] ++
       (* copyContext ca3, ca2, cs1, a4 *)
       copy_context_asm ca3 ca2 cs1 ca4 ++
       [ (* cmove ca0, ct0 *)
         mov ca0 ct0;
         (* clw a1, TrustedStack_offset_mcause(csp) *)
         load_imm ca1 csp TrustedStack_offset_mcause;
         (* csrr a2, mtval *)
         csrr ca2 mtval;
         (* cmove csp, ca0 *)
         mov csp ca0
       ])
      ; (#".Lhandle_error_handler_invoke" ::
         (* csrsi mstatus, 0x8 *)
         csrsi mstatus (Z.shiftl 1 MIE_BIT) ::
         #".Lhandle_error_handler_invoke_irqs" ::
         (* zeroAllRegistersExcept ra, sp, gp, a0, a1, a2 *)
         rclear_asm registers_handler_invoke ++
         [ #".Lhandle_error_handler_cjalr";
           (* cjalr cra *)
           jalr cra cra ])
      ; [ #".Lhandle_error_handler_return";
        (* csrci mstatus, 0x8 *)
        csrci mstatus (Z.shiftl 1 MIE_BIT);
        #".Lhandle_error_handler_return_irqs";
        (* bnez a0, .Lcommon_force_unwind *)
        jnez (".Lcommon_force_unwind")%asm ca0
      ]
      ; ([ #".Lhandle_error_install_context";
         (* cspecialr ct1, mtdc *)
         readsr ct1 mtdc;
         (* csrr t0, CSR_MSHWM *)
         csrr ct0 mshwm;
         (* csw t0, TrustedStack_offset_mshwm(ct1) *)
         store_imm ct1 ct0 TrustedStack_offset_mshwm;
         (* clhu tp, TrustedStack_offset_frameoffset(ct1) *)
         load_imm ctp ct1 TrustedStack_offset_frameoffset;
         (* addi tp, tp, -TrustedStackFrame_size *)
         add ctp ctp (- TrustedStackFrame_size)%Z;
         (* cincoffset ctp, ct1, tp *)
         lea ctp ct1 ctp;
         (* clc ct0, TrustedStackFrame_offset_calleeExportTable(ctp) *)
         load_imm ct0 ctp TrustedStackFrame_offset_calleeExportTable;
         (* cgetbase s0, ct0 *)
         getb cs0 ct0;
         (* csetaddr ct0, ct0, s0 *)
         seta ct0 ct0 cs0;
         (* clc ct0, ExportTable_offset_pcc(ct0) *)
         load_imm ct0 ct0 ExportTable_offset_pcc;
         (* clc cra, TrustedStack_offset_mepcc(csp) *)
         load_imm cra csp TrustedStack_offset_mepcc;
         (* cgetaddr ra, cra *)
         geta cra cra;
         (* csetaddr ct2, ct0, ra *)
         seta ct2 ct0 cra;
         (* cincoffset ca2, csp, TrustedStack_offset_cra *)
         lea ca2 csp TrustedStack_offset_cra;
         (* cincoffset ca3, ct1, TrustedStack_offset_cra *)
         lea ca3 ct1 TrustedStack_offset_cra
       ] ++
       (* copyContext ca3, ca2, cs1, a4 *)
       copy_context_asm ca3 ca2 cs1 ca4 ++
       [ (* clh s1, TrustedStackFrame_offset_errorHandlerCount(ctp) *)
         load_imm cs1 ctp TrustedStackFrame_offset_errorHandlerCount;
         (* addi s1, s1, 1 *)
         add cs1 cs1 1;
         (* csh s1, TrustedStackFrame_offset_errorHandlerCount(ctp) *)
         store_imm ctp cs1 TrustedStackFrame_offset_errorHandlerCount;
         (* cmove csp, ct1 *)
         mov csp ct1;
         (* j .Lcommon_context_install *)
         jmp (".Lcommon_context_install")%asm
       ])
      ; [ #".Lcommon_defer_irqs_and_thread_exit";
        (* csrci mstatus, 0x8 *)
        csrci mstatus (Z.shiftl 1 MIE_BIT);
        #".Lcommon_deferred_irqs_and_thread_exit";
        #".Lcommon_thread_exit";
        (* [deviation] no scheduler: halt *)
        halt
      ]
      ; [ #".Lhandle_error_in_switcher";
        (* auipcc ctp, %cheriot_compartment_hi(.Lswitch_entry_first_spill); cincoffset *)
        auipcc ctp (".Lswitch_entry_first_spill")%asm;
        (* bne t1, tp, .Lcommon_force_unwind *)
        jne (".Lcommon_force_unwind")%asm ct1 ctp;
        (* li a0, -ENOTENOUGHSTACK *)
        mov ca0 ENOTENOUGHSTACK;
        (* li a1, 0 *)
        mov ca1 0;
        #".Lhandle_return_context_install";
        (* auipcc ct2, %cheriot_compartment_hi(.Lswitch_just_return); cincoffset *)
        auipcc ct2 (".Lswitch_just_return")%asm;
        (* csc ca0, TrustedStack_offset_ca0(csp) *)
        store_imm csp ca0 TrustedStack_offset_ca0;
        (* csc ca1, TrustedStack_offset_ca1(csp) *)
        store_imm csp ca1 TrustedStack_offset_ca1;
        (* j .Lcommon_context_install *)
        jmp (".Lcommon_context_install")%asm
      ]
      ; [ #".Lexception_reentered";
        (* [deviation] halt instead of the re-entry loop *)
        halt
      ]
    ].

  Definition switcher_asm : list (list asm_code) :=
    switcher_call_asm ++
    switcher_callback_asm ++
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


  (** The data words of the switcher, before its code: Griotte's key at
      [.unsealing_key_import_tables], zeroes elsewhere. *)
  Definition switcher_data_words (ot : OType) : list Word :=
    [WInt 0; SealRange (true, true) Global ot (ot ^+ 1) ot; WInt 0; WInt 0; WInt 0].

  (** The well-formedness of the layout of a user thread. *)
  Class threadLayoutWf {tlayout : threadLayout} : Type :=
    mkThreadLayoutWf {
        trusted_stack_disjoint_from_shadow :
        disjoint_from_shadow b_trusted_stack e_trusted_stack;
        (* The register save area of the trusted stack is not in the heap. *)
        trusted_stack_not_heap :
        not_heap_range b_trusted_stack (b_trusted_stack ^+ TSTACK_REGFRAME_SZ);
        (* The trusted stack holds its header, the entry frame and a whole
           number of frames. *)
        trusted_stack_frames_fit :
        ∃ n : nat,
          (b_trusted_stack + tstack_frame_offset (S n))%a = Some e_trusted_stack;
        (* The trusted stack is not at address 0: mtdc is never null. *)
        trusted_stack_base_nonzero : (b_trusted_stack : Z) ≠ 0;
        (* The two hazard slots of the thread, outside the shadow table and
           the heap. *)
        hazard_slots_size : (b_hazard_slots + 2)%a = Some e_hazard_slots;
        hazard_slots_disjoint_from_shadow :
        disjoint_from_shadow b_hazard_slots e_hazard_slots;
        hazard_slots_not_heap : not_heap_range b_hazard_slots e_hazard_slots
      }.

  Class switcherLayoutWf `{!switcherLayout} : Type :=
    mkSwitcherLayoutWf {
        switcher_size :
        (a_switcher_call + length switcher_instrs)%a = Some e_switcher ;

        switcher_call_entry_point :
        (b_switcher + 5)%a = Some a_switcher_call ;

        switcher_return_entry_point :
        (b_switcher + (5 + length switcher_call_instrs) )%a = Some a_switcher_return ;

        ot_switcher_size :
        (ot_switcher < ot_switcher ^+ 1)%ot;

        switcher_key_not_shadow : is_shadow_address (b_switcher ^+ 1) = false;
        switcher_not_heap_range : not_heap_range b_switcher e_switcher;
        (* The layout of every user thread is well formed. *)
        swl_thread_wf : ∀ i, threadLayoutWf (tlayout := swl_thread i)
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
    is_heap_cap switcher_entry_call = false.
  Proof.
    rewrite /switcher_entry_call /is_heap_cap /heap_cap_base /memory_cap_base /= switcher_base_not_heap /=.
    reflexivity.
  Qed.

End Switcher.
#[export] Hint Mode threadLayoutWf - ! : typeclass_instances.
#[export] Hint Mode switcherLayoutWf - ! : typeclass_instances.

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

(** [t] mentions the layout or the code of the switcher. *)
Ltac switcher_layout_term t :=
  match t with
  | context [a_switcher_call] => idtac
  | context [b_switcher] => idtac
  | context [e_switcher] => idtac
  | context [switcher_instrs] => idtac
  | context [assembled_switcher] => idtac
  | context [switcher_asm] => idtac
  end.

(** When the goal does not mention the layout or the code of the switcher,
    clear the hypotheses that do: they only slow down [solve_finz]. Fails
    when the goal mentions them. *)
Ltac clear_switcher_layout :=
  match goal with |- ?g => tryif switcher_layout_term g then fail else idtac end;
  repeat (match goal with H : ?T |- _ => switcher_layout_term T; clear H end).

(** [solve_addr] sees through the layout of export tables. It first tries
    without the facts about the switcher's layout, which are irrelevant to
    most goals, then with the full context. The hook has a single
    definition: any later redefinition of [solve_addr_prepare] (for
    instance in [kvs.v]) must also call [exptbl_unfold]. *)
#[global] Ltac solve_addr.solve_addr_prepare ::=
  try exptbl_unfold;
  try solve [clear_switcher_layout; solve_finz].
