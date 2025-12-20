From cap_machine Require Import machine_parameters assembler.
From cap_machine Require Export clear_stack clear_registers.

Section Switcher.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  Definition Lswitch_csp_check_perm_asm : list asm_code :=
    (* Check permissions of the stack *)
    [ #".Lswitcher_csp_check_perm";
        getp ct2 csp;
        mov ctp (encodePerm RWL);
        sub ct2 ct2 ctp;
        jnz (".Lcommon_force_unwind")%asm ct2
      ].

  Definition Lswitch_csp_check_loc_asm : list asm_code :=
    (* Check permissions of the stack *)
    [ #".Lswitcher_csp_check_loc";
        getl ct2 csp;
        mov ctp (encodeLoc Local);
        sub ct2 ct2 ctp;
        jnz (".Lcommon_force_unwind")%asm ct2
      ].

  Definition Lswitch_entry_first_spill_asm : list asm_code :=
    (* Save the callee registers *)
    [ #".Lswitcher_entry_first_spill";
        store csp cs0;
        lea csp 1;
        store csp cs1;
        lea csp 1;
        store csp cra;
        lea csp 1;
        store csp cgp;
        lea csp 1
      ].

  Definition Lswitch_trusted_stack_push_asm  : list asm_code :=
     [
       (* Check that the trusted stack has enough space *)
        readsr ct2 mtdc;
        geta cs0 ct2;
        add cs0 cs0 1;
        gete ctp ct2;
        lt ctp cs0 ctp; (* if (atstk+1 < etstk) then (ctp := 1) else (ctp := 0)*)
        jnz 2 ctp;
        jmp (".Lswitch_trusted_stack_exhausted")%asm;
        (* Save the caller's stack pointer in the trusted stack *)
        lea ct2 1;
        store ct2 csp;
        writesr mtdc ct2
      ].


  Definition Lswitch_stack_chop_asm : list asm_code :=
    (* Chop off the stack *)
    [
        gete cs0 csp;
        geta cs1 csp;
        subseg csp cs1 cs0
      ].

  Definition LoadCapPCC_asm : list asm_code :=
    (* Fetch (unsealing capability and unseal entry point *)
    [
        getb cs1 PC;
        geta cs0 PC;
        sub cs1 cs1 cs0;
        mov cs0 PC;
        lea cs0 cs1;
        lea cs0 (-2)%Z;
        load cs0 cs0
      ].

  Definition Lswitch_unseal_entry_asm : list asm_code :=
    (* Load and decode entry point nargs and offset *)
    [
        unseal ct1 cs0 ct1;
        load cs0 ct1;
        land ct2 cs0 7;
        lshiftr cs0 cs0 3
      ].

  Definition Lswitch_callee_load_asm : list asm_code :=
    (* Prepare callee's PCC in cra, and callee's CGP in cgp *)
     [
        getb cgp ct1;
        geta cs1 ct1;
        sub cs1 cgp cs1;
        lea ct1 cs1;
        load cra ct1;
        lea ct1 1;
        load cgp ct1;
        lea cra cs0;
        add ct2 ct2 1
      ].

  Definition Lswitch_callee_call_asm : list asm_code :=
    (* Jump to callee *)
    [ jalr cra cra ].

  Definition Lswitcher_after_compartment_call_asm : list asm_code :=
    [
      #".Lswitcher_after_compartment_call";
        (* Restores caller's stack frame *)
        readsr ctp mtdc;
        load csp ctp;
        lea ctp (-1)%Z;
        writesr mtdc ctp;

        (* Restores the caller's saved registers *)
        lea csp (-1)%Z;
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
      ].



    (* --- Callback --- *)

  Definition ECOMPARTMENTFAIL : Z := -1.
  Definition ENOTENOUGHTRUSTEDSTACK : Z := -141.

  Definition Lswitch_trusted_stack_exhausted_asm : list asm_code :=
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
        jmp (".Lswitch_callee_dead_zeros")%asm
    ].

  Definition Lcommon_force_unwind_asm : list asm_code :=
    [ #".Lcommon_force_unwind";
        mov ca0 ECOMPARTMENTFAIL;
        mov ca1 0;
        jmp (".Lswitcher_after_compartment_call")%asm
      ].

  Definition Lswitch_just_return_asm : list asm_code :=
   [jmpcap cra].

  Definition switcher_asm : (list (list asm_code)) :=
    [
      (* Call *)
      Lswitch_csp_check_perm_asm
      ; Lswitch_csp_check_loc_asm
      ; Lswitch_entry_first_spill_asm
      ; Lswitch_trusted_stack_push_asm
      ; Lswitch_stack_chop_asm
      (* Zero out the callee's stack frame *)
      ; clear_stack_asm cs0 cs1
      ; LoadCapPCC_asm
      ; Lswitch_unseal_entry_asm
      ; Lswitch_callee_load_asm
      ; clear_registers_pre_call_skip_asm (* Lswitch_zero_arguments_start *)
      ; clear_registers_pre_call_asm (* Lswitch_caller_dead_zeros *)
      ; Lswitch_callee_call_asm
      (* Callback *)
      ; Lswitcher_after_compartment_call_asm
      ; clear_stack_asm ct0 ct1
      (* Lswitch_callee_dead_zeros *)
      ; (#".Lswitch_callee_dead_zeros"::clear_registers_post_call_asm)
      ; Lswitch_just_return_asm
      (* Failure *)
      ; Lswitch_trusted_stack_exhausted_asm
      ; Lcommon_force_unwind_asm
    ]
  .

  Definition assembled_switcher' :=
    Eval vm_compute in assemble_block switcher_asm.
  Definition assembled_switcher :=
    Eval cbv in (revert_regs_code_block assembled_switcher').
  Definition switcher_instrs : list Word :=
   concat (encodeInstrsW <$> assembled_switcher).

  Definition switcher_labels :=
    Eval cbn in (compute_asm_code_env (concat switcher_asm)).2.

  Definition switcher_call_asm :=
   [(* Call *)
          Lswitch_csp_check_perm_asm
          ; Lswitch_csp_check_loc_asm
          ; Lswitch_entry_first_spill_asm
          ; Lswitch_trusted_stack_push_asm
          ; Lswitch_stack_chop_asm
          (* Zero out the callee's stack frame *)
          ; clear_stack_asm cs0 cs1
          ; LoadCapPCC_asm
          ; Lswitch_unseal_entry_asm
          ; Lswitch_callee_load_asm
          ; clear_registers_pre_call_skip_asm (* Lswitch_zero_arguments_start *)
          ; clear_registers_pre_call_asm (* Lswitch_caller_dead_zeros *)
          ; Lswitch_callee_call_asm
   ].
  Definition switcher_call_instrs :=
    Eval compute in concat (firstn 12 (encodeInstrsW <$> assembled_switcher)).

  Class switcherLayout : Type :=
    mkCmptSwitcher {
        b_switcher : Addr ;
        e_switcher : Addr ;
        a_switcher_call : Addr ;
        a_switcher_return : Addr ;

        ot_switcher : OType ;

        b_trusted_stack : Addr;
        e_trusted_stack : Addr;

        switcher_size :
        (a_switcher_call + length switcher_instrs)%a = Some e_switcher ;

        switcher_call_entry_point :
        (b_switcher + 1)%a = Some a_switcher_call ;

        switcher_return_entry_point :
        (b_switcher + (1 + length switcher_call_instrs) )%a = Some a_switcher_return ;

      }.

  Definition is_switcher_entry_point `{switcherLayout} (w : Word) :=
    bool_decide
      (w = (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call)
           ∨
      (w = (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return)
      ))
  .

  Definition encode_entry_point (nargs entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 3 in
    (Z.lor off args).

  Definition decode_entry_point (entry_point : Z) : (Z * Z) :=
    ( Z.land entry_point 7, Z.shiftr entry_point 3).

End Switcher.
