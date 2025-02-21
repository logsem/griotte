From cap_machine Require Import machine_parameters asm_cerise.

Section Switcher.
  Import Asm_Cerise.
  Context `{MP: MachineParameters}.

  Definition switcher : list asm_code :=
    [
      #"switcher";
      (* #[SU, Global, 9, 10, 9] *)
      #"switcher_cc";
      (* Save the callee registers *)
      store csp cs0;
      lea csp 1%Z;
      store csp cs1;
      lea csp 1%Z;
      store csp cra;
      lea csp 1%Z;
      store csp cgp;
      (* Check permissions of the stack *)
      getp ct2 csp;
      mov ctp (encodePerm RWL);
      sub ct2 ct2 ctp;
      jnz 2%Z ct2;
      jmp 2%Z;
      fail;
      (* Save the caller's stack pointer in the trusted stack *)
      readsr ct2 mtdc;
      lea ct2 1%Z;
      store ct2 csp;
      writesr mtdc ct2;
      (* Zero out the callee's stack frame *)
      geta cs0 csp;
      getb cs1 csp;
      subseg csp cs1 cs0;
      #"switcher_zero_stk_init_pre";
      sub cs0 cs1 cs0;
      mov cs1 csp;
      lea cs1 cs0;
      #"switcher_zero_stk_loop_pre";
      jnz 2%Z cs0 ;
      jmp ("switcher_zero_stk_end_pre" - "switcher_zero_stk_loop_pre" - 1%Z)%asm;
      store cs1 0%Z;
      lea cs1 1%Z;
      add cs0 cs0 1%Z;
      #"switcher_zero_stk_loop_end_pre";
      jmp ("switcher_zero_stk_loop_pre" - "switcher_zero_stk_loop_end_pre")%asm;
      #"switcher_zero_stk_end_pre";
      lea csp (-1)%Z;
      (* Fetch (un)sealing capability and unseal entry point *)
      getb cs1 PC;
      geta cs0 PC;
      sub cs1 cs1 cs0;
      mov cs0 PC;
      lea cs0 cs1;
      lea cs0 (-2)%Z;
      load cs0 cs0;
      unseal ct1 cs0 ct1;
      (* Load and decode entry point nargs and offset *)
      load cs0 ct1;
      land ct2 cs0 7%Z;
      lshiftr cs0 cs0 3%Z;
      (* Prepare callee's PCC in cra, and callee's CGP in cgp *)
      getb cgp ct1;
      geta cs1 ct1;
      sub cs1 cgp cs1;
      lea ct1 cs1;
      load cra ct1;
      lea ct1 1%Z;
      load cgp ct1;
      lea cra cs0;
      add ct2 ct2 1%Z;
      (* clear registers, skipping arguments *)
      jmp ct2;
      mov ca0 0%Z;
      mov ca1 0%Z;
      mov ca2 0%Z;
      mov ca3 0%Z;
      mov ca4 0%Z;
      mov ca5 0%Z;
      mov ct0 0%Z;
      mov cnull 0%Z;
      mov ctp 0%Z;
      mov ct1 0%Z;
      mov ct2 0%Z;
      mov cs0 0%Z;
      mov cs1 0%Z;
      mov ca6 0%Z;
      mov ca7 0%Z;
      mov cs2 0%Z;
      mov cs3 0%Z;
      mov cs4 0%Z;
      mov cs5 0%Z;
      mov cs6 0%Z;
      mov cs7 0%Z;
      mov cs8 0%Z;
      mov cs9 0%Z;
      mov cs10 0%Z;
      mov cs11 0%Z;
      mov ct3 0%Z;
      mov ct4 0%Z;
      mov ct5 0%Z;
      mov ct6 0%Z;
      (* Jump to callee *)
      jalr cra cra;
      (* --- Callback --- *)
      (* Restores caller's stack frame *)
      readsr ctp mtdc;
      load csp ctp;
      lea ctp (-1)%Z;
      writesr mtdc ctp;
      (* Restores the caller's saved registers *)
      load cgp csp;
      lea csp (-1)%Z;
      load ca2 csp;
      lea csp (-1)%Z;
      load cs1 csp;
      lea csp (-1)%Z;
      load cs0 csp;
      (* Zero out the callee stack frame *)
      #"switcher_zero_stk_init_post";
      geta ct0 csp;
      getb ct1 csp;
      sub ct0 ct1 ct0;
      mov ct1 csp;
      lea ct1 ct0;
      #"switcher_zero_stk_loop_post";
      jnz 2%Z ct0;
      jmp ("switcher_zero_stk_end_post" - "switcher_zero_stk_loop_post" - 1%Z)%asm;
      store ct1 0%Z;
      lea ct1 1%Z;
      add ct0 ct0 1%Z;
      #"switcher_zero_stk_loop_end_post";
      jmp ("switcher_zero_stk_loop_post" - "switcher_zero_stk_loop_end_post")%asm;
      #"switcher_zero_stk_end_post";
      (* Restores the return pointer to caller  *)
      mov cra ca2;
      (* Clear registers *)
      mov ct0 0%Z;
      mov cnull 0%Z;
      mov ctp 0%Z;
      mov ct1 0%Z;
      mov ct2 0%Z;
      mov ct3 0%Z;
      mov ct4 0%Z;
      mov ct5 0%Z;
      mov ct6 0%Z;
      mov ca2 0%Z;
      mov ca3 0%Z;
      mov ca4 0%Z;
      mov ca5 0%Z;
      mov ca6 0%Z;
      mov ca7 0%Z;
      mov cs0 0%Z;
      mov cs1 0%Z;
      mov cs2 0%Z;
      mov cs3 0%Z;
      mov cs4 0%Z;
      mov cs5 0%Z;
      mov cs6 0%Z;
      mov cs7 0%Z;
      mov cs8 0%Z;
      mov cs9 0%Z;
      mov cs10 0%Z;
      mov cs11 0%Z;
      (* Jump back to caller *)
      jalr cra cra;
      #"switcher_end:"
    ].

  Definition assembled_switcher' :=
    Eval vm_compute in assemble switcher.

  Definition assembled_switcher :=
    Eval cbv in (fmap revert_regs_instr assembled_switcher').

  Definition switcher_instrs := encodeInstrsW assembled_switcher.

  Definition encode_entry_point (nargs entry_point_offset : Z) : Z :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 3 in
    (Z.lor off args).

  Definition decode_entry_point (entry_point : Z) : (Z * Z) :=
    ( Z.land entry_point 7, Z.shiftr entry_point 3).

End Switcher.
