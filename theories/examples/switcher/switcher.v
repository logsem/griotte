From cap_machine Require Import machine_parameters asm_cerise.

Section Switcher.
  Import Asm_Cerise.
  Context `{MP: MachineParameters}.

  Definition switcher : list asm_code :=
    [
      #"switcher";
      (* #[SU, Global, 9, 10, 9] *)
      #"switcher_cc";
      store csp cs0;
      lea csp (-1)%Z;
      store csp cs1;
      lea csp (-1)%Z;
      store csp cra;
      lea csp (-1)%Z;
      store csp cgp;
      getp ct2 csp;
      mov ctp (encodePerm (BPerm R WL LG LM));
      sub ct2 ct2 ctp;
      jnz 2%Z ct2;
      jmp 2%Z;
      fail;
      readsr ct2 mtdc;
      lea ct2 (-1)%Z;
      store ct2 csp;
      writesr mtdc ct2;
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
      getb cs1 PC;
      geta cs0 PC;
      sub cs1 cs1 cs0;
      mov cs0 PC;
      lea cs0 cs1;
      lea cs0 (-2)%Z;
      load cs0 cs0;
      unseal ct1 cs0 ct1;
      load cs0 ct1;
      land ct2 cs0 7%Z;
      lshiftr cs0 cs0 3%Z;
      getb cgp ct1;
      geta cs1 ct1;
      sub cs1 cgp cs1;
      lea ct1 cs1;
      load cra ct1;
      lea ct1 1%Z;
      load cgp ct1;
      lea cra cs0;
      add ct2 ct2 1%Z;
      jmp ct2;
      mov r_t10 0%Z;
      mov r_t11 0%Z;
      mov r_t12 0%Z;
      mov r_t13 0%Z;
      mov r_t14 0%Z;
      mov r_t15 0%Z;
      mov r_t5 0%Z;
      mov r_t0 0%Z;
      mov r_t4 0%Z;
      mov r_t6 0%Z;
      mov r_t7 0%Z;
      mov r_t8 0%Z;
      mov r_t9 0%Z;
      mov r_t16 0%Z;
      mov r_t17 0%Z;
      mov r_t18 0%Z;
      mov r_t19 0%Z;
      mov r_t20 0%Z;
      mov r_t21 0%Z;
      mov r_t22 0%Z;
      mov r_t23 0%Z;
      mov r_t24 0%Z;
      mov r_t25 0%Z;
      mov r_t26 0%Z;
      mov r_t27 0%Z;
      mov r_t28 0%Z;
      mov r_t29 0%Z;
      mov r_t30 0%Z;
      jalr cra cra;
      readsr ctp mtdc;
      load csp ctp;
      lea ctp 1%Z;
      writesr mtdc ctp;
      load cgp csp;
      lea csp 1%Z;
      load ca2 csp;
      lea csp 1%Z;
      load cs1 csp;
      lea csp 1%Z;
      load cs0 csp;
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
      mov cra ca2;
      mov r_t0 0%Z;
      mov r_t4 0%Z;
      mov r_t5 0%Z;
      mov r_t6 0%Z;
      mov r_t7 0%Z;
      mov r_t12 0%Z;
      mov r_t13 0%Z;
      mov r_t14 0%Z;
      mov r_t15 0%Z;
      mov r_t16 0%Z;
      mov r_t17 0%Z;
      mov r_t18 0%Z;
      mov r_t19 0%Z;
      mov r_t20 0%Z;
      mov r_t21 0%Z;
      mov r_t22 0%Z;
      mov r_t23 0%Z;
      mov r_t24 0%Z;
      mov r_t25 0%Z;
      mov r_t26 0%Z;
      mov r_t27 0%Z;
      mov r_t28 0%Z;
      mov r_t29 0%Z;
      mov r_t30 0%Z;
      jalr cra cra;
      #"switcher_end:"
    ].

  Definition assembled_switcher' :=
    Eval vm_compute in assemble switcher.

  Definition assembled_switcher :=
    Eval cbv in (fmap revert_regs_instr assembled_switcher').

  Definition switcher_code := encodeInstrsW assembled_switcher.

  Definition encode_entry_point (nargs : nat) (entry_point_offset : Z) :=
    let args := Z.land nargs 7 in
    let off := Z.shiftl entry_point_offset 3 in
    WInt (Z.lor off args).

End Switcher.
