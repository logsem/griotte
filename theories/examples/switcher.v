From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_frozen region_invariants_allocation.

Section Switcher.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .


  Definition switcher_cross_compartment_call_code
    (switcher_zero_stk_end_pre
       switcher_zero_stk_loop_pre
       switcher_zero_stk_loop_end_pre
      : Z) : list Word
    :=
  encodeInstrsW [
      (* SealRange[SU, Global, switcher_otype, switcher_otype+1,switcher_otype] *)
      Store csp cs0;
      Lea csp (-1)%Z;
      Store csp cs1;
      Lea csp (-1)%Z;
      Store csp cgp;
      GetP ct2 csp;
      Mov ctp (encodePerm (BPerm R WL LG LM));
      Sub ct2 ct2 ctp;
      (* Jnz ct2 2; (* TODO Jnz only for relative jump? *) *)
      (* Jmp 2; (* TODO Jmp only for relative jump? *) *)
      Fail;
      ReadSR ct2 mtdc;
      Lea ct2 (-1)%Z;
      Store ct2 csp;
      WriteSR mtdc ct2;
      GetA cs0 csp;
      GetB cs1 csp;
      Subseg csp cs1 cs0;
      (* switcher_zero_stk_init_pre: *)
      Sub cs0 cs1 cs0;
      Mov cs1 csp;
      Lea cs1 cs0;
      (* switcher_zero_stk_loop_pre: *)
      (* Jnz cs0 2; *)
      (* Jmp (switcher_zero_stk_end_pre - switcher_zero_stk_loop_pre - 1); *)
      Store cs1 0;
      Lea cs1 1;
      machine_base.Add cs0 cs0 1;
      (* switcher_zero_stk_loop_end_pre: *)
      (* Jmp (switcher_zero_stk_loop_pre - switcher_zero_stk_loop_end_pre)%Z; *)
      (* switcher_zero_stk_end_pre: *)
      Lea csp (-1)%Z;
      GetB cs1 PC;
      GetA cs0 PC;
      Sub cs1 cs1 cs0;
      Mov cs0 PC;
      Lea cs0 cs1;
      Lea cs0 (-2)%Z;
      Load cs0 cs0;
      UnSeal ct1 cs0 ct1;
      Load cs0 ct1;
      (* Rem ct2 cs0 10; *)
      Sub cs0 cs0 ct2;
      (* Div cs0 cs0 10; *)
      GetB cgp ct1;
      GetA cs1 ct1;
      Sub cs1 cgp cs1;
      Lea ct1 cs1;
      Load cra ct1;
      Lea ct1 1;
      Load cgp ct1;
      Lea cra cs0;
      machine_base.Add ct2 ct2 1;
      Jmp ct2;
      Mov r_t10 0;
      Mov r_t11 0;
      Mov r_t12 0;
      Mov r_t13 0;
      Mov r_t14 0;
      Mov r_t15 0;
      Mov r_t5 0;
      Mov r_t0 0;
      Mov r_t4 0;
      Mov r_t6 0;
      Mov r_t7 0;
      Mov r_t8 0;
      Mov r_t9 0;
      Mov r_t16 0;
      Mov r_t17 0;
      Mov r_t18 0;
      Mov r_t19 0;
      Mov r_t20 0;
      Mov r_t21 0;
      Mov r_t22 0;
      Mov r_t23 0;
      Mov r_t24 0;
      Mov r_t25 0;
      Mov r_t26 0;
      Mov r_t27 0;
      Mov r_t28 0;
      Mov r_t29 0;
      Mov r_t30 0
      (* ; *)
      (* Jalr cra cra *)
    ].

  Definition switcher_cross_compartment_return_code
    (switcher_zero_stk_end_post
       switcher_zero_stk_loop_post
      switcher_zero_stk_loop_end_post
      : Z) : list Word
    :=
    encodeInstrsW [
        ReadSR ctp mtdc;
        Load csp ctp;
        Lea ctp 1%Z;
        WriteSR mtdc ctp;
        Load cgp csp;
        Lea csp 1%Z;
        Load ca2 csp;
        Lea csp 1;
        Load cs1 csp;
        Lea csp 1%Z;
        Load cs0 csp;
    (* switcher_zero_stk_init_post: *)
    GetA ct0 csp;
      GetB ct1 csp;
      Sub ct0 ct1 ct0;
      Mov ct1 csp;
      Lea ct1 ct0;
      (* switcher_zero_stk_loop_post: *)
      (* Jnz ct0 2; *)
      (* Jmp (switcher_zero_stk_end_post - switcher_zero_stk_loop_post - 1)%Z ; *)
      Store ct1 0%Z;
      Lea ct1 1%Z;
      machine_base.Add ct0 ct0 1%Z;
      (* switcher_zero_stk_loop_end_post: *)
      (* Jmp (switcher_zero_stk_loop_post - switcher_zero_stk_loop_end_post)%Z; *)
      (* switcher_zero_stk_end_post: *)
      Mov cra ca2;
      Mov r_t0 0;
      Mov r_t4 0;
      Mov r_t5 0;
      Mov r_t6 0;
      Mov r_t7 0;
      Mov r_t12 0;
      Mov r_t13 0;
      Mov r_t14 0;
      Mov r_t15 0;
      Mov r_t16 0;
      Mov r_t17 0;
      Mov r_t18 0;
      Mov r_t19 0;
      Mov r_t20 0;
      Mov r_t21 0;
      Mov r_t22 0;
      Mov r_t23 0;
      Mov r_t24 0;
      Mov r_t25 0;
      Mov r_t26 0;
      Mov r_t27 0;
      Mov r_t28 0;
      Mov r_t29 0;
      Mov r_t30 0
      (* ; *)
      (* Jalr cra cra *)
      (* switcher_end: *)
    ].


End Switcher.
