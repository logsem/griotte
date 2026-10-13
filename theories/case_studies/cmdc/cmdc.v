From griotte Require Import machine_parameters assembler fetch assert switcher.

Section CMDC_Main.
  Import Asm_Griotte.
  Local Open Scope Z_scope.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )

     b_main + 0 : WSentry true XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry true RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f
     b_main + 3 : WSealed ot_switcher C.g

   *)
  Definition cmdc_main_asm : list (list asm_code) :=
    [ [ (* the imports *)
        #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_B_f";
        #@".Limport_C_g";

        (* set b <- 0 *)
        store cgp 0;
        mov ca0 cgp;

        (* set c <- 0 *)
        lea cgp 1;
        store cgp 0;

        (* call B.f b *)
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ct0 ct1 (* ca0 -> b *)
      ];
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      fetch_asm ".Limport_B_f" ct1; (* ct1 -> {B.f}_(ot_switcher)  *)
      [ jalr cra ctp;
        (* assert c == 0 *)
        load ct0 cgp; (* ct0 -> c *)
        mov ct1 0
      ];
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ (* prepare for later *)
        mov ca0 cgp;
        mov ca1 0; (* erase returned values from the call *)

        (* set b <- 42 *)
        lea cgp (-1);
        store cgp 42;

        (* call C.g c *)
        geta ct0 ca0;
        add ct1 ct0 1;
        subseg ca0 ct0 ct1 (* ca0 -> c *)
      ];
      fetch_asm ".Limport_switcher" ctp; (* ctp -> switcher entry point *)
      fetch_asm ".Limport_C_g" ct1; (* ct1 -> {C.g}_(ot_switcher)  *)
      [ jalr cra ctp;
        (* assert b == 42 *)
        load ct0 cgp; (* ct0 -> c *)
        mov ct1 42
      ];
      assert_asm ".Limport_assert" ct2 ca2; (* asserts that ( *ct0 = *ct1 ) *)
      [ halt ]
    ].

  Definition cmdc_main_assembled' :=
    Eval vm_compute in assemble_block cmdc_main_asm.
  Definition cmdc_main_assembled :=
    Eval cbv in revert_regs_code_block cmdc_main_assembled'.
  Definition cmdc_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (cmdc_main_assembled !! n)).

  Definition cmdc_main_code : list Word :=
    cmdc_main_instrs_n 0 ++
    cmdc_main_instrs_n 1 ++
    cmdc_main_instrs_n 2 ++
    cmdc_main_instrs_n 3 ++
    cmdc_main_instrs_n 4 ++
    cmdc_main_instrs_n 5 ++
    cmdc_main_instrs_n 6 ++
    cmdc_main_instrs_n 7 ++
    cmdc_main_instrs_n 8 ++
    cmdc_main_instrs_n 9 ++
    cmdc_main_instrs_n 10.

  Definition cmdc_main_data : list Word := [WInt 0; WInt 0].

  Definition cmdc_main_imports `{!switcherLayout} `{!assertLayout}
    (B_f C_g : Sealable) : list Word :=
    [
      WSentry true XSRW_ Local b_switcher e_switcher a_switcher_call;
      WSentry true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g
    ].

  Definition cmdc_B_f_args : nat := 1.
  Definition cmdc_C_g_args : nat := 1.

End CMDC_Main.
