From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert.

Section CMDC_Main.
  Context `{MP: MachineParameters}.

  (* Expect:
     pc := (RX, Global, b_main, e_main, b_main_code )

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f
     b_main + 3 : WSealed ot_switcher C.g

   *)
  Definition cmdc_main_code : list Word :=
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* set b <- 0 *)
      Store cgp 0%Z;
      Mov ca0 cgp;

      (* set c <- 0 *)
      Lea cgp 1%Z;
      Store cgp 0%Z;

      (* call B.f b *)
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> b *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 2 cs0 ct0 ct1 (* cs0 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp;
      (* assert c == 0 *)
      Load ct0 cgp; (* ct0 -> c *)
      Mov ct1 0%Z
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    ++
    encodeInstrsW [
      (* prepare for later *)
      Mov ca0 cgp;
      Mov ca1 0%Z; (* erase returned values from the call *)

      (* set b <- 42 *)
      Lea cgp (-1)%Z;
      Store cgp 42%Z;

      (* call C.g c *)
      GetA ct0 ca0;
      Add ct1 ct0 1%Z;
      Subseg ca0 ct0 ct1 (* ca0 -> c *)
    ]
    ++ fetch_instrs 0 ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs 3 cs0 ct0 ct1 (* cs0 -> {C.g}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Jalr cra ctp;
      (* assert b == 42 *)
      Load ct0 cgp; (* ct0 -> c *)
      Mov ct1 42%Z
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    ++ encodeInstrsW [
      Halt
      (* #"main_e" *)
    ].

  Definition cmdc_main_data : list Word := [WInt 0; WInt 0].

  Definition cmdc_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f C_g : Sealable) : list Word :=
    [
      WSentry XSRW_ Global b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher C_g
    ].

End CMDC_Main.
