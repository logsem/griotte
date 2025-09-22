From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch.

Section Counter_Main.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

      get a
      set a := a + 1
      return a

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSealed ot_switcher C.f

      data:
      +----------------+ a
      |      v >= 0    |
      +----------------+
      |       ...      |


   *)
  Definition counter_main_code : list Word :=
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* get a *)
      Load cs0 cgp;
      (* set a := a + 1 *)
      Add cs0 cs0 1%Z;
      Store cgp cs0
      (* call C_f*)
    ]
    ++ fetch_instrs 0 ct0 cs0 cs1 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 1 ct1 cs0 cs1 (* ct1 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Mov cs0 cra; (* stores the return-to-switcher *)
      Jalr cra ct0 (* jmp to entry point *)
    ]
    ++
    encodeInstrsW [
      Mov cra cs0; (* restores the return-to-switcher *)

      (* return a *)
      Mov ca0 0%Z;
      Mov ca1 0%Z;
      Mov cs0 0%Z;
      Mov cs1 0%Z;
      JmpCap cra

      (* #"main_e" *)
    ].

  Definition counter_main_data : list Word := [WInt 0].

  Definition counter_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (C_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSealed ot_switcher C_f
    ].

End Counter_Main.
