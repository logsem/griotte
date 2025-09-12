From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert.

Section DROE_Main.
  Context `{MP: MachineParameters}.


  (*
    PSEUDO-CODE:

      set b := 42
      set a := (RW, Global, b, b+1, b)
      call B.adv (RO_DRO, Global, a, a+1, a)
      assert (b == 42)
      return 0

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)
     cra := (E-XSRW, Local, b_switcher, e_switcher, a_switcher_return)

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f


      data after initial setup:
      +----------------+ b
      |        42      |
      +----------------+ a
      | (RW,G,b,b+1,b) |
      +----------------+
      |       ...      |


   *)
  Definition droe_main_code : list Word :=
    let ro_dro := (encodePermPair (RO_DRO, Global)) in
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* set b <- 42 *)
      Store cgp 42%Z;     (* b <- 42 *)
      Mov ct0 cgp;        (* ct0 := (RW, Global, b, e, b) *)

      (* set a <- (RW, Global, b, b+1, b) *)
      GetB ct1 cgp;       (* ct1 := b *)
      Add ct2 ct1 1%Z;    (* ct2 := b+1 = a *)
      Subseg ct0 ct1 ct2; (* ct0 := (RW, Global, b, b+1, b) *)

      Lea cgp 1%Z;        (* cgp := (RW, Global, b, e, b+1) *)
      Store cgp ct0;      (* a <- (RW, Global, b, b+1, b) *)

      (* call B.f (RO_DRO, Global, a, a+1,a) *)
      Mov ca0 cgp;         (* ca0 := (RW, Global, b, e, b+1) = (RW, Global, b, e, a) *)
      Lea cgp (-1)%Z;       (* cgp := (RW, Global, b, e, b) *)
      Add ct1 ct2 1%Z;     (* ct1 := a+1 *)
      Subseg ca0 ct2 ct1;  (* ca0 := (RW, Global, a, a+1, a) *)
      Restrict ca0 ro_dro  (* ca0 := (RO_DRO, Global, a, a+1, a) *)
    ]
    ++ fetch_instrs 0 ct0 ct1 ct2 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 2 ct1 ct2 ct3 (* ct1 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      Mov cs0 cra; (* stores the return-to-switcher *)
      (* clear the arguments *)
      Jalr cra ct0;
      Mov cra cs0; (* restores the return-to-switcher *)
      (* -- return from the call -- *)
      (* assert b == 42 *)
      Load ct0 cgp; (* ct0 -> c *)
      Mov ct1 42%Z
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    ++
    encodeInstrsW [
      (* erase returned values from the call *)
      Mov ca0 0;
      Mov ca1 0;
      (* return to caller *)
      JmpCap cra
      (* #"main_e" *)
    ].

  Definition droe_main_data : list Word := [WInt 0; WInt 0].

  Definition droe_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f
    ].

End DROE_Main.
