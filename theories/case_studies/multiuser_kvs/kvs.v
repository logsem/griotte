From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import fetch assert.


Section KVS_Service.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  (*
    ca0 : sealedUserKey
    ca1 : key
    ca2 : val

    cgp0  : [U, Global, OUserKey, OUserKey + 1, OUserKey]
    cgp1  : key0
    cgp2  : val0
    ...   : ...
    cgp31 : key15
    cgp32 : val15
*)
  Definition SIZE_MAP := 16:
  Definition addOrUpdate_asm : list (list asm_code) :=
    [
      (* get full key *)
      [
        load ct1 cgp;
        unseal ca0 ca0 ct1;
        geta ca0 ca0;
        lshiftl ca0 ca0 16;
        lor ca0 ca0 ca1;
        (* ca0 contains the full key *)
      ];
      [
        lea cgp 1;
        mov ct0 0; (* 0 mean false *)
        mov ct1 0; (* ct1 contains the index of loop *)
        (* go through all entries of the map *)
        #".loop_start";
        sub ct2 SIZE_MAP ct1;
        jnz ct2 (".loop_body")%asm
        jmp (".loop_end")%asm
        #".loop_body";

        load ct2 cgp;
        (* we need to check that not 0 *)
        jnz ct2 (".not_empty_slot")
        (* slot is empty, we exit the loop *)
        #".empty_slot";
        jmp (".loop_end");

        (* slot is not empty, we now need to compare ct2 with the full key *)
        #".not_empty_slot";
        sub ct2 ca0 ct2;
        jnz ct2 (".not_same_key");
        #".same_key";
        (* update the value *)
        lea cgp 1;
        store cgp ca2;
        #".not_same_key";
        (* skip, we then finish the body of the loop *)
        lea cgp 2;
        add ct1 ct1 1;
        jmp (".loop_start");
        #".loop_end";
      ];
      [
        (* if ct0 still contains 0, then we did not find an existing key, and we need to add *)
        jnz ct0 (".key_found")%asm;
      ];
      [
        #".key_not_found";
        (* cgp already points to the first empty slot in the map *)
        store cgp ca0;
        lea cgp 1;
        store cgp ca2;
        mov ca0 0;
        jmp (".return")%asm;
      ];
      [
        #".key_found";
        (* return true *)
        mov ca0 1
      ];
      [
        #".return";
        (* return *)
        mov ca1 0
        jmp cra
      ]
    ].

Section KVS_Main.
  Context `{MP: MachineParameters}.

  (* KVS compartment *)
  Definition addOrUpdate : list Word :=



  (*
    PSEUDO-CODE:

    set a := (RW, Global, b, b+1, b)
    set b := 0
    call B.adv (RW-DL, Local, a, a+1, a)
    set b := 42
    call B.adv null
    assert (b==0)
    halt

   *)

  (* Expect:
     pc  := (RX, Global, b_main, e_main, b_main_code)
     cgp := (RW, Global, b, e, b)

     b_main + 0 : WSentry XSRW_ b_switcher e_switcher a_cc_switcher
     b_main + 1 : WSentry RX b_assert e_assert a_assert
     b_main + 2 : WSealed ot_switcher B.f

   *)
  Definition dle_main_code : list Word :=
    let rw_dl := (encodePermPair (RW_DL, Local)) in
    encodeInstrsW [
      (* #"main_b_code"; *)

      (* set b <- 0 *)
      Store cgp 0%Z;      (* b <- 0 *)
      Mov ct0 cgp;        (* ct0 := (RW, Global, b, e, b) *)

      (* set a <- (RW, Global, b, b+1, b) *)
      GetB ct1 cgp;       (* ct1 := b *)
      Add ct2 ct1 1%Z;    (* ct2 := b+1 = a *)
      Subseg ct0 ct1 ct2; (* ct0 := (RW, Global, b, b+1, b) *)

      Lea cgp 1%Z;        (* cgp := (RW, Global, b, e, b+1) *)
      Store cgp ct0;      (* a <- (RW, Global, b, b+1, b) *)
      (* call B.f (RW-DL, Local, a, a+1, a) *)
      Mov ca0 cgp;         (* ca0 := (RW, Global, b, e, b+1) = (RW, Global, b, e, a) *)
      Lea cgp (-1)%Z;      (* cgp := (RW, Global, b, e, b) *)
      Add ct1 ct2 1%Z;     (* ct1 := a+1 *)
      Subseg ca0 ct2 ct1;  (* ca0 := (RW, Global, a, a+1, a) *)
      Restrict ca0 rw_dl  (* ca0 := (RO_DRO, Global, a, a+1, a) *)
    ]
    ++ fetch_instrs 0 ct0 ct1 ct2 (* ct0 -> switcher entry point *)
    ++ fetch_instrs 2 ct1 ct2 ct3 (* ct1 -> {B.f}_(ot_switcher)  *)
    ++
    encodeInstrsW [
      (* Use cs0 and cs1 to save ct0 and ct1 through the call *)
      Mov cs0 ct0; (* cs0 -> switcher entry point *)
      Mov cs1 ct1; (* cs1 -> {B.f}_(ot_switcher)  *)
      (* switcher_call to B.f *)
      Jalr cra ct0;
      (* set b := 42 *)
      Store cgp 42%Z;      (* b <- 0 *)
      (* call B.adv null *)
      Mov ca0 0%Z;
      Mov ct0 cs0; (* ct0 -> switcher entry point *)
      Mov ct1 cs1; (* ct1 -> {B.f}_(ot_switcher)  *)
      (* switcher_call to B.f *)
      Jalr cra ct0;
      (* assert (b==42) *)
      Load ct0 cgp; (* ct0 -> b *)
      Mov ct1 42%Z  (* ct1 -> 42 *)
    ]
    ++ assert_instrs 1 ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    ++
    encodeInstrsW [
      (* halt *)
      Halt
      (* #"main_e" *)
    ].

  Definition dle_main_data : list Word := [WInt 0; WInt 0].

  Definition dle_main_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f
    ].

End DLE_Main.
