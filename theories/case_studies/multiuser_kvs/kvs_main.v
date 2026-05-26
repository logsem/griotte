From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import kvs fetch assert.

Section KVS_Main.
  Context `{MP: MachineParameters}.

  (** Example using the KVS service.

      ```
        #include "kvs.h"

        DECLARE_AND_DEFINE_STATIC_SEALED_VALUE(UserKeyT, service, SealingType, userKey, 1);

        void __cheri_compartment("caller1") entry() {
             auto sealedUserKey = STATIC_SEALED_VALUE(userKey);
             addOrUpdate(sealedUserKey, 1, 12);
             adv.f();
             res = read(sealedUserKey, 1);
             assert (r == 12);
        }
      ```
   *)

  Definition SWITCHER_CALL_OFFSET := 0.
  Definition ASSERT_OFFSET := 1.
  Definition ADV_F_OFFSET := 2.
  Definition KVS_INSERT_OFFSET := 3.
  Definition KVS_READ_OFFSET := 4.
  Definition KVS_ERASE_OFFSET := 5.

  Definition SEALED_USER_KEY_OFFSET := 0.

  Definition kvs_main_code : list Word :=
    encodeInstrsW [
      (* #"main_code"; *)

      (* addOrUpdate(sealedUserKey, 1, 12) *)
      Lea cgp SEALED_USER_KEY_OFFSET; (* TODO remove *)
      Load ca0 cgp;
      Mov ca1 1;
      Mov ca2 12
      ]
    ++ fetch_instrs SWITCHER_CALL_OFFSET ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs KVS_INSERT_OFFSET ct1 ct0 cs0    (* ct1 -> {KVS.addOrUpdate}_(ot_switcher)  *)
    ++ encodeInstrsW [ Jalr cra ctp ]
    (* adv.f() *)
    ++ encodeInstrsW [
      (* check if inserted *)
      Jnz 2 ca0;  (* ca0 = 0 if inserted. So, jumps if no empty slot *)
      (* case INSERT_PASS *)
      Jmp 2;
      (* case INSERT_FAIL *)
      Halt;
      Mov ca0 0;
      Mov ca1 0 ]
    ++ fetch_instrs SWITCHER_CALL_OFFSET ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs ADV_F_OFFSET ct1 ct0 cs0         (* ct1 -> {adv.f}_(ot_switcher)  *)
    ++ encodeInstrsW [ Jalr cra ctp ]
    (* res = read(sealedUserKey, 1) *)
    ++ encodeInstrsW [
      (* read(sealedUserKey, 1)*)
      Lea cgp SEALED_USER_KEY_OFFSET; (* TODO remove *)
      Load ca0 cgp;
      Mov ca1 1
    ]
    ++ fetch_instrs SWITCHER_CALL_OFFSET ctp ct0 ct1 (* ctp -> switcher entry point *)
    ++ fetch_instrs KVS_READ_OFFSET ct1 ct0 cs0      (* ct1 -> {KVS.read}_(ot_switcher)  *)
    ++ encodeInstrsW [ Jalr cra ctp ]
    (* assert (ret == 12) *)
    ++ encodeInstrsW [
      Mov ct0 ca1;
      Mov ct1 12
    ]
    ++ assert_instrs ASSERT_OFFSET ct2 ct3 ct4 (* asserts that ( *ct0 = *ct1 ) *)
    ++ encodeInstrsW [ Halt ]
  .

  Definition KVS_USER_KEY_MAIN : Z := 0.
  Definition kvs_main_data {KVS : kvsLayout} : list Word := [kvs_user_seal_key KVS_USER_KEY_MAIN].

  Definition kvs_main_imports {KVS : kvsLayout}
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f : Sealable) : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher (KVS_addOrUpdate Global);
      WSealed ot_switcher (KVS_read Global);
      WSealed ot_switcher (KVS_erase Global)
    ].

End KVS_Main.
