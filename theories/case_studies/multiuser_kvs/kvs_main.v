From griotte Require Import machine_parameters assembler.
From griotte Require Import kvs fetch assert.

Section KVS_Main.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.
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

  Definition SWITCHER_CALL_OFFSET : nat := 0.
  Definition ASSERT_OFFSET : nat := 1.
  Definition ADV_F_OFFSET : nat := 2.
  Definition KVS_INSERT_OFFSET : nat := 3.
  Definition KVS_READ_OFFSET : nat := 4.
  Definition KVS_ERASE_OFFSET : nat := 5.
  Definition SEALED_USER_KEY_OFFSET : nat := 6.

  (** The main program. The data symbols [#@] name the entries of the
      import table, which precedes the code, in the order of
      [kvs_main_imports]; the offsets above are their indices. *)
  Definition kvs_main_asm : list (list asm_code) :=
    [ (* 0: fetch the sealed user key *)
      [ #@".Limport_switcher";
        #@".Limport_assert";
        #@".Limport_adv";
        #@".Limport_addOrUpdate";
        #@".Limport_read";
        #@".Limport_erase";
        #@".Limport_user_key";
        #".Lkvs_main" ] ++
      fetch_asm ".Limport_user_key" cs1;
      (* 1: addOrUpdate(sealedUserKey, 1, 12) *)
      [ mov cs0 cra; (* cs0 -> return-to-switcher *)
        mov ca0 cs1;
        mov ca1 1;
        mov ca2 12 ];
      (* 2: ctp -> switcher entry point *)
      fetch_asm ".Limport_switcher" ctp;
      (* 3: ct1 -> {KVS.addOrUpdate}_(ot_switcher) *)
      fetch_asm ".Limport_addOrUpdate" ct1;
      (* 4 *)
      [ jalr cra ctp ];
      (* 5: check if inserted *)
      [ jnez 2 ca0; (* ca0 = 0 if inserted. So, jumps if no empty slot *)
        (* case INSERT_PASS *)
        jmp 2;
        (* case INSERT_FAIL / ENOTENOUGHTRUSTEDSTACK *)
        jmp ".Lkvs_return";
        (* case INSERT_PASS *)
        mov ca0 0;
        mov ca1 0 ];
      (* 6: ctp -> switcher entry point *)
      fetch_asm ".Limport_switcher" ctp;
      (* 7: ct1 -> {adv.f}_(ot_switcher) *)
      fetch_asm ".Limport_adv" ct1;
      (* 8: adv.f() *)
      [ jalr cra ctp ];
      (* 9: res = read(sealedUserKey, 1) *)
      [ mov ca0 cs1;
        mov ca1 1 ];
      (* 10: ctp -> switcher entry point *)
      fetch_asm ".Limport_switcher" ctp;
      (* 11: ct1 -> {KVS.read}_(ot_switcher) *)
      fetch_asm ".Limport_read" ct1;
      (* 12 *)
      [ jalr cra ctp ];
      (* 13: check if ENOTENOUGHTRUSTEDSTACK *)
      [ jnez 2 ca0; (* ca0 = 0 if NOT ENOTENOUGHTRUSTEDSTACK. *)
        (* case PASS *)
        jmp 2;
        (* case ENOTENOUGHTRUSTEDSTACK *)
        jmp ".Lkvs_return";
        (* case PASS *)
        mov ct0 ca1;
        mov ct1 12 ];
      (* 14: assert (ret == 12), that is ( *ct0 = *ct1 ) *)
      assert_asm ".Limport_assert" ct2 ca2;
      (* 15: return, the thread exits *)
      [ #".Lkvs_return";
        mov cra cs0;
        ret ]
    ].

  Definition kvs_main_assembled :=
    Eval compute in assemble_block kvs_main_asm.
  Lemma kvs_main_assembles : asm_ok (assemble_block_check kvs_main_asm).
  Proof. asm_check. Qed.
  Definition kvs_main_instrs_n (n : nat) : list Word :=
    encodeInstrsW (default [] (kvs_main_assembled !! n)).

  Definition kvs_main_add_phase_instrs : list Word :=
    kvs_main_instrs_n 0
    ++ kvs_main_instrs_n 1
    ++ kvs_main_instrs_n 2
    ++ kvs_main_instrs_n 3
    ++ kvs_main_instrs_n 4
    ++ kvs_main_instrs_n 5.

  Definition kvs_main_adversary_phase_instrs : list Word :=
    kvs_main_instrs_n 6
    ++ kvs_main_instrs_n 7
    ++ kvs_main_instrs_n 8.

  Definition kvs_main_read_assert_phase_instrs : list Word :=
    kvs_main_instrs_n 9
    ++ kvs_main_instrs_n 10
    ++ kvs_main_instrs_n 11
    ++ kvs_main_instrs_n 12
    ++ kvs_main_instrs_n 13
    ++ kvs_main_instrs_n 14
    ++ kvs_main_instrs_n 15.

  Definition kvs_main_code : list Word :=
    kvs_main_instrs_n 0
    ++ kvs_main_instrs_n 1
    ++ kvs_main_instrs_n 2
    ++ kvs_main_instrs_n 3
    ++ kvs_main_instrs_n 4
    ++ kvs_main_instrs_n 5
    ++ kvs_main_instrs_n 6
    ++ kvs_main_instrs_n 7
    ++ kvs_main_instrs_n 8
    ++ kvs_main_instrs_n 9
    ++ kvs_main_instrs_n 10
    ++ kvs_main_instrs_n 11
    ++ kvs_main_instrs_n 12
    ++ kvs_main_instrs_n 13
    ++ kvs_main_instrs_n 14
    ++ kvs_main_instrs_n 15.

  #[local] Close Scope Z_scope.
  #[local] Coercion Z.of_nat : nat >-> Z.

  Definition kvs_main_data  : list Word := [].
  Definition kvs_main_static_sealed ( KVS_USER_KEY_MAIN : Z ) : list Word := [ WInt KVS_USER_KEY_MAIN ].

  Definition kvs_main_imports {KVS : kvsLayout}
    (kvs_main_static_sealed_addr : Addr)
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    (b_assert e_assert : Addr)
    (B_f : Sealable) : list Word :=
    [
      WSentry FwdDisable true XSRW_ Local b_switcher e_switcher a_cc_switcher;
      WSentry Inherit true RX Global b_assert e_assert b_assert;
      WSealed ot_switcher B_f;
      WSealed ot_switcher (KVS_addOrUpdate Global);
      WSealed ot_switcher (KVS_read Global);
      WSealed ot_switcher (KVS_erase Global);
      (kvs_user_seal_key Global kvs_main_static_sealed_addr)
    ].

End KVS_Main.

(** The code of the concrete adversary of [kvs_concrete], assembled here,
    away from the program logic's coercions. It inserts key [1] with value
    [42] in its own KVS namespace, then erases that key. It restores its
    return capability and clears its argument registers before returning to
    the main program. *)
Section kvs_B_code.
  Import Asm_Griotte.
  #[local] Open Scope Z_scope.

  Definition kvs_B_asm : list asm_code :=
    [ #@".Limport_switcher";
      #@".Limport_addOrUpdate";
      #@".Limport_read";
      #@".Limport_erase";
      #@".Limport_user_key";
      #"adv_entry" ] ++
    (* Fetch the adversary's sealed KVS user key. *)
    fetch_asm ".Limport_user_key" cs1 ++
    (* Preserve the return capability and prepare
       addOrUpdate(sealed key, 1, 42). *)
    [ mov cs0 cra;
      mov ca0 cs1;
      mov ca1 1;
      mov ca2 42 ] ++
    (* Fetch the switcher entry point and the sealed KVS.addOrUpdate entry
       point, and invoke KVS.addOrUpdate through the switcher. *)
    fetch_asm ".Limport_switcher" ctp ++
    fetch_asm ".Limport_addOrUpdate" ct1 ++
    [ jalr cra ctp;
      (* Prepare erase(sealed key, 1). *)
      mov ca0 cs1;
      mov ca1 1 ] ++
    (* Fetch the switcher entry point and the sealed KVS.erase entry point,
       and invoke KVS.erase through the switcher. *)
    fetch_asm ".Limport_switcher" ctp ++
    fetch_asm ".Limport_erase" ct1 ++
    [ jalr cra ctp;
      (* Restore the return capability, clear arguments, and return via the
         switcher. *)
      mov cra cs0;
      mov ca0 0;
      mov ca1 0;
      mov ca2 0;
      ret ].

  Definition kvs_B_instrs : list instr :=
    Eval compute in assemble kvs_B_asm.
  Lemma kvs_B_assembles : asm_ok (assemble_check kvs_B_asm).
  Proof. asm_check. Qed.

  (** The offset of the entry point from the start of the PCC. *)
  Definition kvs_B_adv_entry : nat :=
    Eval vm_compute in label_offset kvs_B_asm "adv_entry".
End kvs_B_code.

(** The index of the export [f] of the adversary [B], in the order of the
    firmware. *)
Definition kvs_B_entry_f : nat := 0.
