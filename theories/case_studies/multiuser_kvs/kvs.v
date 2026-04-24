From cap_machine Require Import machine_parameters assembler.

Section KVS_Service.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  (** Multiuser KVS service inspired from
      https://github.com/vmurali/cheriot-rtos/blob/service/examples/11.service/service.cc

      TODO description of the service
   *)
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
  Definition SIZE_MAP := 16.

  Definition EMPTY_SLOT : Z := -1.
  Definition DEFAULT_VAL : Z := 0.

  Definition kvs_getFullKey_asm (rdst rsealkey rkey rscratch : RegName) : list asm_code :=
    [
      (* get full key *)
      load rscratch cgp;
      unseal rdst rsealkey rscratch;
      geta rdst rdst;
      lshiftl rdst rdst 16;
      lor rdst rdst rkey
    ].
  (* TODO I think the 3 functions can be refactored by using a (common) search macros.
     It would probably be slitghly less faithfull to the original code,
     but it would make it much easier to verify.
 *)

  (* TODO I'm pretty sure this code is not correct *)
  Definition kvs_addOrUpdate_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [
        lea cgp 1;
        mov ct0 0; (* 0 mean false *)
        mov ct1 0; (* ct1 contains the index of loop *)
        (* go through all entries of the map *)
        #".loop_start";
        sub ct2 SIZE_MAP ct1;
        jnz (".loop_body")%asm ct2;
        jmp (".loop_end")%asm;
        #".loop_body";
        load ct2 cgp;
        (* we need to check that not -1 (empty slot) *)
        sub ct2 ct2 EMPTY_SLOT;
        jnz (".not_empty_slot") ct2;
        (* slot is empty, we exit the loop *)
        #".empty_slot";
        jmp (".loop_end");
        (* slot is not empty, we now need to compare ct2 with the full key *)
        #".not_empty_slot";
        sub ct2 ca0 ct2;
        jnz (".not_same_key") ct2;
        #".same_key";
        (* update the value *)
        lea cgp 1;
        store cgp ca2;
        mov ca0 1;
        jmp (".return")%asm;
        #".not_same_key";
        (* skip, we then finish the body of the loop *)
        lea cgp 2;
        add ct1 ct1 1;
        jmp (".loop_start");
        #".loop_end"
      ];
      [
        (* if ct0 still contains 0, then we did not find an existing key, and we need to add *)
        jnz (".key_found")%asm ct0
      ];
      [
        #".key_not_found";
        (* cgp already points to the first empty slot in the map *)
        store cgp ca0;
        lea cgp 1;
        store cgp ca2;
        mov ca0 0;
        jmp (".return")%asm
      ];
      [
        #".key_found";
        (* return true *)
        mov ca0 1
      ];
      [
        #".return";
        (* return *)
        mov ca1 0;
        jmp cra
      ]
    ].

  Definition kvs_read_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [
        lea cgp 1;
        mov ct0 DEFAULT_VAL; (* 0 is the default value if key not found in KVS *)
        mov ct1 0; (* ct1 contains the index of loop *)
        (* go through all entries of the map *)
        #".loop_start";
        sub ct2 SIZE_MAP ct1;
        jnz (".loop_body")%asm ct2;
        jmp (".loop_end")%asm;
        #".loop_body";
        load ct2 cgp;
        (* we need to check that not -1 (empty slot) *)
        sub ct2 ct2 EMPTY_SLOT;
        jnz (".not_empty_slot") ct2;
        (* slot is empty, we exit the loop *)
        #".empty_slot";
        jmp (".loop_end");
        (* slot is not empty, we now need to compare ct2 with the full key *)
        #".not_empty_slot";
        sub ct2 ca0 ct2;
        jnz (".not_same_key") ct2;
        #".same_key";
        (* return the read value *)
        lea cgp 1;
        load ct0 cgp;
        #".not_same_key";
        (* skip, we then finish the body of the loop *)
        lea cgp 2;
        add ct1 ct1 1;
        jmp (".loop_start");
        #".loop_end"
      ];
      [
        #".return";
        (* ct0 contains the read value; or 0 if no existing key *)
        mov ca0 ct1;
        (* return *)
        mov ca1 0;
        jmp cra
      ]
    ].

  Definition kvs_erase_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [
        lea cgp 1;
        mov ct0 0; (* 0 is the default value if key not found in KVS *)
        mov ct1 0; (* ct1 contains the index of loop *)
        (* go through all entries of the map *)
        #".loop_start";
        sub ct2 SIZE_MAP ct1;
        jnz (".loop_body")%asm ct2;
        jmp (".loop_end")%asm;
        #".loop_body";
        load ct2 cgp;
        (* we need to check that not -1 (empty slot) *)
        sub ct2 ct2 EMPTY_SLOT;
        jnz (".not_empty_slot") ct2;
        (* slot is empty, we exit the loop *)
        #".empty_slot";
        jmp (".loop_end");
        (* slot is not empty, we now need to compare ct2 with the full key *)
        #".not_empty_slot";
        sub ct2 ca0 ct2;
        jnz (".not_same_key") ct2;
        #".same_key";
        (* erase the value and delete the key *)
        store cgp EMPTY_SLOT;
        lea cgp 1;
        store cgp DEFAULT_VAL;
        #".not_same_key";
        (* skip, we then finish the body of the loop *)
        lea cgp 2;
        add ct1 ct1 1;
        jmp (".loop_start");
        #".loop_end"
      ];
      [
        #".return";
        (* no return value *)
        (* return *)
        mov ca0 0;
        mov ca1 0;
        jmp cra
      ]
    ].

  Definition kvs_getFullKey (rdst rsealkey rkey rscratch : RegName) :=
    Eval compute in assemble (kvs_getFullKey_asm rdst rsealkey rkey rscratch).
  Definition kvs_getFullKey_instrs (rdst rsealkey rkey rscratch : RegName) : list Word :=
    encodeInstrsW (kvs_getFullKey rdst rsealkey rkey rscratch).


  Definition assembled_kvs_addOrUpdate' := Eval vm_compute in (assemble_block kvs_addOrUpdate_asm).
  Definition assembled_kvs_addOrUpdate  := Eval cbv in (revert_regs_code_block assembled_kvs_addOrUpdate').
  Definition kvs_addOrUpdate_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_addOrUpdate).

  Definition assembled_kvs_read' := Eval vm_compute in (assemble_block kvs_read_asm).
  Definition assembled_kvs_read  := Eval cbv in (revert_regs_code_block assembled_kvs_read').
  Definition kvs_read_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_read).

  Definition assembled_kvs_erase' := Eval vm_compute in (assemble_block kvs_erase_asm).
  Definition assembled_kvs_erase  := Eval cbv in (revert_regs_code_block assembled_kvs_erase').
  Definition kvs_erase_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_erase).

  Fixpoint repeat_list `{A : Type} (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n => l ++ repeat_list l n
    end.

  Definition kvs_initial_map :=
    repeat_list [WInt EMPTY_SLOT; WInt DEFAULT_VAL] SIZE_MAP.

  Definition kvs_data (OUserKey : OType) : list Word :=
    [WSealRange (false, true) Global OUserKey (OUserKey^+1)%ot OUserKey] ++ kvs_initial_map.

  Definition kvs_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher
    ].
End KVS_Service.
