From cap_machine Require Import machine_parameters assembler.
From cap_machine Require Import switcher.

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

  Definition ASM_TRUE : Z := 0.
  Definition ASM_FALSE : Z := (-1).

  Definition kvs_getFullKey_asm (rdst rsealkey rkey rscratch : RegName) : list asm_code :=
    [
      (* get full key *)
      load rscratch cgp;
      unseal rdst rsealkey rscratch;
      geta rdst rdst;
      lshiftl rdst rdst 16;
      lor rdst rdst rkey
    ].

  (* TODO we could consider encoding option Z as:
     - [?]0 -> None
     - [z]1 -> Some z

     Check option (if ropt contains an option 0):
     - land rres ropt 1  --> rres = if None then 0 else 1
     - lsr ropt 1        --> ropt = if Some z then z else [garbage]

     To make an option z (if rz contains z):
     - Some z
       lsl rres rz 1
       lor rres rres 1
     - None
       mov rres 0

       It would make the search macro a bit more annoying though
   *)

  (** The functions had been refactored to use a (common) search macros.
      It is slightly less faithful to the original code,
      but it accomplishes the same,
      and it will make it easier to verify.
   *)

  (** KVS Search:
      This macro searches whether the element in [rkey] exists in the map.
      Arguments:
      - [cgp] points at the first key of the map
      - [rkey], [ridx] and [rscratch] are clobbered.
      Return value:
      + If the element exists:
        - [cgp] points-to the found key
        - [ridx] >= 0

      + If no element in found:
        - [cgp] points-to the first key of the map
        - [ridx] = -1
   *)
  Definition kvs_search_asm (rkey ridx rscratch: RegName) : (list asm_code) :=
    [
      (* initialise ridx *)
      mov ridx 0%Z;
      (* go through all entries of the map *)
      #".loop_start";
      sub rscratch SIZE_MAP ridx;
      jnz (".loop_body")%asm rscratch;
      jmp (".loop_end_not_found")%asm;
      #".loop_body";
      load rscratch cgp;
      (* we now need to compare rscratch with the full key *)
      sub rscratch rkey rscratch;
      jnz (".not_same_key")%asm rscratch;
      #".same_key";
      (* key was found, [cgp] points-to the the found key *)
      jmp (".loop_end_found")%asm;
      #".not_same_key";
      (* skip, we then finish the body of the loop *)
      lea cgp 2;
      add ridx ridx 1;
      jmp (".loop_start");
      #".loop_end_not_found";
      lea cgp (-(2*SIZE_MAP))%Z;
      mov ridx (-1)%Z;
      #".loop_end_found"
    ].

  (** AddOrUpdate.
      Arguments:
      - [ca0] contains the sealed user key
      - [ca1] contains the map key to insert/update
      - [ca2] contains the new value to insert
      Return values:
      - [ca0] contains TRUE if value was inserted, and FALSE if no empty slot
      - [ca1] contains 0
 *)
  Definition kvs_addOrUpdate_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [ lea cgp 1 ] ;
      (kvs_search_asm ca0 ct1 ct2) ;
      [
        sub ct1 ct1 (-1)%Z;
        jnz (".addOrUpdate_key_not_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        #".addOrUpdate_key_found";
        (* update the value *)
        lea cgp 1;
        store cgp ca2;
        (* return true *)
        mov ca0 ASM_TRUE;
        mov ca1 0;
        jmp cra;
        #".addOrUpdate_key_not_found";
        (* we need to find an empty slot *)
        mov ca0 EMPTY_SLOT
      ] ;
      (kvs_search_asm ctp ct1 ct2) ;
      [
        sub ct1 (-1)%Z ct1;
        jnz (".addOrUpdate_emptyslot_not_found")%asm ct1;
        (* empty slot found, we know that [cgp] points-to it *)
        #".addOrUpdate_emptyslot_found";
        (* insert the key/value in empty slot *)
        store cgp ca0;
        lea cgp 1;
        store cgp ca2;
        (* return true *)
        mov ca0 ASM_TRUE;
        mov ca1 0;
        jmp cra;
        #".addOrUpdate_emptyslot_not_found";
        (* no empty slot found, return false *)
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jmp cra
      ]
    ].

  (** Read.
      Arguments:
      - [ca0] contains the sealed user key
      - [ca1] contains the map key to read
      Return values:
      - [ca0] contains TRUE or FALSE (whether the key was found)
      - [ca1] contains the read value, if the key was found
   *)
  Definition kvs_read_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [ lea cgp 1 ] ;
      (kvs_search_asm ca0 ct1 ct2) ;
      [
        sub ct1 ct1 (-1)%Z;
        jnz (".read_key_not_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        #".read_key_found";
        (* read the value *)
        lea cgp 1;
        load ca1 cgp;
        (* return true *)
        mov ca0 ASM_TRUE;
        jmp cra;
        #".read_key_not_found";
        (* no empty slot found, return false *)
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jmp cra
      ]
    ].


  (** Erase.
      Arguments:
      - [ca0] contains the sealed user key
      - [ca1] contains the map key to erase
      Return values:
      - [ca0] and [ca1] contains 0
   *)
  Definition kvs_erase_asm : list (list asm_code) :=
    [
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [ lea cgp 1 ] ;
      (kvs_search_asm ca0 ct1 ct2) ;
      [
        sub ct1 ct1 (-1)%Z;
        jnz (".erase_key_not_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        #".erase_key_found";
        (* erase the key *)
        store cgp EMPTY_SLOT;
        lea cgp 1;
        store cgp 0;
        (* return void *)
        #".erase_key_not_found";
        (* no empty slot found, return void *)
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

  Definition kvs_service_instrs : list Word :=
    kvs_addOrUpdate_instrs ++ kvs_read_instrs ++ kvs_erase_instrs.

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

  Class kvsLayout : Type :=
    mkCmptKvs {
        KVS_OTYPE : OType;
        b_kvs_exp_tbl : Addr;
        e_kvs_exp_tbl : Addr
      }.


  Definition kvs_user_seal_key {KVS : kvsLayout} (n : nat) :=
    WSealed KVS_OTYPE (SCap (O LG LM) Global 0%a 0%a (0 ^+ n)%a).

  Definition length_kvs_imports := length (kvs_imports za za za za_ot).

  Definition kvs_exp_tbl_entry_addOrUpdate :=
    WInt (encode_entry_point 3 (length_kvs_imports)).

  Definition KVS_addOrUpdate {KVS : kvsLayout} : Sealable :=
    SCap RO Global b_kvs_exp_tbl e_kvs_exp_tbl (b_kvs_exp_tbl ^+2)%a.

  Definition kvs_exp_tbl_entry_read :=
    WInt (encode_entry_point 2 (length_kvs_imports + length kvs_addOrUpdate_instrs)).

  Definition KVS_read {KVS : kvsLayout} : Sealable :=
    SCap RO Global b_kvs_exp_tbl e_kvs_exp_tbl (b_kvs_exp_tbl ^+3)%a.

  Definition kvs_exp_tbl_entry_erase :=
    WInt (encode_entry_point 2 (length_kvs_imports + length kvs_addOrUpdate_instrs + length kvs_erase_instrs)).

  Definition KVS_erase {KVS : kvsLayout} : Sealable :=
    SCap RO Global b_kvs_exp_tbl e_kvs_exp_tbl (b_kvs_exp_tbl ^+4)%a.

  Definition kvs_export_table_entries : list Word :=
    [ kvs_exp_tbl_entry_addOrUpdate;
      kvs_exp_tbl_entry_read;
      kvs_exp_tbl_entry_erase
    ].

End KVS_Service.
