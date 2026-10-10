From griotte Require Import machine_parameters assembler.
From griotte Require Import bitblast.
From griotte Require Import switcher.

Section KVS_Service.
  Import Asm_Griotte.
  Context `{MP: MachineParameters}.
  Local Coercion Z.of_nat : nat >-> Z.

  (* Encoding of type constructors into ASM *)
  Definition ASM_TRUE : Z := 0.
  Definition ASM_FALSE : Z := (-1).

  Definition ASM_NONE : Z := 0.
  Definition ASM_SOME : Z := 1.


  (** Multiuser KVS service inspired from
      https://github.com/vmurali/cheriot-rtos/blob/service/examples/11.service/service.cc

      The multiuser KVS is a key-value store service where a single, global data structure
      contains multiple databases and is maintained by a single compartment, the KVS service.
      Each users have access to their unique (sealed) user key,
      and only the KVS compartment can unseal them to read the user key value.

      Because each users have only access to their own, unique sealed user key,
      we know that multiple, mutually distrustful users cannot read or change
      the other users' sub-KVS.
   *)

  (*
    Import+UNSEALING_USER_KEY_OFFSET  : [U, Global, OUserKey, OUserKey + 1, OUserKey]

    ca0 : sealedUserKey
    ca1 : key
    ca2 : val

    cgp0  : option0
    cgp1  : key0
    cgp2  : val0
    ...   : ...
    cgp45 : option15
    cgp46 : key15
    cgp47 : val15
   *)
  Definition SIZE_MAP := 16.

  Definition EMPTY_SLOT : Z := -1.
  Definition DEFAULT_VAL : Z := 0.

  Definition ASM_SIZEOF_KVS_ENTRY : Z := 3.
  Definition UNSEALING_USER_KEY_OFFSET := 1.

  (** CHERIoT-C++ code of `getFullKey`:
<<
FKeyT getFullKey(Sealed<UKeyT> suk, MKeyT mk) {
TokenKey kvsSKey = STATIC_SEALING_TYPE(SUKeyT);
int16_t uk = token_unseal(kvsSKey, suk)->value;
return (uk << 16 | mk);
}
>>
   *)
  Definition kvs_getFullKey_asm (rdst rsealkey rkey rscratch1 rscratch2 : RegName) : list asm_code :=
    [(* fetch sealing key from imports *)
      mov rdst PC;
      getb rscratch1 rdst;
      geta rscratch2 rdst;
      sub rscratch1 rscratch1 rscratch2;
      lea rdst rscratch1;
      lea rdst UNSEALING_USER_KEY_OFFSET;
      load rdst rdst;
      (* get full key *)
      unseal rdst rdst rsealkey;
      load rdst rdst;
      lshiftl rdst rdst 16;
      lor rdst rdst rkey
    ].

  Definition kvs_getFullKey (rdst rsealkey rkey rscratch1 rscratch2 : RegName) :=
    Eval compute in assemble (kvs_getFullKey_asm rdst rsealkey rkey rscratch1 rscratch2).
  Definition kvs_getFullKey_instrs (rdst rsealkey rkey rscratch1 rscratch2 : RegName) : list Word :=
    encodeInstrsW (kvs_getFullKey rdst rsealkey rkey rscratch1 rscratch2).

  (** The functions had been refactored to use a (common) search macros.
      It is slightly less faithful to the original code,
      but it accomplishes the same,
      and it will make it easier to verify.
   *)

  (** CHERIoT-C++ code of `search`:
<<
pair<int, int> search(FKeyT fk) {
  int idxEmpty = -1;
  for (int i = 0; i < SIZE; i++) {
    if(entries[i]) {
      if(entries[i]->first == fk)
      { return {i, idxEmpty} ; }
    } else { idxEmpty = i; }
  }
  return {-1, idxEmpty};
}
>>
   *)

  (** KVS Search:
      This macro searches whether the element in [rkey] exists in the map.
      Arguments:
      - [cgp] points at the first key of the map
      - [ridx], [ridx_empty] and [rscratch] are clobbered.
      Return value:
      + If the element exists:
        - [cgp] points-to the found key
        - [ridx] >= 0

      + If no element in found:
        - [cgp] points-to the first key of the map
        - [ridx] = -1
        - [ridx_empty] = _index_ of an empty slot if available, -1 otherwise
   *)
  Definition kvs_search_asm_pre (rkey ridx ridx_empty rscratch : RegName) : (list asm_code) :=
    [
      (* initialise ridx *)
      mov ridx 0%Z;
      mov ridx_empty (-1)%Z;
      (* go through all entries of the map *)
      #".loop_start";
      sub rscratch SIZE_MAP ridx;
      jnz (".loop_body")%asm rscratch;
      jmp (".loop_end_not_found")%asm;
      #".loop_body";
      load rscratch cgp;
      (* we now need check if the index is None or Some *)
      jnz (".some_index")%asm rscratch;
      #".none_index";
      mov ridx_empty ridx;
      lea cgp ASM_SIZEOF_KVS_ENTRY;
      add ridx ridx 1;
      jmp (".loop_start");
      #".some_index";
      (* we now need to compare rscratch with the full key *)
      lea cgp 1;
      load rscratch cgp;
      sub rscratch rkey rscratch;
      jnz (".not_same_key")%asm rscratch;
      #".same_key";
      lea cgp (-1)%Z;
      (* key was found, [cgp] points-to the the found key *)
      jmp (".loop_end_found")%asm;
      #".not_same_key";
      (* skip, we then finish the body of the loop *)
      lea cgp 2;
      add ridx ridx 1;
      jmp (".loop_start");
      #".loop_end_not_found";
      lea cgp (-(ASM_SIZEOF_KVS_ENTRY*SIZE_MAP))%Z;
      mov ridx (-1)%Z;
      #".loop_end_found"
    ].
  Definition kvs_search_asm_env (rkey ridx ridx_empty rscratch : RegName) :=
    Eval vm_compute in (compute_asm_code_env (kvs_search_asm_pre rkey ridx ridx_empty  rscratch)).2.
  Definition kvs_search_asm (rkey ridx ridx_empty  rscratch : RegName) :=
    Eval compute in resolve_labels_macros (kvs_search_asm_pre rkey ridx ridx_empty  rscratch)
                      (kvs_search_asm_env rkey ridx ridx_empty  rscratch).
  Definition kvs_search (rkey ridx ridx_empty  rscratch : RegName) :=
    Eval compute in assemble (kvs_search_asm rkey ridx ridx_empty  rscratch).
  Definition kvs_search_instrs (rkey ridx ridx_empty  rscratch : RegName) : list Word :=
    encodeInstrsW (kvs_search rkey ridx ridx_empty  rscratch).

  Definition UINT16_MIN : Z := 0.
  Definition UINT16_MAX : Z := 2 ^ 16.


  (** CHERIoT-C++ code of `dyn_check_uint16`:
<<
bool dyn_check_uint16(MKeyT mk) {
    return (0 <= mk && mk < UINT16_MAX);
}
>>
   *)

  (**  KVS uint16 check:
       This macros checks whether the argument [rv] is a correct UINT16,
       and in particular that UINT16_MIN <= [rv] < UINT16_MAX.
       Arguments:
       - [rv] contains the value that will be checked
       - [rdst] -
       Result:
       - [rv]: not changed
       - [rdst]: if is_uint16(rv) then ASM_TRUE else ASM_FALSE
   *)
  Definition kvs_check_uint16_asm_pre (rv rdst : RegName) : (list asm_code) :=
    [
      lt rdst (UINT16_MIN-1)%Z rv; (* rdst := if (UINT16_MIN <= rv) then 0 else 1 *)
      jnz (".kvs_key_check_uint16_min")%asm rdst;
      #".kvs_key_check_uint16_too_low";
      mov rdst ASM_FALSE;
      jmp (".kvs_key_ret")%asm;
      #".kvs_key_check_uint16_min";
      lt rdst rv UINT16_MAX; (* rdst := if (rv < UINT16_MAX) then 0 else 1 *)
      jnz (".kvs_key_check_uint16_max")%asm rdst;
      #".kvs_key_check_uint16_too_big";
      mov rdst ASM_FALSE;
      jmp (".kvs_key_ret")%asm;
      #".kvs_key_check_uint16_max";
      mov rdst ASM_TRUE;
      #".kvs_key_ret"
    ].
  Definition kvs_check_uint16_asm_env (rv rdst : RegName) :=
    Eval vm_compute in (compute_asm_code_env (kvs_check_uint16_asm_pre rv rdst)).2.
  Definition kvs_check_uint16_asm (rv rdst : RegName) :=
    Eval compute in resolve_labels_macros (kvs_check_uint16_asm_pre rv rdst)
                      (kvs_check_uint16_asm_env rv rdst).
  Definition kvs_check_uint16 (rv rdst : RegName) :=
    Eval compute in assemble (kvs_check_uint16_asm rv rdst).
  Definition kvs_check_uint16_instrs (rv rdst : RegName) : list Word :=
    encodeInstrsW (kvs_check_uint16 rv rdst).


  (** CHERIoT-C++ code of `insert`:
<<
bool __cheri_compartment("kvs") insert(Sealed<UKeyT> suk, MKeyT mk, Val val)
{
  if ( !dyn_check_uint16( mk ) ) { return false; }
  FKeyT fk = getFullKey(suk, mk);

  // Search if the full key already exists
  pair<int, int> res = search(fk);
  // The key exists and is updated
  if ( res.first != -1 )
  { entries[res.first]->second = val; return true; }
  // The key does not exists, check if there is an empty spot
  if (res.second != -1) {
    entries[res.second] = {fk, val};
    return true;
  }
  return false;
}
>>
   *)

  (** AddOrUpdate.
      Arguments:
      - [ca0] contains the sealed user key
      - [ca1] contains the map key to insert/update
      - [ca2] contains the new value to insert
      Return values:
      - [ca0] contains TRUE if value was inserted, and FALSE if no empty slot or key not uint16
      - [ca1] contains 0
 *)
  Definition kvs_addOrUpdate_asm : list (list asm_code) :=
    [
      (kvs_check_uint16_asm ca1 ct1) ;
      [
        jnz (".addOrUpdate_not_uint16")%asm ct1;
        #".addOrUpdate_uint16";
        jmp (".addOrUpdate_uint16_check_pass")%asm;
        #".addOrUpdate_not_uint16";
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jalr cnull cra;
        #".addOrUpdate_uint16_check_pass"
      ]
      ;
      (kvs_getFullKey_asm ctp ca0 ca1 ct1 ct2)
      (* ca0 contains the full key *)
      ;
      [ mov ca0 ctp ] ;
      (kvs_search_asm ca0 ctp ct1 ct2) ;
      (* ctp: -1 if element not found  *)
      (* ct1: -1 if no empty slot, otherwise index of empty slot *)
      [

        sub ctp ctp (-1)%Z;
        jnz (".addOrUpdate_key_found")%asm ctp;

        (* key was not found, we need to check if there's a empty slot available *)
        #".addOrUpdate_key_not_found";
        (* we need to find an empty slot *)
        sub ctp ct1 (-1)%Z;
        jnz (".addOrUpdate_empty_slot_found")%asm ctp;

        (* no empty slot found, return false *)
        #".addOrUpdate_empty_slot_not_found";
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jalr cnull cra;
        (* empty slot found: insert some/key/value *)

        #".addOrUpdate_empty_slot_found";
        (* make cgp points to the empty index *)
        mul ct1 ct1 ASM_SIZEOF_KVS_ENTRY;
        lea cgp ct1;
        (* insert Some *)
        store cgp ASM_SOME;
        lea cgp 1;
        (* insert Key *)
        store cgp ca0;
        lea cgp 1;
        (* insert Value *)
        store cgp ca2;
        (* return true *)
        mov ca0 ASM_TRUE;
        mov ca1 0;
        jalr cnull cra;

        (* key was found, we know that [cgp] points-to it *)
        #".addOrUpdate_key_found";
        (* update the value *)
        lea cgp 2;
        store cgp ca2;
        (* return true *)
        mov ca0 ASM_TRUE;
        mov ca1 0;
        jalr cnull cra

      ]
    ].
  Definition assembled_kvs_addOrUpdate' := Eval vm_compute in (assemble_block kvs_addOrUpdate_asm).
  Definition assembled_kvs_addOrUpdate  := Eval cbv in (revert_regs_code_block assembled_kvs_addOrUpdate').
  Definition kvs_addOrUpdate_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_addOrUpdate).


  (** CHERIoT-C++ code of `read`:
<<
optional<Val> __cheri_compartment("kvs") read(Sealed<UKeyT> suk, MKeyT mk)
{
    if ( !dyn_check_uint16( mk ) ) { return nullopt; }
    FKeyT fk = getFullKey(suk, mk);

    // Search if the full key exists
    pair<int, int> res = search(fk);
    // The key exists and is read
    if ( res.first != -1 )
    { return entries[res.second]->second; }
    // The key is not found
    return nullopt;
}
>>
   *)

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
      (kvs_check_uint16_asm ca1 ct1) ;
      [
        jnz (".read_not_uint16")%asm ct1;
        #".read_uint16";
        jmp (".read_uint16_check_pass")%asm;
        #".read_not_uint16";
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jalr cnull cra;
        #".read_uint16_check_pass"
      ]
      ;
      (kvs_getFullKey_asm ctp ca0 ca1 ct1 ct2)
      (* ca0 contains the full key *)
      ;
      [ mov ca0 ctp ] ;
      (kvs_search_asm ca0 ctp ct1 ct2) ;
      [
        sub ctp ctp (-1)%Z;
        jnz (".read_key_found")%asm ctp;
        (* key was found, we know that [cgp] points-to it *)
        #".read_key_not_found";
        (* no empty slot found, return false *)
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jmp (".read_key_ret")%asm;
        #".read_key_found";
        (* read the value *)
        lea cgp 2;
        load ca1 cgp;
        (* return true *)
        mov ca0 ASM_TRUE;
        #".read_key_ret";
        jalr cnull cra
      ]
    ].
  Definition assembled_kvs_read' := Eval vm_compute in (assemble_block kvs_read_asm).
  Definition assembled_kvs_read  := Eval cbv in (revert_regs_code_block assembled_kvs_read').
  Definition kvs_read_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_read).

  (** CHERIoT-C++ code of `erase`:
<<
void __cheri_compartment("kvs") erase(Sealed<UKeyT> suk, MKeyT mk)
{
    if ( !dyn_check_uint16( mk ) ) { return; }
    FKeyT fk = getFullKey(suk, mk);

    // Search if the full key already exists
    pair<int, int> res = search(fk);
    // The key exists and is erased
    if ( res.first != -1 )
    { entries[res.second] = nullopt; }
}
>>
   *)

  (** Erase.
      Arguments:
      - [ca0] contains the sealed user key
      - [ca1] contains the map key to erase
      Return values:
      - [ca0] and [ca1] contains 0
   *)
  Definition kvs_erase_asm : list (list asm_code) :=
    [
      (kvs_check_uint16_asm ca1 ct1) ;
      [
        jnz (".erase_not_uint16")%asm ct1;
        #".erase_uint16";
        jmp (".erase_uint16_check_pass")%asm;
        #".erase_not_uint16";
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jalr cnull cra;
        #".erase_uint16_check_pass"
      ]
      ;
      (kvs_getFullKey_asm ctp ca0 ca1 ct1 ct2)
      (* ca0 contains the full key *)
      ;
      [ mov ca0 ctp ] ;
      (kvs_search_asm ca0 ctp ct1 ct2) ;
      [
        sub ctp ctp (-1)%Z;
        jnz (".erase_key_found")%asm ctp;
        (* key was found, we know that [cgp] points-to it *)
        (* return void *)
        #".erase_key_not_found";
        jmp (".erase_return");
        #".erase_key_found";
        (* erase the key *)
        store cgp ASM_NONE;
        #".erase_return";
        (* return void *)
        mov ca0 0;
        mov ca1 0;
        jalr cnull cra
      ]
    ].
  Definition assembled_kvs_erase' := Eval vm_compute in (assemble_block kvs_erase_asm).
  Definition assembled_kvs_erase  := Eval cbv in (revert_regs_code_block assembled_kvs_erase').
  Definition kvs_erase_instrs : list Word := concat (encodeInstrsW <$> assembled_kvs_erase).


  Definition kvs_service_instrs : list Word :=
    kvs_addOrUpdate_instrs ++ kvs_read_instrs ++ kvs_erase_instrs.


  Local Definition kvs_service_unsealing_key_pre (KVS_OTYPE : OType) :=
    WSealRange (false, true) Global KVS_OTYPE (KVS_OTYPE^+1)%ot KVS_OTYPE.

  Local Definition kvs_imports_pre (b_switcher e_switcher a_cc_switcher : Addr) (KVS_OTYPE : OType) (ot_switcher : OType)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher;
      (kvs_service_unsealing_key_pre KVS_OTYPE)
    ].

  Definition length_kvs_imports := length (kvs_imports_pre za za za za_ot za_ot).

  Fixpoint repeat_list `{A : Type} (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n => l ++ repeat_list l n
    end.

  Definition kvs_data :=
    repeat_list [WInt ASM_NONE;WInt EMPTY_SLOT; WInt DEFAULT_VAL] SIZE_MAP.

  Definition length_kvs_data := length kvs_data.

  Definition kvs_nb_exports : Z := 3.
  Definition length_kvs_exports_tbl : Z := 2 + kvs_nb_exports.

  Class kvsLayout : Type :=
    mkKvsLayout {
        KVS_OTYPE : OType;

        KVS_pcc_b : Addr;
        KVS_pcc_b' : Addr;
        KVS_pcc_e : Addr;


        KVS_cgp_b : Addr;
        KVS_cgp_e : Addr;


        b_kvs_exp_tbl : Addr;
        e_kvs_exp_tbl : Addr;
      }.

  Class kvsLayoutWf `{kvsLayout} : Type :=
    mkKvsLayoutWf {
        KVS_OTYPE_size : (KVS_OTYPE < KVS_OTYPE ^+ 1)%ot;

        KVS_size_imports : (KVS_pcc_b + length_kvs_imports)%a = Some KVS_pcc_b';

        KVS_size_code : (KVS_pcc_b' + length kvs_service_instrs)%a = Some KVS_pcc_e;

        KVS_size_data : (KVS_cgp_b + length_kvs_data)%a = Some KVS_cgp_e;

        kvs_exp_tbl_size : (b_kvs_exp_tbl + length_kvs_exports_tbl)%a = Some e_kvs_exp_tbl
      }.

  (* Meta information about addOrUpdate entry point *)
  Definition kvs_addOrUpdate_nargs : nat := 3.
  Definition kvs_addOrUpdate_pcc_off := (length_kvs_imports).
  Definition kvs_addOrUpdate_pcc_addr {KVS : kvsLayout} := (KVS_pcc_b ^+ kvs_addOrUpdate_pcc_off)%a.
  Definition kvs_exp_tbl_entry_addOrUpdate :=
    WInt (encode_entry_point kvs_addOrUpdate_nargs kvs_addOrUpdate_pcc_off).
  Definition kvs_addOrUpdate_exp_tbl_off : nat := 2.
  Definition kvs_addOrUpdate_exp_tbl_addr {KVS : kvsLayout} : Addr := (b_kvs_exp_tbl ^+ kvs_addOrUpdate_exp_tbl_off)%a.
  Definition KVS_addOrUpdate {KVS : kvsLayout} (g : Locality) : Sealable :=
    SCap RO g b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr.

  (* Meta information about read entry point *)
  Definition kvs_read_nargs : nat := 2.
  Definition kvs_read_pcc_off := (length_kvs_imports + length kvs_addOrUpdate_instrs).
  Definition kvs_read_pcc_addr {KVS : kvsLayout} := (KVS_pcc_b ^+ kvs_read_pcc_off)%a.
  Definition kvs_exp_tbl_entry_read :=
    WInt (encode_entry_point kvs_read_nargs kvs_read_pcc_off).
  Definition kvs_read_exp_tbl_off : nat := 3.
  Definition kvs_read_exp_tbl_addr {KVS : kvsLayout} : Addr := (b_kvs_exp_tbl ^+ kvs_read_exp_tbl_off)%a.
  Definition KVS_read {KVS : kvsLayout} (g : Locality) : Sealable :=
    SCap RO g b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr%a.

  (* Meta information about erase entry point *)
  Definition kvs_erase_nargs : nat := 2.
  Definition kvs_erase_pcc_off := (length_kvs_imports + length kvs_addOrUpdate_instrs + length kvs_read_instrs).
  Definition kvs_erase_pcc_addr {KVS : kvsLayout} := (KVS_pcc_b ^+ kvs_erase_pcc_off)%a.
  Definition kvs_exp_tbl_entry_erase :=
    WInt (encode_entry_point kvs_erase_nargs kvs_erase_pcc_off).
  Definition kvs_erase_exp_tbl_off : nat := 4.
  Definition kvs_erase_exp_tbl_addr {KVS : kvsLayout} : Addr := (b_kvs_exp_tbl ^+ kvs_erase_exp_tbl_off)%a.
  Definition KVS_erase {KVS : kvsLayout} (g : Locality) : Sealable :=
    SCap RO g b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr%a.

  (* Export table of KVS service *)
  Definition kvs_export_table_entries : list Word :=
    [ kvs_exp_tbl_entry_addOrUpdate;
      kvs_exp_tbl_entry_read;
      kvs_exp_tbl_entry_erase
    ].


  Definition kvs_service_unsealing_key {KVS : kvsLayout} :=
    WSealRange (false, true) Global KVS_OTYPE (KVS_OTYPE^+1)%ot KVS_OTYPE.
  Definition kvs_imports {KVS : kvsLayout} (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType) :=
    kvs_imports_pre b_switcher e_switcher a_cc_switcher KVS_OTYPE ot_switcher.

  Definition kvs_full_key (user_key nkey : Z) := Z.lor (user_key ≪ 16) nkey.

  Definition kvs_user_seal_key_scap {KVS : kvsLayout} (g : Locality) (a : Addr) :=
    (SCap RO g a (a ^+ 1)%a a).

  Definition kvs_user_seal_key {KVS : kvsLayout} (g : Locality) (a : Addr) :=
    WSealed KVS_OTYPE (kvs_user_seal_key_scap g a).



  Lemma shiftr_inj (a a' b : Z) :
    a = a' -> (a ≫ b)%Z = (a' ≫ b)%Z.
  Proof. intros ->; done. Qed.
  Lemma land_inj (a b c : Z) :
    b = c -> Z.land a b = Z.land a c.
  Proof. intros ->; done. Qed.

  Lemma Z_testbit_mask_N_true (N : nat) :
    forall n, (0 ≤ n < N)%Z -> Z.testbit (2 ^ N - 1) n = true.
  Proof.
    intros n Hn.
    replace (2 ^ N - 1)%Z with (Z.pred (2 ^ N)) by done.
    rewrite -Z.ones_equiv.
    bitblast.
  Qed.

  Lemma Z_testbit_mask_16_true (n : Z) :
    (0 ≤ n < 16)%Z -> Z.testbit (2 ^ 16 - 1) n = true.
  Proof. eapply (Z_testbit_mask_N_true 16). Qed.

  Lemma Z_testbit_mask_N_false (N : nat) :
    forall n, (0 ≤ n)%Z -> ¬(0 ≤ n < N)%Z -> Z.testbit (2 ^ N - 1) n = false.
  Proof.
    intros n Hn Hn'.
    replace (2 ^ N - 1)%Z with (Z.pred (2 ^ N)) by done.
    rewrite -Z.ones_equiv.
    bitblast.
  Qed.

  Lemma Z_testbit_mask_16_false (n : Z) :
    (0 ≤ n)%Z -> ¬(0 ≤ n < 16)%Z -> Z.testbit (2 ^ 16 - 1) n = false.
  Proof. eapply (Z_testbit_mask_N_false 16). Qed.

  Definition is_uint16 ( z : Z ) : Prop := (UINT16_MIN <= z < UINT16_MAX)%Z.

  Lemma kvs_full_key_inj (uk1 nk1 uk2 nk2 : Z) :
    is_uint16 nk1 ->
    is_uint16 nk2 ->
    (kvs_full_key uk1 nk1 = kvs_full_key uk2 nk2)%Z -> uk1 = uk2 ∧ nk1 = nk2.
  Proof.
    intros Hnk1 Hnk2 Heq.
    unfold kvs_full_key in Heq.
    unfold is_uint16, UINT16_MIN, UINT16_MAX in Hnk1, Hnk2.
    split.
    - assert ( uk1 = (Z.lor (uk1 ≪ 16) nk1) ≫ 16)%Z as -> by bitblast.
      assert ( uk2 = (Z.lor (uk2 ≪ 16) nk2) ≫ 16)%Z as -> by bitblast.
      by apply shiftr_inj.
    - assert ( nk1 = Z.land (2^16 -1) (Z.lor (uk1 ≪ 16) nk1))%Z as ->.
      { bitblast as n.
        - rewrite Z_testbit_mask_16_true; auto; bitblast.
        - rewrite Z_testbit_mask_16_false; auto.
      }
      assert ( nk2 = Z.land (2^16 -1) (Z.lor (uk2 ≪ 16) nk2))%Z as ->.
      { bitblast as n.
        - rewrite Z_testbit_mask_16_true; auto; bitblast.
        - rewrite Z_testbit_mask_16_false; auto.
      }
      by apply land_inj.
  Qed.

End KVS_Service.

Ltac solve_addr_kvs :=
  repeat match goal with
    | H : context [ ASM_SIZEOF_KVS_ENTRY ] |- _ => rewrite /ASM_SIZEOF_KVS_ENTRY in H
    | _ : _ |- context [ ASM_SIZEOF_KVS_ENTRY ] => rewrite /ASM_SIZEOF_KVS_ENTRY
    end
  ; solve_addr.

Tactic Notation "solve_addr" := solve_addr_kvs.
Tactic Notation "solve_addr" "-" hyp_list(Hs) := clear Hs; solve_addr_kvs.
Tactic Notation "solve_addr" "+" hyp_list(Hs) := clear -Hs; solve_addr_kvs.
