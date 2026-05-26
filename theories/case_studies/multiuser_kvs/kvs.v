From cap_machine Require Import machine_parameters assembler.
From cap_machine Require Import bitblast.
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
      unseal rdst rscratch rsealkey;
      geta rdst rdst;
      lshiftl rdst rdst 16;
      lor rdst rdst rkey
    ].

  Definition kvs_getFullKey (rdst rsealkey rkey rscratch : RegName) :=
    Eval compute in assemble (kvs_getFullKey_asm rdst rsealkey rkey rscratch).
  Definition kvs_getFullKey_instrs (rdst rsealkey rkey rscratch : RegName) : list Word :=
    encodeInstrsW (kvs_getFullKey rdst rsealkey rkey rscratch).

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
  Definition kvs_search_asm_pre (rkey ridx rscratch : RegName) : (list asm_code) :=
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
  Definition kvs_search_asm_env (rkey ridx rscratch : RegName) :=
    Eval vm_compute in (compute_asm_code_env (kvs_search_asm_pre rkey ridx rscratch)).2.
  Definition kvs_search_asm (rkey ridx rscratch : RegName) :=
    Eval compute in resolve_labels_macros (kvs_search_asm_pre rkey ridx rscratch)
                      (kvs_search_asm_env rkey ridx rscratch).
  Definition kvs_search (rkey ridx rscratch : RegName) :=
    Eval compute in assemble (kvs_search_asm rkey ridx rscratch).
  Definition kvs_search_instrs (rkey ridx rscratch : RegName) : list Word :=
    encodeInstrsW (kvs_search rkey ridx rscratch).

  Definition UINT16_MIN : Z := 0.
  Definition UINT16_MAX : Z := 2 ^ 16.

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
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [ lea cgp 1 ] ;
      (kvs_search_asm ca0 ct1 ct2) ;
      [
        sub ct1 ct1 (-1)%Z;
        jnz (".addOrUpdate_key_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        #".addOrUpdate_key_not_found";
        (* we need to find an empty slot *)
        mov ctp EMPTY_SLOT;
        jmp (".addOrUpdate_search_empty_slot");
        #".addOrUpdate_key_found";
        (* update the value *)
        lea cgp 1;
        store cgp ca2;
        (* return true *)
        mov ca0 ASM_TRUE;
        mov ca1 0;
        jalr cnull cra;
        #".addOrUpdate_search_empty_slot"
      ] ;
      (kvs_search_asm ctp ct1 ct2) ;
      [
        sub ct1 (-1)%Z ct1;
        jnz (".addOrUpdate_emptyslot_found")%asm ct1;
        (* empty slot found, we know that [cgp] points-to it *)
        #".addOrUpdate_emptyslot_not_found";
        (* no empty slot found, return false *)
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jalr cnull cra;
        #".addOrUpdate_emptyslot_found";
        (* insert the key/value in empty slot *)
        store cgp ca0;
        lea cgp 1;
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
      (kvs_getFullKey_asm ca0 ca0 ca1 ct1)
      (* ca0 contains the full key *)
      ;
      [ lea cgp 1 ] ;
      (kvs_search_asm ca0 ct1 ct2) ;
      [
        sub ct1 ct1 (-1)%Z;
        jnz (".read_key_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        #".read_key_not_found";
        (* no empty slot found, return false *)
        mov ca0 ASM_FALSE;
        mov ca1 0;
        jmp (".read_key_ret")%asm;
        #".read_key_found";
        (* read the value *)
        lea cgp 1;
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
        jnz (".erase_key_found")%asm ct1;
        (* key was found, we know that [cgp] points-to it *)
        (* return void *)
        #".erase_key_not_found";
        jmp (".erase_return");
        #".erase_key_found";
        (* erase the key *)
        store cgp EMPTY_SLOT;
        lea cgp 1;
        store cgp 0;
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

  Definition kvs_imports
    (b_switcher e_switcher a_cc_switcher : Addr) (ot_switcher : OType)
    : list Word :=
    [
      WSentry XSRW_ Local b_switcher e_switcher a_cc_switcher
    ].

  Definition length_kvs_imports := length (kvs_imports za za za za_ot).

  Fixpoint repeat_list `{A : Type} (l : list A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S n => l ++ repeat_list l n
    end.

  Definition kvs_initial_map :=
    repeat_list [WInt EMPTY_SLOT; WInt DEFAULT_VAL] SIZE_MAP.

  Local Definition kvs_service_unsealing_key_pre (KVS_OTYPE : OType) :=
    WSealRange (false, true) Global KVS_OTYPE (KVS_OTYPE^+1)%ot KVS_OTYPE.

  Local Definition kvs_data_pre (KVS_OTYPE : OType) : list Word :=
    (kvs_service_unsealing_key_pre KVS_OTYPE) :: kvs_initial_map.

  Definition length_kvs_data := length (kvs_data_pre za_ot).

  Definition kvs_nb_exports : Z := 3.
  Definition length_kvs_exports_tbl : Z := 2 + kvs_nb_exports.

  Class kvsLayout : Type :=
    mkCmptKvs {
        KVS_OTYPE : OType;
        KVS_OTYPE_size :
        (KVS_OTYPE < KVS_OTYPE ^+ 1)%ot;

        KVS_pcc_b : Addr;
        KVS_pcc_b' : Addr;
        KVS_pcc_e : Addr;
        KVS_size_imports : (KVS_pcc_b + length_kvs_imports)%a = Some KVS_pcc_b';
        KVS_size_code : (KVS_pcc_b' + length kvs_service_instrs)%a = Some KVS_pcc_e;

        KVS_cgp_b : Addr;
        KVS_cgp_e : Addr;
        KVS_size_data : (KVS_cgp_b + length_kvs_data)%a = Some KVS_cgp_e;

        b_kvs_exp_tbl : Addr;
        e_kvs_exp_tbl : Addr;
        kvs_exp_tbl_size : (b_kvs_exp_tbl <= b_kvs_exp_tbl ^+ length_kvs_exports_tbl < e_kvs_exp_tbl)%a
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
  Definition kvs_erase_pcc_off := (length_kvs_imports + length kvs_addOrUpdate_instrs + length kvs_erase_instrs).
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
  Definition kvs_data {KVS : kvsLayout} := kvs_data_pre KVS_OTYPE.

  Definition kvs_full_key (user_key nkey : Z) := Z.lor (user_key ≪ 16) nkey.

  Definition kvs_user_seal_key_scap {KVS : kvsLayout} (z : Z) :=
    (SCap (O LG LM) Global 0%a 0%a (0 ^+ z)%a).

  Definition kvs_user_seal_key {KVS : kvsLayout} (z : Z) :=
    WSealed KVS_OTYPE (kvs_user_seal_key_scap z).



  Lemma shiftr_inj (a a' b : Z) :
    a = a' -> (a ≫ b)%Z = (a' ≫ b)%Z.
  Proof. intros ->; done. Qed.
  Lemma land_inj (a b c : Z) :
    b = c -> Z.land a b = Z.land a c.
  Proof. intros ->; done. Qed.

  (* TODO any better way to prove this? *)
  Lemma Z_testbit_mask_16_true (n : Z) :
    (0 ≤ n < 16)%Z -> Z.testbit (2 ^ 16 - 1) n = true.
  Proof.
    intros H.
    destruct (decide (n = 0)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 1)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 2)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 3)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 4)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 5)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 6)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 7)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 8)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 9)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 10)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 11)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 12)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 13)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 14)%Z); simplify_eq; first bitblast.
    destruct (decide (n = 15)%Z); simplify_eq; first bitblast.
    lia.
  Qed.
  Lemma Z_testbit_mask_16_false (n : Z) :
    (0 ≤ n)%Z -> ¬(0 ≤ n < 16)%Z -> Z.testbit (2 ^ 16 - 1) n = false.
  Proof.
    intros H1 H2.
    apply Z.bits_above_log2; first lia.
    apply Z.log2_lt_pow2; first lia.
    assert (2^16 <= 2^n)%Z by (apply Z.pow_le_mono_r_iff; lia).
    lia.
  Qed.

  Definition is_uint16 ( z : Z ) : Prop := (UINT16_MIN <= z < UINT16_MAX)%Z.
  Definition wf_kvs_full_key (ku kn : Z) : Prop := (0 <= ku)%Z ∧ is_uint16 kn.

  Lemma kvs_full_key_inj (uk1 nk1 uk2 nk2 : Z) :
    wf_kvs_full_key uk1 nk1 ->
    wf_kvs_full_key uk2 nk2 ->
    (kvs_full_key uk1 nk1 = kvs_full_key uk2 nk2)%Z -> uk1 = uk2 ∧ nk1 = nk2.
  Proof.
    intros [Huk1 Hnk1] [Huk2 Hnk2] Heq.
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

  Lemma kvs_full_key_not_empty (ku kn : Z) :
    wf_kvs_full_key ku kn ->
    (kvs_full_key ku kn ≠ EMPTY_SLOT)%Z.
  Proof.
    intros [Hku Hkn].
    unfold EMPTY_SLOT.
    enough (0 <= kvs_full_key ku kn)%Z; first lia.
    unfold kvs_full_key.
    unfold is_uint16, UINT16_MIN, UINT16_MAX in Hkn.
    apply Z.lor_nonneg; split; last lia.
    apply Z.shiftl_nonneg; lia.
  Qed.

End KVS_Service.
