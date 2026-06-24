From griotte Require Import machine_base machine_parameters bitblast.
Local Open Scope Z_scope.

Definition _PERM_ENC      : Z := 0. (* 0b000 *)
Definition _SEAL_PERM_ENC : Z := 1. (* 0b001 *)
Definition _LOCALITY_ENC  : Z := 2. (* 0b010 *)
Definition _WTYPE_ENC     : Z := 3. (* 0b011 *)
Definition _PERM_LOC_ENC  : Z := 4. (* 0b100 *)
Definition _SEAL_LOC_ENC  : Z := 5. (* 0b101 *)


Definition encode_const (typ cst : Z) : Z :=
Z.lor (cst ≪ 3) typ.

Definition decode_const (i : Z) : (Z*Z) :=
  let b0 := Z.testbit i 0 in
  let b1 := Z.testbit i 1 in
  let b2 := Z.testbit i 2 in
  let typ :=
    match b2,b1,b0 with
    | false, false, false => 0
    | false, false, true => 1
    | false, true, false => 2
    | false, true, true => 3
    | true, false, false => 4
    | true, false, true => 5
    | true, true, false => 6
    | true, true, true => 7
    end
  in
  (typ, (i ≫ 3) ).

Definition _WINT_ENC   : Z := 0. (* 0b000 *)
Definition _SCAP_ENC   : Z := 1. (* 0b001 *)
Definition _SRANGE_ENC : Z := 2. (* 0b010 *)
Definition _SEALED_ENC : Z := 3. (* 0b011 *)
Definition _SENTRY_ENC : Z := 4. (* 0b100 *)

Definition wtype_encoding (w : Word) : Z :=
  match w with
  | WInt _ => _WINT_ENC
  | WSealable (SCap _ _ _ _ _) => _SCAP_ENC
  | WSealable (SSealRange _ _ _ _ _) => _SRANGE_ENC
  | WSentry _ _ _ _ _ => _SENTRY_ENC
  | WSealed _ _ => _SEALED_ENC
  end.

Definition encode_wtype (w : Word) : Z :=
  encode_const _WTYPE_ENC (wtype_encoding w).


Definition _LOCAL_ENC  : Z := 0.
Definition _GLOBAL_ENC : Z := 1.

Definition locality_encoding ( g : Locality ) :=
  match g with
  | Local => _LOCAL_ENC
  | Global => _GLOBAL_ENC
  end.

Definition encode_locality ( g : Locality ) :=
  encode_const _LOCALITY_ENC (locality_encoding g).

Definition locality_decoding ( i : Z ) : Locality :=
  let b0 := Z.testbit i 0 in
  match b0 with
  | false => Local
  | true => Global
  end.

Definition decode_locality ( i : Z) : Locality :=
  let '(typ, payload) := decode_const i in
  if ( typ =? _WTYPE_ENC )
  then locality_decoding payload
  else Local (* default locality *).


Definition _ORX_ENC : Z := 0. (* 0b00 *)
Definition _R_ENC   : Z := 1. (* 0b01 *)
Definition _X_ENC   : Z := 2. (* 0b10 *)
Definition _XSR_ENC : Z := 3. (* 0b11 *)

Definition rxperm_encoding ( rx : RXperm ) :=
  match rx with
  | Orx => _ORX_ENC
  | R => _R_ENC
  | X => _X_ENC
  | XSR => _XSR_ENC
  end
.

Definition _OW_ENC : Z := 0. (* 0b00 *)
Definition _W_ENC  : Z := 1. (* 0b01 *)
Definition _WL_ENC : Z := 2. (* 0b10 *)

Definition wperm_encoding ( w : Wperm ) :=
  match w with
  | Ow => _OW_ENC
  | W=> _W_ENC
  | WL => _WL_ENC
  end
.

Definition _DL_ENC : Z := 0. (* 0b00 *)
Definition _LG_ENC : Z := 1. (* 0b01 *)

Definition dlperm_encoding ( dl : DLperm ) :=
  match dl with
  | DL => _DL_ENC
  | LG => _LG_ENC
  end
.

Definition _DRO_ENC : Z := 0. (* 0b00 *)
Definition _LM_ENC  : Z := 1. (* 0b01 *)

Definition droperm_encoding ( dro : DROperm ) :=
  match dro with
  | DRO => _DRO_ENC
  | LM => _LM_ENC
  end
.

Definition perm_encoding ( p : Perm ) : Z :=
  match p with
    | BPerm rx w dl dro =>
        let enc_dro  := ( (droperm_encoding dro) ≪ 0) in
        let enc_dl := ( (dlperm_encoding dl) ≪ 1) in
        let enc_w := ( (wperm_encoding w) ≪ 2) in
        let enc_rx := ( (rxperm_encoding rx) ≪ 4) in
        Z.lor enc_rx ( Z.lor enc_w ( Z.lor enc_dl enc_dro  ) )
  end.

Definition perm_decoding (i : Z) : Perm :=
  let b5 := Z.testbit i 5 in
  let b4 := Z.testbit i 4 in
  let b3 := Z.testbit i 3 in
  let b2 := Z.testbit i 2 in
  let b1 := Z.testbit i 1 in
  let b0 := Z.testbit i 0 in
  let rx :=
    match b5, b4 with
    | false, false => Orx
    | false, true => R
    | true, false => X
    | true, true => XSR
    end
  in
  let w :=
    match b3, b2 with
    | false, false => Ow
    | false, true => W
    | true, false => WL
    | true, true => Ow (* default Wperm *)
    end
  in
  let dl :=
    match b1 with
    | false => DL
    | true => LG
    end
  in
  let dro :=
    match b0 with
    | false => DRO
    | true => LM
    end
  in
  BPerm rx w dl dro.


Definition encode_perm (p : Perm) : Z :=
  encode_const _PERM_ENC (perm_encoding p).

Definition decode_perm (i : Z) : Perm :=
  let '(typ, payload) := decode_const i in
  if ( typ =? _PERM_ENC )
  then perm_decoding payload
  else (BPerm Orx Ow DL DRO). (* default permission *)


Definition seal_perm_encoding ( sp : SealPerms ) : Z :=
  match sp with
  | (false, false) => 0
  | (false, true) => 1
  | (true, false) => 2
  | (true, true) => 3
  end.

Definition seal_perm_decoding (i : Z ) : SealPerms :=
  let b1 := Z.testbit i 1 in
  let b0 := Z.testbit i 0 in
  (b1, b0).


Definition encode_seal_perm (sp : SealPerms) : Z :=
  encode_const _SEAL_PERM_ENC (seal_perm_encoding sp).

Definition decode_seal_perm (i : Z.t) : SealPerms :=
  let '(typ, payload) := decode_const i in
  if ( typ =? _SEAL_PERM_ENC )
  then seal_perm_decoding payload
  else (false,false). (* default seal permission *)

(** Permission-locality encoding *)
Definition perm_loc_pair_encoding (p : Perm) (g : Locality) : Z :=
  let size_perm := 6 in
  let encoded_g := ( (locality_encoding g) ≪ size_perm ) in
  let encoded_p := perm_encoding p in
  Z.lor encoded_g encoded_p.

Definition encode_perm_loc_pair (p : Perm) (g : Locality) : Z :=
  encode_const _PERM_LOC_ENC (perm_loc_pair_encoding p g).

Definition perm_loc_pair_decoding (i : Z) : Perm * Locality :=
  let size_perm := 6 in
  let encoded_g := (i ≫ size_perm) in
  let encoded_p := Z.land i (Z.pred (2^(size_perm + 1))) in
  (perm_decoding encoded_p, locality_decoding encoded_g).

Definition decode_perm_loc_pair (i : Z) : Perm * Locality :=
  let '(typ, payload) := decode_const i in
  if ( typ =? _PERM_LOC_ENC )
  then perm_loc_pair_decoding payload
  else ( (BPerm Orx Ow DL DRO) , Local). (* default perm-loc *)

(** Sealing Permission-locality encoding *)
Definition seal_perm_loc_pair_encoding (p : SealPerms) (g : Locality) : Z :=
  let size_seal_perm := 2 in
  let encoded_g := ( (locality_encoding g) ≪ size_seal_perm ) in
  let encoded_p := seal_perm_encoding p in
  Z.lor encoded_g encoded_p.

Definition encode_seal_perm_loc_pair (p : SealPerms) (g : Locality) : Z :=
  encode_const _SEAL_LOC_ENC (seal_perm_loc_pair_encoding p g).

Definition seal_perm_loc_pair_decoding (i : Z) : SealPerms * Locality :=
  let size_seal_perm := 2 in
  let encoded_g := (i ≫ size_seal_perm) in
  let encoded_p := Z.land i (Z.pred (2^(size_seal_perm+1))) in
  (seal_perm_decoding encoded_p, locality_decoding encoded_g).

Definition decode_seal_perm_loc_pair (i : Z) : SealPerms * Locality :=
  let '(typ, payload) := decode_const i in
  if ( typ =? _SEAL_LOC_ENC )
  then seal_perm_loc_pair_decoding payload
  else ( (false,false) , Local). (* default sealperm-loc *)




Definition encode_reg (r : RegName) : Z :=
  match r with
  | PC => 0
  | registers.R n _ => (Z.of_nat n) + 1
  end.

Definition decode_reg ( i : Z ) : RegName :=
  if (i =? 0)
  then PC
  else
    match (n_to_regname (Z.to_nat (i-1))) with
    | Some r => r
    | None => PC (* default register *)
    end.

Definition encode_sreg (sr : SRegName) : Z :=
match sr with | MTDC => 0 end.

Definition decode_sreg (i : Z) : SRegName := MTDC.

From Equations Require Import Equations.
From Stdlib Require Import Wellfounded.

Local Close Scope Z_scope.

Program Fixpoint split_int (i : nat) {measure i lt} : nat * nat :=
  match i with
  | 0 => (0, 0)
  | _ =>
      let x1 := Nat.land i 1 in
      let y1 := Nat.land (Nat.div i 2) 1 in
      let '(x2, y2) := split_int (Nat.div i 4) in
      (x1 + 2 * x2, y1 + 2 * y2)
  end.
Next Obligation.
  destruct (Nat.divmod i 3 0 3) eqn:H; cbn.
  opose proof (Nat.divmod_spec i 3 0 3 _) as H'; first lia.
  rewrite H in H'; destruct H' as [? ?].
  lia.
Qed.

Program Fixpoint interleave_int (x y : nat)
  {measure (x + y) lt} : nat :=
  match x, y with
  | 0, 0 => 0
  | _ , _ =>
      let x1 := Nat.land x 1 in
      let y1 := 2 * Nat.land y 1 in
      let x2 := Nat.div x 2 in
      let y2 := Nat.div y 2 in
      x1 + y1 + 4 * interleave_int x2 y2
  end.
Next Obligation.
  destruct (Nat.divmod x 1 0 1) eqn:Hx; cbn.
  opose proof (Nat.divmod_spec x 1 0 1 _) as Hx'; first lia.
  rewrite Hx in Hx'; destruct Hx' as [? ?].
  destruct (Nat.divmod y 1 0 1) eqn:Hy; cbn.
  opose proof (Nat.divmod_spec y 1 0 1 _) as Hy'; first lia.
  rewrite Hy in Hy'; destruct Hy' as [? ?].
  lia.
Qed.
Next Obligation.
  apply (wf_inverse_image _ _ _ (fun p => projT1 p + projT2 p)).
  apply lt_wf.
Qed.
Next Obligation.
  apply lt_wf.
Qed.


Local Open Scope Z_scope.
Definition z_sign (z : Z) : Z :=
  if z <? 0 then -1
  else if z =? 0 then 0
  else 1.

Definition encode_signs (x y : Z) : Z :=
  match z_sign y, z_sign x with
  | -1, -1 => 0
  | -1, 0 | -1, 1 => 2
  | 0, -1 | 1, -1 => 1
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 => 0
  | _, _ => 0 (* unreachable, like OCaml assert false *)
  end.
Definition encode_int_int (x y : Z) : Z :=
  let sign_bits := encode_signs x y in
  let interleaved :=
    Z.of_nat (interleave_int (Z.to_nat (Z.abs x))
                             (Z.to_nat (Z.abs y)))
  in
  sign_bits + 4 * interleaved.


Definition decode_int (i : Z) : Z * Z :=
  let is_x_neg := Z.testbit i 0 in
  let is_y_neg := Z.testbit i 1 in
  let '(x, y) := split_int (Z.to_nat (Z.shiftr i 2)) in
  let xz := Z.of_nat x in
  let yz := Z.of_nat y in
  match is_x_neg, is_y_neg with
  | true, true => (Z.opp xz, Z.opp yz)
  | true, false => (Z.opp xz, yz)
  | false, true => (xz, Z.opp yz)
  | false, false => (xz, yz)
  end.

Definition encode_machine_op (s : instr) : Z :=
  let encode_opcode_args := 
  let ( ^! ) opcode args = Z.(opcode + (args lsl 8)) in
  let const_convert opcode c =
    match c with Register r -> (opcode, encode_reg r) | Const n -> Z.(succ opcode, n)
  in
  let two_const_convert opcode c1 c2 =
    let opc1, c1_enc =
      match c1 with Register r -> (opcode, encode_reg r) | Const i -> Z.(opcode + ~$2, i)
    in
    let opc2, c2_enc = const_convert opc1 c2 in
    (opc2, encode_int_int c1_enc c2_enc)
  in
  match s with
  | Jmp c ->
      (* 0x00, 0x01 *)
      let opc, c_enc = const_convert ~$0x00 c in
      opc ^! c_enc
  | Jnz (r, c) ->
      (* 0x02, 0x03 *)
      let opc, c_enc = const_convert ~$0x02 c in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Jalr (r1, r2) ->
      (* 0x04 *)
      ~$0x04 ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | ReadSR (r, sr) ->
      (* 0x05 *)
      ~$0x05 ^! encode_int_int (encode_reg r) (encode_sreg sr)
  | WriteSR (sr, r) ->
      (* 0x06 *)
      ~$0x06 ^! encode_int_int (encode_sreg sr) (encode_reg r)
  | Move (r, c) ->
      (* 0x07, 0x08 *)
      let opc, c_enc = const_convert ~$0x07 c in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Load (r1, r2) ->
      (* 0x09 *)
      ~$0x09 ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | Store (r, c) ->
      (* 0x0a, 0x0b  *)
      let opc, c_enc = const_convert ~$0x0a c in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Add (r, c1, c2) ->
      (* 0x0c, 0x0d, 0x0e, 0x0f *)
      let opc, c_enc = two_const_convert ~$0x0c c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Sub (r, c1, c2) ->
      (* 0x10, 0x11, 0x12, 0x13 *)
      let opc, c_enc = two_const_convert ~$0x10 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Mul (r, c1, c2) ->
      (* 0x14, 0x15, 0x16, 0x17 *)
      let opc, c_enc = two_const_convert ~$0x14 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Rem (r, c1, c2) ->
      (* 0x18, 0x19, 0x1a, 0x1b *)
      let opc, c_enc = two_const_convert ~$0x18 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Div (r, c1, c2) ->
      (* 0x1c, 0x1d, 0x1e, 0x1f *)
      let opc, c_enc = two_const_convert ~$0x1c c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Lt (r, c1, c2) ->
      (* 0x20, 0x21, 0x22, 0x23 *)
      let opc, c_enc = two_const_convert ~$0x20 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Lea (r, c) ->
      (* 0x24, 0x25 *)
      let opc, c_enc = const_convert ~$0x24 c in
      opc ^! encode_int_int (encode_reg r) c_enc
  | Restrict (r, c) ->
      (* 0x26, 0x27 *)
      let opc, c_enc = const_convert ~$0x26 c in
      opc ^! encode_int_int (encode_reg r) c_enc
  | SubSeg (r, c1, c2) ->
      (* 0x28, 0x29, 0x2a, 0x2b *)
      let opc, c_enc = two_const_convert ~$0x28 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | GetL (r1, r2) -> ~$0x2c ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetB (r1, r2) -> ~$0x2d ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetE (r1, r2) -> ~$0x2e ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetA (r1, r2) -> ~$0x2f ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetP (r1, r2) -> ~$0x30 ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetOType (r1, r2) -> ~$0x31 ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | GetWType (r1, r2) -> ~$0x32 ^! encode_int_int (encode_reg r1) (encode_reg r2)
  | Seal (r1, r2, r3) ->
      ~$0x33 ^! encode_int_int (encode_reg r1) (encode_int_int (encode_reg r2) (encode_reg r3))
  | UnSeal (r1, r2, r3) ->
      ~$0x34 ^! encode_int_int (encode_reg r1) (encode_int_int (encode_reg r2) (encode_reg r3))
  | Fail -> ~$0x35
  | Halt -> ~$0x36
  | LAnd (r, c1, c2) ->
      (* 0x37, 0x38, 0x39, 0x3a *)
      let opc, c_enc = two_const_convert ~$0x37 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | LOr (r, c1, c2) ->
      (* 0x3b, 0x3c, 0x3d, 0x3e *)
      let opc, c_enc = two_const_convert ~$0x3b c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | LShiftL (r, c1, c2) ->
      (* 0x3f, 0x40, 0x41, 0x42 *)
      let opc, c_enc = two_const_convert ~$0x3f c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc
  | LShiftR (r, c1, c2) ->
      (* 0x43, 0x44, 0x45, 0x46 *)
      let opc, c_enc = two_const_convert ~$0x43 c1 c2 in
      opc ^! encode_int_int (encode_reg r) c_enc






Lemma encode_locality_inj : Inj eq eq encode_locality.
Proof. intros l1 l2 Hl; destruct l1, l2; cbn in *; done. Qed.

Lemma encode_perm_inj : Inj eq eq encode_perm.
Proof. intros p1 p2 Hp; destruct p1 as [ [] [] [] [] ], p2 as [ [] [] [] [] ]; cbn in *; done. Qed.

Lemma encode_seal_perm_inj : Inj eq eq encode_seal_perm.
Proof. intros p1 p2 Hp; destruct p1 as [ [] [ ] ], p2 as [ [] [ ] ]; cbn in *; done. Qed.

Lemma decode_encode_perm_loc_inv (p : Perm) (l : Locality) :
    decode_perm_loc_pair (encode_perm_loc_pair p l) = (p, l).
Proof. destruct p as [ [] [] [] [] ], l; cbv; done. Qed.

Lemma decode_encode_seal_perm_loc_inv (p : SealPerms) (l : Locality) :
    decode_seal_perm_loc_pair (encode_seal_perm_loc_pair p l) = (p, l).
Proof. destruct p as [ [] [] ], l; cbv; done. Qed.

Lemma encode_wtype_correct :
  forall w w', match w,w' with
          | WCap _ _ _ _ _, WCap _ _ _ _ _ => encode_wtype w = encode_wtype w'
          | WSentry _ _ _ _ _, WSentry _ _ _ _ _ => encode_wtype w = encode_wtype w'
          | WSealRange _ _ _ _ _, WSealRange _ _ _ _ _ => encode_wtype w = encode_wtype w'
          | WSealed _ _, WSealed _ _ => encode_wtype w = encode_wtype w'
          | WInt _, WInt _ => encode_wtype w = encode_wtype w'
          | _, _ => encode_wtype w <> encode_wtype w'
          end.
Proof. intros w w'; destruct_word w; destruct_word w'; done. Qed.

Local Instance InstanceMachineParameters :=
{
    decodeInstr : Z → instr;
    encodeInstr : instr → Z;

    decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;

    encodePerm : Perm → Z;
    encodePerm_inj : Inj eq eq encodePerm;
    decodePerm : Z → Perm;

    encodeLoc : Locality → Z;
    encodeLoc_inj : Inj eq eq encodeLoc;

    decodePermPair : Z → Perm * Locality;
    encodePermPair : Perm * Locality → Z;

    decode_encode_permPair_inv :
    forall pl, decodePermPair (encodePermPair pl) = pl;

    encodeSealPerms : SealPerms → Z;
    encodeSealPerms_inj : Inj eq eq encodeSealPerms;
    decodeSealPerms : Z → SealPerms;

    decode_encode_seal_perms_inv :
    forall pl, decodeSealPerms (encodeSealPerms pl) = pl;

    decodeSealPermPair : Z → SealPerms * Locality;
    encodeSealPermPair : SealPerms * Locality → Z;

    decode_encode_SealPermPair_inv :
    forall pl, decodeSealPermPair (encodeSealPermPair pl) = pl;

    encodeWordType : Word -> Z;
    decodeWordType : Z -> Word;
    encodeWordType_correct :
    forall w w', match w,w' with
            | WCap _ _ _ _ _, WCap _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSentry _ _ _ _ _, WSentry _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealRange _ _ _ _ _, WSealRange _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealed _ _, WSealed _ _ => encodeWordType w = encodeWordType w'
            | WInt _, WInt _ => encodeWordType w = encodeWordType w'
            | _, _ => encodeWordType w <> encodeWordType w'
            end;
  }.
