From griotte Require Import machine_base.
From griotte Require Export trap_fault heap_layout mmio_shadow mmio_revoker mmio.

Class InstructionEncoding := {
    decodeInstr : Z → instr;
    encodeInstr : instr → Z;

    decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;
  }.

Class PermissionEncoding := {
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
  }.

Class WordEncoding := {
    encodeWordType : Word -> Z;
    decodeWordType : Z -> Word;
    encodeWordType_correct :
    forall w w', match w,w' with
            | WCap _ _ _ _ _ _, WCap _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSentry _ _ _ _ _ _ _, WSentry _ _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealRange _ _ _ _ _ _, WSealRange _ _ _ _ _ _ => encodeWordType w = encodeWordType w'
            | WSealed _ _, WSealed _ _ => encodeWordType w = encodeWordType w'
            | WInt _, WInt _ => encodeWordType w = encodeWordType w'
            | _, _ => encodeWordType w <> encodeWordType w'
            end;
  }.

(** The encoding of the value that trap entry writes to mtval for a CHERI
    fault: a cause code and a register number, packed in two fields that a
    mask, and a shift then a mask, extract. The number of a general register
    is its RISC-V index. *)
Class MtvalEncoding := {
    cause_code_num : cheri_cause_code → Z;
    cause_code_num_inj :: Inj (=) (=) cause_code_num;
    cheri_reg_num : cheri_reg → Z;
    cheri_reg_num_inj :: Inj (=) (=) cheri_reg_num;
    cheri_reg_num_gpr r : cheri_reg_num (CheriGPR r) = reg_index r;
    MTVAL_CODE_MASK : Z;
    MTVAL_REG_SHIFT : Z;
    MTVAL_REG_MASK : Z;
    encode_mtval : cheri_cause_code → cheri_reg → Z;
    encode_mtval_code c r :
      Z.land (encode_mtval c r) MTVAL_CODE_MASK = cause_code_num c;
    encode_mtval_reg c r :
      Z.land (Z.shiftr (encode_mtval c r) MTVAL_REG_SHIFT) MTVAL_REG_MASK = cheri_reg_num r;
  }.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

Section mtval_encoding.
  Context `{MtvalEncoding}.

  (** The fields of an mtval, as code computes them. *)
  Definition mtval_code_field (z : Z) : Z := Z.land z MTVAL_CODE_MASK.
  Definition mtval_reg_field (z : Z) : Z :=
    Z.land (Z.shiftr z MTVAL_REG_SHIFT) MTVAL_REG_MASK.

  (** The decoders: [None] is CHERIoT's [Invalid]. *)
  Definition mtval_cause_code (z : Z) : option cheri_cause_code :=
    finite_preimage cause_code_num (mtval_code_field z).
  Definition mtval_register (z : Z) : option cheri_reg :=
    finite_preimage cheri_reg_num (mtval_reg_field z).

  Lemma mtval_code_field_encode c r : mtval_code_field (encode_mtval c r) = cause_code_num c.
  Proof. apply encode_mtval_code. Qed.

  Lemma mtval_reg_field_encode c r : mtval_reg_field (encode_mtval c r) = cheri_reg_num r.
  Proof. apply encode_mtval_reg. Qed.

  Lemma mtval_cause_code_encode c r : mtval_cause_code (encode_mtval c r) = Some c.
  Proof. by rewrite /mtval_cause_code mtval_code_field_encode finite_preimage_inj. Qed.

  Lemma mtval_register_encode c r : mtval_register (encode_mtval c r) = Some r.
  Proof. by rewrite /mtval_register mtval_reg_field_encode finite_preimage_inj. Qed.

  #[global] Instance encode_mtval_inj : Inj2 (=) (=) (=) encode_mtval.
  Proof.
    intros c r c' r' Heq. split.
    - apply (inj cause_code_num).
      by rewrite -(encode_mtval_code c r) -(encode_mtval_code c' r') Heq.
    - apply (inj cheri_reg_num).
      by rewrite -(encode_mtval_reg c r) -(encode_mtval_reg c' r') Heq.
  Qed.

  (** The PC and the special capability registers have numbers outside those
      of the general registers. *)
  Lemma cheri_reg_num_special s :
    (∀ r, s ≠ CheriGPR r) → ¬ (0 ≤ cheri_reg_num s ≤ Z.of_nat RegNum)%Z.
  Proof.
    intros Hs Hrange. destruct (reg_index_surj _ Hrange) as [r Hr].
    apply (Hs r), (inj cheri_reg_num). by rewrite cheri_reg_num_gpr Hr.
  Qed.
End mtval_encoding.

Class MachineParameters := {
    instruction_encoding_mixin :: InstructionEncoding;
    permission_encoding_mixin :: PermissionEncoding;
    word_encoding_mixin :: WordEncoding;
    (* The encoding of allocation statuses, for the shadow region *)
    alloc_status_encoding_mixin :: AllocStatusEncoding;
    (* Machine parameters for the heap and the shadow regions *)
    heap_mixin :: HeapRegion;
    shadow_mixin :: ShadowRegion;
    heap_shadow_translation_mixin :: HeapShadowTranslation;
    heap_shadow_disjoint :
    (finz.seq_between heap_b heap_e) ##
      (finz.seq_between shadow_b shadow_e);
    (* Machine parameter for the revoker *)
    revoker_mixin :: RevokerRegion;
    revoker_not_heap : withinBounds heap_b heap_e revoker_addr = false;
    revoker_not_shadow : withinBounds shadow_b shadow_e revoker_addr = false;
    (* The encoding of mtval for a CHERI fault *)
    mtval_encoding_mixin :: MtvalEncoding;
  }.

Lemma revoker_not_heap_address `{MachineParameters} :
  is_heap_address revoker_addr = false.
Proof. exact revoker_not_heap. Qed.

Lemma revoker_not_shadow_address `{MachineParameters} :
  is_shadow_address revoker_addr = false.
Proof. exact revoker_not_shadow. Qed.

(* Lift the encoding / decoding between Z and instructions on Words: simplify
   fail on capabilities. *)

Definition decodeInstrW `{MachineParameters} : Word → instr :=
  fun w =>
    match w with
    | WInt z => decodeInstr z
    | _ => Fail
    end.

Definition encodeInstrW `{MachineParameters} : instr → Word :=
  fun i => WInt (encodeInstr i).

Lemma decode_encode_instrW_inv `{MachineParameters} (i: instr):
  decodeInstrW (encodeInstrW i) = i.
Proof. apply decode_encode_instr_inv. Qed.

Definition encodeInstrsW `{MachineParameters} : list instr → list Word :=
  map encodeInstrW.

#[global] Instance decode_encode_cancel `{MachineParameters}: Cancel (=) decodeInstr encodeInstr.
Proof. intro. eapply decode_encode_instr_inv. Qed.

#[global] Instance decode_encode_cancelW `{MachineParameters}: Cancel (=) decodeInstrW encodeInstrW.
Proof. intro. eapply decode_encode_instrW_inv. Qed.

#[global] Instance decode_instr_surj `{MachineParameters}: Surj (=) decodeInstr.
Proof. eapply cancel_surj. Qed.

#[global] Instance encode_instr_inj `{MachineParameters}: Inj (=) (=) encodeInstr.
Proof. eapply cancel_inj. Qed.

#[global] Instance decode_instrW_surj `{MachineParameters}: Surj (=) decodeInstrW.
Proof. eapply cancel_surj. Qed.

#[global] Instance encode_instrw_inj `{MachineParameters}: Inj (=) (=) encodeInstrW.
Proof. eapply cancel_inj. Qed.

(** Integer encoding of the permission field of a word (see [get_p]). *)
Definition encodePermSum `{MachineParameters} (p : Perm + SealPerms) : Z :=
  match p with
  | inl p => encodePerm p
  | inr p => encodeSealPerms p
  end.

Section word_type_encoding.
  Definition wt_cap := Cap (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sentry := Sentry Inherit (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sealrange := SealRange (false, false) Global 0%ot 0%ot 0%ot.
  Definition wt_sealed := Sealed 0%ot (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_int := WInt 0.
End word_type_encoding.

Ltac solve_encodeWordType :=
  match goal with
  | H: _ |- encodeWordType ?x = encodeWordType ?y =>
      try reflexivity
      ; pose proof (encodeWordType_correct x y) as Heq
      ; unfold wt_cap, wt_sentry, wt_int, wt_sealrange, wt_cap; simpl in Heq
      ; auto
  end.

Ltac simpl_encodeWordType :=
  match goal with
  | H: _ |- context G [encodeWordType (WCap ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WCap t p g b e a) = encodeWordType wt_cap) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSentry ?k ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSentry k t p g b e a) = encodeWordType wt_sentry) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealRange ?t ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSealRange t p g b e a) = encodeWordType wt_sealrange) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WInt ?n)] =>
      rewrite (_: encodeWordType (WInt n) = encodeWordType wt_int) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealed ?o ?s)] =>
      rewrite (_: encodeWordType (WSealed o s) = encodeWordType wt_sealed) ; last solve_encodeWordType
  end.

Lemma encodeWordType_correct_cap `{MachineParameters} : forall t p g b e a t' p' g' b' e' a',
  encodeWordType (WCap t p g b e a) = encodeWordType (WCap t' p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sentry `{MachineParameters} : forall k t p g b e a k' t' p' g' b' e' a',
  encodeWordType (WSentry k t p g b e a) = encodeWordType (WSentry k' t' p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_int `{MachineParameters} : forall z z',
  encodeWordType (WInt z) = encodeWordType (WInt z').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealrange `{MachineParameters} : forall t p g b e a t' p' g' b' e' a',
  encodeWordType (WSealRange t p g b e a) = encodeWordType (WSealRange t' p' g' b' e' a').
Proof.
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeWordType (WSealed o s) = encodeWordType (WSealed o' s').
  intros; solve_encodeWordType.
Qed.
