From stdpp Require Import countable.
From griotte Require Import machine_base machine_parameters.

#[local] Open Scope Z_scope.
#[local] Transparent MemNum.

#[local] Definition encode_countable `{Countable A} (x : A) : Z :=
  Z.pos (encode x).

#[local] Definition decode_countable `{Countable A} (default : A) (z : Z) : A :=
  match z with
  | Z.pos p =>
      match decode p with
      | Some x => x
      | None => default
      end
  | _ => default
  end.

#[local] Lemma decode_encode_countable `{Countable A} (default x : A) :
  decode_countable default (encode_countable x) = x.
Proof.
  unfold decode_countable, encode_countable.
  rewrite decode_encode.
  reflexivity.
Qed.

#[local] Lemma encode_countable_inj `{Countable A} :
  Inj (=) (=) (@encode_countable A _ _).
Proof.
  intros x y Hxy.
  apply encode_inj.
  by injection Hxy.
Qed.

#[local] Definition encode_word_type (w : Word) : Z :=
  match w with
  | WInt _ => 0
  | WCap _ _ _ _ _ _ => 1
  | WSentry _ _ _ _ _ _ _ => 2
  | WSealRange _ _ _ _ _ _ => 3
  | WSealed _ _ => 4
  end.

#[local] Definition decode_word_type (z : Z) : Word :=
  match z with
  | 1 => wt_cap
  | 2 => wt_sentry
  | 3 => wt_sealrange
  | 4 => wt_sealed
  | _ => wt_int
  end.

#[local] Lemma encode_word_type_correct :
  forall w w', match w, w' with
  | WCap _ _ _ _ _ _, WCap _ _ _ _ _ _ =>
      encode_word_type w = encode_word_type w'
  | WSentry _ _ _ _ _ _ _, WSentry _ _ _ _ _ _ _ =>
      encode_word_type w = encode_word_type w'
  | WSealRange _ _ _ _ _ _, WSealRange _ _ _ _ _ _ =>
      encode_word_type w = encode_word_type w'
  | WSealed _ _, WSealed _ _ =>
      encode_word_type w = encode_word_type w'
  | WInt _, WInt _ =>
      encode_word_type w = encode_word_type w'
  | _, _ => encode_word_type w <> encode_word_type w'
  end.
Proof. intros w w'. destruct_word w; destruct_word w'; done. Qed.

#[local] Definition encode_alloc_status (s : AllocStatus) : Z :=
  match s with ShadowLive => 0 | ShadowQuarantined => 1 end.

#[local] Definition decode_alloc_status (z : Z) : AllocStatus :=
  if Z.eqb z 0 then ShadowLive else ShadowQuarantined.

#[local] Lemma decode_encode_alloc_status s :
  decode_alloc_status (encode_alloc_status s) = s.
Proof. by destruct s. Qed.

#[local] Definition default_heap_region : HeapRegion := {|
    heap_b := 0%a;
    heap_e := @finz.FinZ MemNum 1%Z eq_refl eq_refl;
    heap_valid := ltac:(solve_addr)
  |}.

#[local] Definition default_shadow_region : ShadowRegion := {|
    shadow_b := @finz.FinZ MemNum 2%Z eq_refl eq_refl;
    shadow_e := @finz.FinZ MemNum 3%Z eq_refl eq_refl;
    shadow_valid := ltac:(solve_addr)
  |}.

#[local] Definition default_revoker_region : RevokerRegion := {|
    revoker_addr := @finz.FinZ MemNum 4%Z eq_refl eq_refl
  |}.

(** CHERIoT's [CauseCode] values ([sdk/include/cheri.h]). *)
#[local] Definition CauseCode_BoundsViolation : Z := 0x01.
#[local] Definition CauseCode_TagViolation : Z := 0x02.
#[local] Definition CauseCode_SealViolation : Z := 0x03.
#[local] Definition CauseCode_PermitExecuteViolation : Z := 0x11.
#[local] Definition CauseCode_PermitLoadViolation : Z := 0x12.
#[local] Definition CauseCode_PermitStoreViolation : Z := 0x13.
#[local] Definition CauseCode_PermitAccessSystemRegistersViolation : Z := 0x18.

(** CHERIoT's [RegisterNumber] values of the PC and the special capability
    registers ([sdk/include/cheri.h]); a general register is numbered by its
    RISC-V index. *)
#[local] Definition RegisterNumber_PCC : Z := 0x20.
#[local] Definition RegisterNumber_MTCC : Z := 0x3c.
#[local] Definition RegisterNumber_MTDC : Z := 0x3d.
#[local] Definition RegisterNumber_MEPCC : Z := 0x3f.

(** cheriot-sail's mtval of a CHERI fault: the cause code in the low bits,
    then the register number ([extract_cheri_mtval], [cheri.hh]). *)
#[local] Definition cheriot_mtval_code_width : Z := 5.
#[local] Definition cheriot_mtval_reg_width : Z := 6.

#[local] Definition cheriot_cause_code_num (c : cheri_cause_code) : Z :=
  match c with
  | BoundsViolation => CauseCode_BoundsViolation
  | TagViolation => CauseCode_TagViolation
  | SealViolation => CauseCode_SealViolation
  | PermitExecuteViolation => CauseCode_PermitExecuteViolation
  | PermitLoadViolation => CauseCode_PermitLoadViolation
  | PermitStoreViolation => CauseCode_PermitStoreViolation
  | PermitAccessSystemRegistersViolation => CauseCode_PermitAccessSystemRegistersViolation
  end.

#[local] Definition cheriot_reg_num (r : cheri_reg) : Z :=
  match r with
  | CheriGPR r => reg_index r
  | CheriPCC => RegisterNumber_PCC
  | CheriMTCC => RegisterNumber_MTCC
  | CheriMTDC => RegisterNumber_MTDC
  | CheriMEPCC => RegisterNumber_MEPCC
  end.

#[local] Definition cheriot_encode_mtval (c : cheri_cause_code) (r : cheri_reg) : Z :=
  cheriot_reg_num r * 2 ^ cheriot_mtval_code_width + cheriot_cause_code_num c.

#[local] Lemma cheriot_cause_code_num_range c :
  0 ≤ cheriot_cause_code_num c < 2 ^ cheriot_mtval_code_width.
Proof. destruct c; vm_compute; split; congruence. Qed.

#[local] Lemma cheriot_reg_num_range r :
  0 ≤ cheriot_reg_num r < 2 ^ cheriot_mtval_reg_width.
Proof.
  destruct r as [r| | | |]; try (vm_compute; split; congruence).
  pose proof (reg_index_range r) as Hr. rewrite /RegNum in Hr.
  rewrite /cheriot_reg_num /cheriot_mtval_reg_width. lia.
Qed.

#[local] Lemma cheriot_cause_code_num_inj : Inj (=) (=) cheriot_cause_code_num.
Proof. intros [] []; vm_compute; congruence. Qed.

#[local] Lemma cheriot_reg_num_inj : Inj (=) (=) cheriot_reg_num.
Proof.
  intros [r| | | |] [r'| | | |]; try (vm_compute; congruence);
    rewrite /cheriot_reg_num /RegisterNumber_PCC /RegisterNumber_MTCC
      /RegisterNumber_MTDC /RegisterNumber_MEPCC;
    [by intros ->%(inj reg_index) | ..];
    first [pose proof (reg_index_range r) as Hr | pose proof (reg_index_range r') as Hr];
    rewrite /RegNum in Hr; lia.
Qed.

#[local] Lemma cheriot_encode_mtval_code c r :
  Z.land (cheriot_encode_mtval c r) (Z.ones cheriot_mtval_code_width) = cheriot_cause_code_num c.
Proof.
  pose proof (cheriot_cause_code_num_range c).
  rewrite Z.land_ones; last done.
  rewrite /cheriot_encode_mtval Z.add_comm Z.mod_add; last done.
  by apply Z.mod_small.
Qed.

#[local] Lemma cheriot_encode_mtval_reg c r :
  Z.land (Z.shiftr (cheriot_encode_mtval c r) cheriot_mtval_code_width)
    (Z.ones cheriot_mtval_reg_width) = cheriot_reg_num r.
Proof.
  pose proof (cheriot_cause_code_num_range c). pose proof (cheriot_reg_num_range r).
  rewrite Z.land_ones; last done. rewrite Z.shiftr_div_pow2; last done.
  rewrite /cheriot_encode_mtval Z.div_add_l; last done.
  rewrite Z.div_small; last done. rewrite Z.add_0_r. by apply Z.mod_small.
Qed.

(** CHERIoT's encoding of mtval. *)
#[local] Definition cheriot_mtval_encoding : MtvalEncoding := {|
  cause_code_num := cheriot_cause_code_num;
  cause_code_num_inj := cheriot_cause_code_num_inj;
  cheri_reg_num := cheriot_reg_num;
  cheri_reg_num_inj := cheriot_reg_num_inj;
  cheri_reg_num_gpr r := eq_refl;
  MTVAL_CODE_MASK := Z.ones cheriot_mtval_code_width;
  MTVAL_REG_SHIFT := cheriot_mtval_code_width;
  MTVAL_REG_MASK := Z.ones cheriot_mtval_reg_width;
  encode_mtval := cheriot_encode_mtval;
  encode_mtval_code := cheriot_encode_mtval_code;
  encode_mtval_reg := cheriot_encode_mtval_reg
|}.

#[local] Instance machine_parameters_instance : MachineParameters := {|
  instruction_encoding_mixin := {|
    decodeInstr := decode_countable Fail;
    encodeInstr := encode_countable;
    decode_encode_instr_inv := decode_encode_countable Fail
  |};
  permission_encoding_mixin := {|
    encodePerm := encode_countable;
    encodePerm_inj := encode_countable_inj;
    decodePerm := decode_countable (O LG LM);

    encodeLoc := encode_countable;
    encodeLoc_inj := encode_countable_inj;

    decodePermPair := decode_countable ((O LG LM), Local);
    encodePermPair := encode_countable;
    decode_encode_permPair_inv := decode_encode_countable ((O LG LM), Local);

    encodeSealPerms := encode_countable;
    encodeSealPerms_inj := encode_countable_inj;
    decodeSealPerms := decode_countable (false, false);
    decode_encode_seal_perms_inv := decode_encode_countable (false, false);

    decodeSealPermPair := decode_countable ((false, false), Local);
    encodeSealPermPair := encode_countable;
    decode_encode_SealPermPair_inv :=
      decode_encode_countable ((false, false), Local)
  |};
  word_encoding_mixin := {|
    encodeWordType := encode_word_type;
    decodeWordType := decode_word_type;
    encodeWordType_correct := encode_word_type_correct
  |};
  encodeAllocStatus := encode_alloc_status;
  decodeAllocStatus := decode_alloc_status;
  decode_encode_alloc_status_inv := decode_encode_alloc_status;
  heap_mixin := default_heap_region;
  shadow_mixin := default_shadow_region;
  heap_shadow_translation_mixin :=
    @affine_heap_shadow_translation default_heap_region default_shadow_region eq_refl;
  heap_shadow_disjoint := ltac:(
    unfold disjoint; intros a Hheap Hshadow;
    rewrite !elem_of_finz_seq_between in Hheap;
    rewrite !elem_of_finz_seq_between in Hshadow;
    unfold finz.le_lt in Hheap; unfold finz.le_lt in Hshadow;
    cbn in Hheap; cbn in Hshadow; lia);
  revoker_mixin := default_revoker_region;
  revoker_not_heap := eq_refl;
  revoker_not_shadow := eq_refl;
  mtval_encoding_mixin := cheriot_mtval_encoding
|}.
