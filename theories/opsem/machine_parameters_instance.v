From stdpp Require Import countable.
From griotte Require Import machine_base machine_parameters.

Local Open Scope Z_scope.
Local Transparent MemNum.

Local Definition encode_countable `{Countable A} (x : A) : Z :=
  Z.pos (encode x).

Local Definition decode_countable `{Countable A} (default : A) (z : Z) : A :=
  match z with
  | Z.pos p =>
      match decode p with
      | Some x => x
      | None => default
      end
  | _ => default
  end.

Local Lemma decode_encode_countable `{Countable A} (default x : A) :
  decode_countable default (encode_countable x) = x.
Proof.
  unfold decode_countable, encode_countable.
  rewrite decode_encode.
  reflexivity.
Qed.

Local Lemma encode_countable_inj `{Countable A} :
  Inj (=) (=) (@encode_countable A _ _).
Proof.
  intros x y Hxy.
  apply encode_inj.
  by injection Hxy.
Qed.

Local Definition encode_word_type (w : Word) : Z :=
  match w with
  | WInt _ => 0
  | WCap _ _ _ _ _ _ => 1
  | WSentry _ _ _ _ _ _ => 2
  | WSealRange _ _ _ _ _ _ => 3
  | WSealed _ _ => 4
  end.

Local Definition decode_word_type (z : Z) : Word :=
  match z with
  | 1 => wt_cap
  | 2 => wt_sentry
  | 3 => wt_sealrange
  | 4 => wt_sealed
  | _ => wt_int
  end.

Local Lemma encode_word_type_correct :
  forall w w', match w, w' with
  | WCap _ _ _ _ _ _, WCap _ _ _ _ _ _ =>
      encode_word_type w = encode_word_type w'
  | WSentry _ _ _ _ _ _, WSentry _ _ _ _ _ _ =>
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

Local Definition default_heap_region : HeapRegion := {|
    heap_b := 0%a;
    heap_e := @finz.FinZ MemNum 1%Z eq_refl eq_refl;
    heap_valid := ltac:(solve_addr)
  |}.

Local Definition default_shadow_region : ShadowRegion := {|
    shadow_b := @finz.FinZ MemNum 2%Z eq_refl eq_refl;
    shadow_e := @finz.FinZ MemNum 3%Z eq_refl eq_refl;
    shadow_valid := ltac:(solve_addr)
  |}.

Local Instance machine_parameters_instance : MachineParameters := {|
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
  heap_mixin := default_heap_region;
  shadow_mixin := default_shadow_region;
  heap_shadow_translation_mixin :=
    @affine_heap_shadow_translation default_heap_region default_shadow_region eq_refl;
  heap_shadow_disjoint := ltac:(
    unfold disjoint; intros a Hheap Hshadow;
    rewrite !elem_of_finz_seq_between in Hheap;
    rewrite !elem_of_finz_seq_between in Hshadow;
    unfold finz.le_lt in Hheap; unfold finz.le_lt in Hshadow;
    cbn in Hheap; cbn in Hshadow; lia)
|}.
