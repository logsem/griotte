From Stdlib Require Import ZArith.
From stdpp Require Import base.
From cap_machine Require Import machine_base.
From iris.proofmode Require Import proofmode.

Class MachineParameters := {
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
    decode_encode_word_type_inv :
    forall w, decodeWordType (encodeWordType w) = w;
  }.

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

Global Instance decode_encode_cancel `{MachineParameters}: Cancel (=) decodeInstr encodeInstr.
Proof. intro. eapply decode_encode_instr_inv. Qed.

Global Instance decode_encode_cancelW `{MachineParameters}: Cancel (=) decodeInstrW encodeInstrW.
Proof. intro. eapply decode_encode_instrW_inv. Qed.

Global Instance decode_instr_surj `{MachineParameters}: Surj (=) decodeInstr.
Proof. eapply cancel_surj. Qed.

Global Instance encode_instr_inj `{MachineParameters}: Inj (=) (=) encodeInstr.
Proof. eapply cancel_inj. Qed.

Global Instance decode_instrW_surj `{MachineParameters}: Surj (=) decodeInstrW.
Proof. eapply cancel_surj. Qed.

Global Instance encode_instrw_inj `{MachineParameters}: Inj (=) (=) encodeInstrW.
Proof. eapply cancel_inj. Qed.


Section word_type_encoding.
  Definition wt_cap := WCap (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sentry := WSentry (O LG LM) Global 0%a 0%a 0%a.
  Definition wt_sealrange := WSealRange (false, false) Global 0%ot 0%ot 0%ot.
  Definition wt_sealed := WSealed 0%ot (SCap (O LG LM) Global 0%a 0%a 0%a).
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
  | H: _ |- context G [encodeWordType (WCap ?g ?p ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WCap p g b e a) = encodeWordType wt_cap) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSentry ?g ?p ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSentry p g b e a) = encodeWordType wt_cap) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealRange ?p ?g ?b ?e ?a)] =>
      rewrite (_: encodeWordType (WSealRange p g b e a) = encodeWordType wt_sealrange) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WInt ?n)] =>
      rewrite (_: encodeWordType (WInt n) = encodeWordType wt_int) ; last solve_encodeWordType

  | H: _ |- context G [encodeWordType (WSealed ?o ?s)] =>
      rewrite (_: encodeWordType (WSealed o s) = encodeWordType wt_sealed) ; last solve_encodeWordType
  end.

Lemma encodeWordType_correct_cap `{MachineParameters} : forall p g b e a p' g' b' e' a',
  encodeWordType (WCap p g b e a) = encodeWordType (WCap p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sentry `{MachineParameters} : forall p g b e a p' g' b' e' a',
  encodeWordType (WSentry p g b e a) = encodeWordType (WSentry p' g' b' e' a').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_int `{MachineParameters} : forall z z',
  encodeWordType (WInt z) = encodeWordType (WInt z').
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealrange `{MachineParameters} : forall p g b e a p' g' b' e' a',
  encodeWordType (WSealRange p g b e a) = encodeWordType (WSealRange p' g' b' e' a').
Proof.
  intros; solve_encodeWordType.
Qed.

Lemma encodeWordType_correct_sealed `{MachineParameters} : forall o s o' s',
  encodeWordType (WSealed o s) = encodeWordType (WSealed o' s').
  intros; solve_encodeWordType.
Qed.
