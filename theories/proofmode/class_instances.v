From Stdlib Require Import ZArith Lia ssreflect.
From stdpp Require Import base.
From griotte Require Import machine_base machine_parameters classes logical_words.
From machine_utils Require Export class_instances.

Instance DecodeInstr_encode `{MachineParameters} (i: instr) :
  DecodeInstr (encodeInstrW i) i.
Proof. apply decode_encode_instrW_inv. Qed.


(* The instruction word of a logical word in normal form. *)
Instance DecodeInstr_lw `{MachineParameters} (w : Word) π (i: instr) :
  DecodeInstr w i → DecodeInstr (lw (w @@? π)) i.
Proof. done. Qed.
