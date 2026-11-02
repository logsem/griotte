From griotte Require Import machine_base.

(** The in-memory bit encoding of a capability (Sail's [capToBits]), used
    where a device register receives a capability store. *)
Class CapBitsEncoding := {
    cap_to_bits : Word → Z;
  }.
(* No [Hint Mode]: the class has no parameter, hence no input position. *)

(** The bits of a word stored to a device register: an integer is its own
    bits, any other word its encoding. The tag is not part of the bits:
    Sail's [mem_write_cap] writes it apart, as metadata. *)
Definition word_to_bits `{CapBitsEncoding} (w : Word) : Z :=
  match w with
  | WInt z => z
  | _ => cap_to_bits (clear_tag w)
  end.

Lemma word_to_bits_clear_tag `{CapBitsEncoding} w :
  word_to_bits (clear_tag w) = word_to_bits w.
Proof. destruct w as [z| | |]; [done|..]; by rewrite /word_to_bits clear_tag_idempotent. Qed.
