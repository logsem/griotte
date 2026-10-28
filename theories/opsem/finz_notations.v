From stdpp Require Import numbers.
From machine_utils Require Export finz.

(** Offsets of addresses and otypes, outside any scope: [a ^+ 1] needs no
    [%a]. Same levels as machine_utils' [finz_scope] copies. *)
Notation "a ^+ off" := (finz.incr_default a off%Z) (at level 50).
Notation "a ^- off" := (finz.incr_default a (-off)%Z) (at level 51).

(** Print offsets with the notations above, not with machine_utils'
    [finz_scope] copies (which print as [(a ^+ 1)%f]). Files that re-export
    [finz] re-export this file after it, so that the effect survives. *)
Disable Notation "_ ^+ _" (only printing) : finz_scope.
Disable Notation "_ ^- _" (only printing) : finz_scope.
