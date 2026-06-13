From griotte Require Export stdpp_extra.
From machine_utils Require Export finz.
From stdpp Require Export numbers.

(* No longer a coercion in Coq >= 8.14*)
Local Coercion Z.of_nat : nat >-> Z.

(* We assume a fixed set of memory addresses.

   The exact size of the address space does not matter, it could be made a
   parameter of the machine.
*)
Definition MemNum: Z := 2000000.
Global Opaque MemNum.

(* -------------------------------- Memory addresses -----------------------------------*)

Notation Addr := (finz MemNum).
Declare Scope Addr_scope.
Delimit Scope Addr_scope with a.

Notation "a1 <= a2 < a3" := (@finz.le_lt MemNum a1 a2 a3) : Addr_scope.
Notation "a1 <= a2" := (@finz.le MemNum a1 a2) : Addr_scope.
Notation "a1 <=? a2" := (@finz.leb MemNum a1 a2) : Addr_scope.
Notation "a1 < a2" := (@finz.lt MemNum a1 a2) : Addr_scope.
Notation "a1 <? a2" := (@finz.ltb MemNum a1 a2) : Addr_scope.
Notation "a1 + z" := (@finz.incr MemNum a1 z) : Addr_scope.
Notation "a ^+ off" := (@finz.incr_default MemNum a off) (at level 50) : Addr_scope.

Notation z_to_addr := (@finz.of_z MemNum).
Notation z_of := (@finz.to_z MemNum).

Notation za := (@finz.FinZ MemNum 0%Z eq_refl eq_refl).
Notation top := (finz.largest za : Addr).
Notation "0" := (za) : Addr_scope.

Notation eqb_addr := (λ (a1 a2: Addr), Z.eqb a1 a2).
Notation "a1 =? a2" := (eqb_addr a1 a2) : Addr_scope.

Notation addr_incr_eq := (finz_incr_eq).

Global Open Scope general_if_scope.

Global Instance addr_inhabited: Inhabited Addr := populate (@finz.FinZ MemNum 0%Z eq_refl eq_refl).
