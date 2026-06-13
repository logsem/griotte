From stdpp Require Export numbers.
From machine_utils Require Export finz.
From griotte Require Export stdpp_extra.

(* No longer a coercion in Coq >= 8.14*)
Local Coercion Z.of_nat : nat >-> Z.

(* We assume a fixed set of otypes.

   The exact size of the otype space does not matter, it could be made a
   parameter of the machine.
*)
Definition ONum: Z := 2000000.
Global Opaque ONum.

(* ---------------------------------- OTypes ----------------------------------------*)

(* Number of otypes in our system *)
Notation OType := (finz ONum).
Declare Scope OType_scope.
Delimit Scope OType_scope with ot.

Notation "a1 <= a2 < a3" := (@finz.le_lt ONum a1 a2 a3) : OType_scope.
Notation "a1 <= a2" := (@finz.le ONum a1 a2) : OType_scope.
Notation "a1 <=? a2" := (@finz.leb ONum a1 a2) : OType_scope.
Notation "a1 < a2" := (@finz.lt ONum a1 a2) : OType_scope.
Notation "a1 <? a2" := (@finz.ltb ONum a1 a2) : OType_scope.
Notation "a1 + z" := (@finz.incr ONum a1 z) : OType_scope.
Notation "a ^+ off" := (@finz.incr_default ONum a off) (at level 50) : OType_scope.

Notation z_to_otype := (@finz.of_z ONum).
Notation z_of_ot := (@finz.to_z ONum).

Notation za_ot := (@finz.FinZ ONum 0%Z eq_refl eq_refl).
Notation top_ot := (finz.largest za_ot : OType).
Notation "0" := (za_ot) : OType_scope.

Notation eqb_otype := (λ (a1 a2: OType), Z.eqb a1 a2).
Notation "a1 =? a2" := (eqb_otype a1 a2) : OType_scope.

Notation otype_incr_eq := (finz_incr_eq).

Global Instance otype_inhabited: Inhabited OType := populate (@finz.FinZ ONum 0%Z eq_refl eq_refl).
