From Stdlib Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From Stdlib.micromega Require Import ZifyClasses.
From stdpp Require Import gmap fin_maps list.
From Stdlib Require Import ssreflect.
From cap_machine Require Import stdpp_extra.
From machine_utils Require Export finz.

(* No longer a coercion in Coq >= 8.14*)
Local Coercion Z.of_nat : nat >-> Z.

(* We assume a fixed set of registers, and a finite set of memory addresses.

   The exact size of the address space does not matter, it could be made a
   parameter of the machine.
*)

Definition RegNum: nat := 31.
Definition MemNum: Z := 2000000.
Definition ONum: Z := 1000.
Global Opaque MemNum.
Global Opaque ONum.

(* ---------------------------------- Registers ----------------------------------------*)

Inductive RegName: Type :=
| PC
| R (n: nat) (fin: n <=? RegNum = true).

Inductive SRegName : Type :=
| MTDC.

Global Instance reg_eq_dec : EqDecision RegName.
Proof. intros r1 r2.  destruct r1 as [| n fin ],r2 as [|n0 fin0]; [by left | by right | by right |].
       destruct (Nat.eq_dec n n0).
       + subst n0. left.
         assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2) as H.
         { intros b n' m' P1 P2. apply eq_proofs_unicity.
           intros x y; destruct x; destruct y; auto. }
         rewrite (H _ _ _ fin fin0). reflexivity.
       + right. congruence.
Defined.

Lemma reg_eq_sym (r1 r2 : RegName) : r1 ≠ r2 → r2 ≠ r1. Proof. auto. Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  match Nat.le_dec n RegNum with left _ => Some (R n _) | right _ => None end.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
Defined.

Global Instance reg_countable : Countable RegName.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl ()
                               | R n fin => inr n
                               end ;
            decode n := match (decode n) with
                        | Some (inl ()) => Some PC
                        | Some (inr n) => n_to_regname n
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r as [|n fin]; auto.
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (Nat.le_dec n RegNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Nat.leb_le n RegNum) in fin.
Defined.


Global Instance sreg_eq_dec : EqDecision SRegName.
Proof. intros r1 r2; destruct r1,r2; by left. Defined.

Global Instance sreg_countable : Countable SRegName.
Proof.
  refine {| encode r := encode match r with
                               | MTDC => Some ()
                               end ;
            decode n := match (decode n) with
                        | Some () => Some MTDC
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
Defined.

Global Instance reg_finite : finite.Finite RegName.
Proof. apply (finite.enc_finite (λ r : RegName, match r with
                                                | PC => S RegNum
                                                | R n fin => n
                                                end)
                (λ n : nat, match n_to_regname n with | Some r => r | None => PC end)
                (S (S RegNum))).
       - intros x. destruct x as [| n fin];auto.
         unfold n_to_regname.
         destruct (Nat.le_dec n RegNum).
         + do 2 f_equal. apply eq_proofs_unicity. decide equality.
         + exfalso. by apply (Nat.leb_le n RegNum) in fin.
       - intros x.
         + destruct x as [|n fin];[lia|]. apply Nat.leb_le in fin. lia.
       - intros i Hlt. unfold n_to_regname.
         destruct (Nat.le_dec i RegNum);auto.
         lia.
Defined.

Global Instance sreg_finite : finite.Finite SRegName.
Proof.
 apply (finite.enc_finite (λ r : SRegName, match r with | MTDC => 0%nat end)
                (λ n : nat, MTDC)
                1%nat).
 - by intro sr; destruct sr.
 - by intro sr; destruct sr.
 - lia.
Defined.

(* Instances for [zify]: make [lia] work on registers *)
(* TODO: separate the proof parts into lemmas *)

Definition Z_of_regname (r: RegName): Z.
  destruct r as [|n fin].
  + exact 0.
  + exact (S n).
Defined.

Instance RegName_InjTyp : InjTyp RegName Z.
  refine (mkinj _ _ Z_of_regname (fun n => n <= RegNum + 1)%Z _).
  intros [|n fin]; cbn;first lia.
  apply Nat.leb_le in fin; lia.
Defined.
Add Zify InjTyp RegName_InjTyp.

Instance Op_RegName_eq : BinRel (@eq RegName).
  refine ({| TR := @eq Z; TRInj := _ |}).
  cbn. intros r1 r2. split.
  - intros ->; eauto.
  - destruct r1; destruct r2; eauto; cbn; try apply Nat.leb_le in fin; try lia.
    intros ->%Nat2Z.inj%eq_add_S.
    f_equal. apply eq_proofs_unicity. intros [|] [|]; eauto.
Defined.
Add Zify BinRel Op_RegName_eq.

(* Names for registers *)
(* special registers *)
Definition cnull  : RegName := R 0 eq_refl. (* supposed to be null register *)
Definition cra    : RegName := R 1 eq_refl. (* link register *)
Definition csp    : RegName := R 2 eq_refl. (* compartment stack register *)
Definition cgp    : RegName := R 3 eq_refl. (* global data register *)

(* temporary registers *)
Definition ctp : RegName := R 4 eq_refl.
Definition ct0 : RegName := R 5 eq_refl.
Definition ct1 : RegName := R 6 eq_refl.
Definition ct2 : RegName := R 7 eq_refl.
Definition ct3 : RegName := R 28 eq_refl.
Definition ct4 : RegName := R 29 eq_refl.
Definition ct5 : RegName := R 30 eq_refl.
Definition ct6 : RegName := R 31 eq_refl.

(* other temporary registers *)
Definition cs0  : RegName := R 8 eq_refl.  (* also aliased cfp *)
Definition cs1  : RegName := R 9 eq_refl.
Definition cs2  : RegName := R 18 eq_refl.
Definition cs3  : RegName := R 19 eq_refl.
Definition cs4  : RegName := R 20 eq_refl.
Definition cs5  : RegName := R 21 eq_refl.
Definition cs6  : RegName := R 22 eq_refl.
Definition cs7  : RegName := R 23 eq_refl.
Definition cs8  : RegName := R 24 eq_refl.
Definition cs9  : RegName := R 25 eq_refl.
Definition cs10 : RegName := R 26 eq_refl.
Definition cs11 : RegName := R 27 eq_refl.

(* argument registers *)
Definition ca0 : RegName := R 10 eq_refl.
Definition ca1 : RegName := R 11 eq_refl.
Definition ca2 : RegName := R 12 eq_refl.
Definition ca3 : RegName := R 13 eq_refl.
Definition ca4 : RegName := R 14 eq_refl.
Definition ca5 : RegName := R 15 eq_refl.
Definition ca6 : RegName := R 16 eq_refl.
Definition ca7 : RegName := R 17 eq_refl.

Notation mtdc  := MTDC.

(* A list of all general purpose registers *)
Definition all_registers : list RegName :=
  [
    cnull  ; (* supposed to be null register *)
    cra    ; (* link register *)
    csp    ; (* compartment stack register *)
    cgp    ; (* global data register *)
    (* temporary registers *)
    ctp ;
    ct0 ;
    ct1 ;
    ct2 ;
    ct3 ;
    ct4 ;
    ct5 ;
    ct6 ;
    (* other temporary registers *)
    cs0  ;  (* also aliased cfp *)
    cs1  ;
    cs2  ;
    cs3  ;
    cs4  ;
    cs5  ;
    cs6  ;
    cs7  ;
    cs8  ;
    cs9  ;
    cs10 ;
    cs11 ;
    (* argument registers *)
    ca0 ;
    ca1 ;
    ca2 ;
    ca3 ;
    ca4 ;
    ca5 ;
    ca6 ;
    ca7 ;
    PC
  ].

(* Set of all registers *)
Definition all_registers_s : gset RegName := list_to_set all_registers.

Lemma all_registers_NoDup :
  NoDup all_registers.
Proof.
  unfold all_registers.
  repeat (
    apply NoDup_cons_2;
    first (repeat (rewrite not_elem_of_cons; split; [done|]); apply not_elem_of_nil)
  ).
  by apply NoDup_nil.
Qed.

(* Spec for all_registers *)

Lemma all_registers_correct r1 :
  r1 ∈ all_registers.
Proof.
  set ( all_registers' := [cnull; cra; csp; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5; ca6; ca7;
        cs2; cs3; cs4; cs5; cs6; cs7; cs8; cs9; cs10; cs11; ct3; ct4; ct5; ct6; PC]).
  assert (elements ((list_to_set all_registers) : gset RegName) ≡ₚ elements ((list_to_set all_registers') : gset RegName)).
  { set_solver. }
  setoid_rewrite elements_list_to_set in H; cycle 1.
  { rewrite /all_registers.
    repeat (apply NoDup_cons; split; first set_solver).
    by apply NoDup_nil.
  }
  { rewrite /all_registers'.
    repeat (apply NoDup_cons; split; first set_solver).
    by apply NoDup_nil.
  }
  setoid_rewrite H.
  destruct r1 as [|n fin].
  - do 32 (apply elem_of_cons; right).
      by apply elem_of_list_singleton.
  - induction n as [|n IHn].
    + apply elem_of_cons; left.
      apply f_equal. apply eq_proofs_unicity. decide equality.
    + apply elem_of_list_lookup_2 with (S n).
      repeat (destruct n as [|n];
                first (simpl;do 2 f_equal;apply eq_proofs_unicity;decide equality)).
      cbn.
      simpl in *. inversion fin.
Qed.

Lemma all_registers_s_correct r:
  r ∈ all_registers_s.
Proof.
  rewrite /all_registers_s elem_of_list_to_set.
  apply all_registers_correct.
Qed.

Lemma all_registers_correct_sub r : NoDup r → r ⊆+ all_registers.
Proof.
  intros Hdup.
  apply NoDup_submseteq;auto. intros r' Hin.
  apply all_registers_correct.
Qed.

Instance setunfold_all_regs:
  forall x, SetUnfoldElemOf x all_registers_s True.
Proof.
  intros. constructor. split; auto.
  intro. eapply all_registers_s_correct.
Qed.

Lemma all_registers_union_l s :
  s ∪ all_registers_s = all_registers_s.
Proof.
  apply (anti_symm subseteq). 2: set_solver.
  rewrite elem_of_subseteq. intros ? _.
  apply all_registers_s_correct.
Qed.

Lemma all_registers_union_r s :
  all_registers_s ∪ s = all_registers_s.
Proof. rewrite union_comm_L. apply all_registers_union_l. Qed.

Lemma all_registers_subseteq s :
  s ⊆ all_registers_s.
Proof.
  rewrite elem_of_subseteq. intros ? _. apply all_registers_s_correct.
Qed.

Lemma regmap_full_dom {A} (r: gmap RegName A):
  (∀ x, is_Some (r !! x)) →
  dom r = all_registers_s.
Proof.
  intros Hfull. apply (anti_symm subseteq); rewrite elem_of_subseteq.
  - intros rr _. apply all_registers_s_correct.
  - intros rr _. rewrite elem_of_dom. apply Hfull.
Qed.

Global Opaque cnull cra csp cgp ctp ct0 ct1 ct2 cs0 cs1 ca0 ca1 ca2 ca3 ca4 ca5 ca6 ca7
        cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ct3 ct4 ct5 ct6.

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
Notation top_ot := (finz.largest za : OType).
Notation "0" := (za_ot) : OType_scope.

Notation eqb_otype := (λ (a1 a2: OType), Z.eqb a1 a2).
Notation "a1 =? a2" := (eqb_otype a1 a2) : OType_scope.

Notation otype_incr_eq := (finz_incr_eq).
