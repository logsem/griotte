From Stdlib Require Import Eqdep_dec. (* Needed to prove decidable equality on RegName *)
From Stdlib.micromega Require Import ZifyClasses.
From stdpp Require Import gmap list countable.
From machine_utils Require Export finz.
From griotte Require Export stdpp_extra.

(* No longer a coercion in Coq >= 8.14*)
#[local] Coercion Z.of_nat : nat >-> Z.

(* We assume a fixed set of registers: the RV32E register file x0-x15 *)
Definition RegNum: nat := 15.

(* ---------------------------------- Registers ----------------------------------------*)

(* The general registers. The PC is not one of them: it is a separate field
   of the machine configuration, which no instruction operand can name. *)
Inductive RegName: Type :=
| R (n: nat) (fin: n <=? RegNum = true).

Inductive SRegName : Type :=
| MTDC.

#[global] Instance reg_eq_dec : EqDecision RegName.
Proof. intros r1 r2.  destruct r1 as [n fin],r2 as [n0 fin0].
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

#[global] Instance reg_countable : Countable RegName.
Proof.
  refine {| encode r := encode match r with
                               | R n fin => n
                               end ;
            decode n := match (decode n) with
                        | Some n => n_to_regname n
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r as [n fin].
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (Nat.le_dec n RegNum).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Nat.leb_le n RegNum) in fin.
Defined.


#[global] Instance sreg_eq_dec : EqDecision SRegName.
Proof. intros r1 r2; destruct r1,r2; by left. Defined.

#[global] Instance sreg_countable : Countable SRegName.
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

#[global] Instance reg_finite : finite.Finite RegName.
Proof. apply (finite.enc_finite (λ r : RegName, match r with
                                                | R n fin => n
                                                end)
                (λ n : nat, match n_to_regname n with | Some r => r | None => R 0 eq_refl end)
                (S RegNum)).
       - intros x. destruct x as [n fin].
         unfold n_to_regname.
         destruct (Nat.le_dec n RegNum).
         + do 2 f_equal. apply eq_proofs_unicity. decide equality.
         + exfalso. by apply (Nat.leb_le n RegNum) in fin.
       - intros x.
         + destruct x as [n fin]. apply Nat.leb_le in fin. lia.
       - intros i Hlt. unfold n_to_regname.
         destruct (Nat.le_dec i RegNum);auto.
         lia.
Defined.

#[global] Instance sreg_finite : finite.Finite SRegName.
Proof.
 apply (finite.enc_finite (λ r : SRegName, match r with | MTDC => 0%nat end)
                (λ n : nat, MTDC)
                1%nat).
 - by intro sr; destruct sr.
 - intro sr; destruct sr; lia.
 - lia.
Defined.

(* Instances for [zify]: make [lia] work on registers *)
(* TODO: separate the proof parts into lemmas *)

Definition Z_of_regname (r: RegName): Z.
  destruct r as [n fin].
  exact (S n).
Defined.

#[export] Instance RegName_InjTyp : InjTyp RegName Z.
  refine (mkinj _ _ Z_of_regname (fun n => 1 <= n <= RegNum + 1)%Z _).
  intros [n fin]; cbn.
  apply Nat.leb_le in fin; lia.
Defined.
Add Zify InjTyp RegName_InjTyp.

#[export] Instance Op_RegName_eq : BinRel (@eq RegName).
  refine ({| TR := @eq Z; TRInj := _ |}).
  cbn. intros r1 r2. split.
  - intros ->; eauto.
  - destruct r1; destruct r2; cbn.
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

(* other temporary registers *)
Definition cs0  : RegName := R 8 eq_refl.  (* also aliased cfp *)
Definition cs1  : RegName := R 9 eq_refl.

(* argument registers *)
Definition ca0 : RegName := R 10 eq_refl.
Definition ca1 : RegName := R 11 eq_refl.
Definition ca2 : RegName := R 12 eq_refl.
Definition ca3 : RegName := R 13 eq_refl.
Definition ca4 : RegName := R 14 eq_refl.
Definition ca5 : RegName := R 15 eq_refl.

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
    (* other temporary registers *)
    cs0  ;  (* also aliased cfp *)
    cs1  ;
    (* argument registers *)
    ca0 ;
    ca1 ;
    ca2 ;
    ca3 ;
    ca4 ;
    ca5
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
  set ( all_registers' := [cnull; cra; csp; cgp; ctp; ct0; ct1; ct2; cs0; cs1; ca0; ca1; ca2; ca3; ca4; ca5]).
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
  destruct r1 as [n fin].
  induction n as [|n IHn].
  + apply elem_of_cons; left.
    apply f_equal. apply eq_proofs_unicity. decide equality.
  + apply list_elem_of_lookup_2 with (S n).
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

#[export] Instance setunfold_all_regs:
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

#[global] Opaque cnull cra csp cgp ctp ct0 ct1 ct2 cs0 cs1 ca0 ca1 ca2 ca3 ca4 ca5.
