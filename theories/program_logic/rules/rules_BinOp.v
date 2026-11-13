From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.
From griotte Require Import machine_base.

Section griotte_lang_rules.
  Context `{MP: MachineParameters}.

  Definition denote (i: instr) (n1 n2: Z): Z :=
    match i with
    | machine_instructions.Add _ _ _ => (n1 + n2)%Z
    | Sub _ _ _ => (n1 - n2)%Z
    | Mul _ _ _ => (n1 * n2)%Z
    | LAnd _ _ _ => (Z.land n1 n2)
    | LOr _ _ _ => (Z.lor n1 n2)
    | LShiftL _ _ _ => (n1 ≪ n2)%Z
    | LShiftR _ _ _ => (n1 ≫ n2)%Z
    | Lt _ _ _ => (Z.b2z (n1 <? n2)%Z)
    | Le _ _ _ => (Z.b2z (n1 <=? n2)%Z)
    | _ => 0%Z
    end.

  Definition is_BinOp (i: instr) (r: RegName) (arg1 arg2: Z + RegName) :=
    i = machine_instructions.Add r arg1 arg2 ∨
    i = Sub r arg1 arg2 ∨
    i = Mul r arg1 arg2 ∨
    i = LAnd r arg1 arg2 ∨
    i = LOr r arg1 arg2 ∨
    i = LShiftL r arg1 arg2 ∨
    i = LShiftR r arg1 arg2 ∨
    i = Lt r arg1 arg2 ∨
    i = Le r arg1 arg2.

End griotte_lang_rules.

(* Hints to automate proofs of is_BinOp *)
Lemma is_BinOp_Add dst arg1 arg2 :
  is_BinOp (Add dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Sub dst arg1 arg2 :
  is_BinOp (Sub dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Mul dst arg1 arg2 :
  is_BinOp (Mul dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LAnd dst arg1 arg2 :
  is_BinOp (LAnd dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LOr dst arg1 arg2 :
  is_BinOp (LOr dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftL dst arg1 arg2 :
  is_BinOp (LShiftL dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_LShiftR dst arg1 arg2 :
  is_BinOp (LShiftR dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Lt dst arg1 arg2 :
  is_BinOp (Lt dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.
Lemma is_BinOp_Le dst arg1 arg2 :
  is_BinOp (Le dst arg1 arg2) dst arg1 arg2.
Proof. intros; unfold is_BinOp; naive_solver. Qed.

#[export] Hint Resolve is_BinOp_Add : core.
#[export] Hint Resolve is_BinOp_Sub : core.
#[export] Hint Resolve is_BinOp_Mul : core.
#[export] Hint Resolve is_BinOp_LAnd : core.
#[export] Hint Resolve is_BinOp_LOr : core.
#[export] Hint Resolve is_BinOp_LShiftL : core.
#[export] Hint Resolve is_BinOp_LShiftR : core.
#[export] Hint Resolve is_BinOp_Lt : core.
#[export] Hint Resolve is_BinOp_Le : core.

(** ** The register step in closed form *)

Section binop_next_ok.
  Context `{MP : MachineParameters}.

  (** A BinOp writes the denotation of its operands, untagged. A register
      operand gives the address of its word ([lz_of_argument]): an integer,
      or the address of a capability. *)
  Lemma binop_next_ok i p lpc regs dst ρ1 ρ2 n1 n2 :
    is_BinOp i dst ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    regs_next_ok i p lpc regs dst (WInt (denote i n1 n2) @@? None) 1.
  Proof.
    intros Hi Hn1 Hn2. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy. destruct_or! Hi; subst i;
      by rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn1) (regs_copy_z _ _ _ _ _ Hcopy Hn2)
        /= /regs_effect.
  Qed.
End binop_next_ok.

#[export] Hint Resolve binop_next_ok | 0 : regs_next_ok_db.
