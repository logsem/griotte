From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** The conditional jumps, which differ only by their comparison
    [jcond_test]. *)
Definition is_JCond (i : instr) (off arg1 arg2 : Z + RegName) :=
  i = Jeq off arg1 arg2 ∨
  i = Jne off arg1 arg2 ∨
  i = Jlt off arg1 arg2 ∨
  i = Jle off arg1 arg2.

(* Hints to automate proofs of is_JCond *)
Lemma is_JCond_Jeq off arg1 arg2 : is_JCond (Jeq off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jne off arg1 arg2 : is_JCond (Jne off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jlt off arg1 arg2 : is_JCond (Jlt off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.
Lemma is_JCond_Jle off arg1 arg2 : is_JCond (Jle off arg1 arg2) off arg1 arg2.
Proof. rewrite /is_JCond. naive_solver. Qed.

#[export] Hint Resolve is_JCond_Jeq : core.
#[export] Hint Resolve is_JCond_Jne : core.
#[export] Hint Resolve is_JCond_Jlt : core.
#[export] Hint Resolve is_JCond_Jle : core.

(** The conditional jumps have no WP rule of their own: [iInstr] steps them
    with the register rules of [rules_regs.v] ([wp_regs_jump_0] to
    [wp_regs_jump_3]), from their register steps in closed form below. *)

Section jcond_jump_agree.
  Context `{MP : MachineParameters}.

  Lemma exec_opt_is_JCond i off arg1 arg2 p φ :
    is_JCond i off arg1 arg2 →
    exec_opt i p φ = exec_jcond (jcond_test i) off arg1 arg2 φ.
  Proof. intros HH. destruct_or! HH; subst i; reflexivity. Qed.

  (** A conditional jump whose test holds moves the PC by its offset. *)
  Lemma jcond_jump_agree_jmp i off ρ1 ρ2 p lpc regs n1 n2 imm :
    is_JCond i off ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    jcond_test i n1 n2 = true →
    lz_of_argument regs off = Some imm →
    regs_jump_agree i p lpc regs imm.
  Proof.
    intros Hi H1 H2 Ht Himm φ S _ Hc.
    rewrite (exec_opt_is_JCond _ _ _ _ _ _ Hi) /exec_jcond (regs_copy_z _ _ _ _ _ Hc H1)
      (regs_copy_z _ _ _ _ _ Hc H2) /= Ht (regs_copy_z _ _ _ _ _ Hc Himm) /=.
    by rewrite /regs_effect.
  Qed.

  (** A conditional jump whose test fails moves the PC to the next
      instruction. *)
  Lemma jcond_jump_agree_next i off ρ1 ρ2 p lpc regs n1 n2 :
    is_JCond i off ρ1 ρ2 →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    jcond_test i n1 n2 = false →
    regs_jump_agree i p lpc regs 1.
  Proof.
    intros Hi H1 H2 Ht φ S _ Hc.
    rewrite (exec_opt_is_JCond _ _ _ _ _ _ Hi) /exec_jcond (regs_copy_z _ _ _ _ _ Hc H1)
      (regs_copy_z _ _ _ _ _ Hc H2) /= Ht.
    done.
  Qed.

  (** The comparison of a register with zero, [Jne off r 0] and
      [Jeq off r 0]: on a register holding the integer [0], else on whether
      its word is zero ([nonZero]). *)
  Lemma jnez_jump_agree_next_int off r p lpc regs v :
    regs !!ₗ r = Some v →
    IsLInt v 0 →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hv.
    by eapply jcond_jump_agree_next; [ | eapply lz_of_argument_reg_int | apply lz_of_argument_z | ].
  Qed.

  Lemma jnez_jump_agree_next off r p lpc regs v :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = false →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hz.
    by eapply jcond_jump_agree_next; [ | apply lz_of_argument_reg | apply lz_of_argument_z | ].
  Qed.

  Lemma jnez_jump_agree_jmp off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = true →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jne off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hnz Himm.
    by eapply jcond_jump_agree_jmp; [ | apply lz_of_argument_reg | apply lz_of_argument_z | | ].
  Qed.

  Lemma jeqz_jump_agree_jmp_int off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    IsLInt v 0 →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hv Himm.
    by eapply jcond_jump_agree_jmp;
      [ | eapply lz_of_argument_reg_int | apply lz_of_argument_z | | ].
  Qed.

  Lemma jeqz_jump_agree_jmp off r p lpc regs v imm :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = false →
    lz_of_argument regs off = Some imm →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs imm.
  Proof.
    intros Hr Hz Himm.
    by eapply jcond_jump_agree_jmp;
      [ | apply lz_of_argument_reg | apply lz_of_argument_z | cbn; by apply negb_false_iff | ].
  Qed.

  Lemma jeqz_jump_agree_next off r p lpc regs v :
    regs !!ₗ r = Some v →
    nonZero v.(lw) = true →
    regs_jump_agree (Jeq off (inr r) (inl 0%Z)) p lpc regs 1.
  Proof.
    intros Hr Hnz.
    by eapply jcond_jump_agree_next;
      [ | apply lz_of_argument_reg | apply lz_of_argument_z | cbn; by apply negb_true_iff ].
  Qed.
End jcond_jump_agree.

(* The comparison of a register with zero is stepped by its own lemmas
   below, the other forms by the general ones. The taken jump first: a test
   that fails is cheaper to reject on a known operand (zero) than on a
   symbolic one. *)
#[export] Hint Extern 0 (regs_jump_agree ?i _ _ _ _) =>
  lazymatch i with
  | Jne _ (inr _) (inl 0%Z) => fail
  | Jeq _ (inr _) (inl 0%Z) => fail
  | _ => simple eapply jcond_jump_agree_jmp
  end : regs_next_ok_db.
#[export] Hint Extern 1 (regs_jump_agree ?i _ _ _ _) =>
  lazymatch i with
  | Jne _ (inr _) (inl 0%Z) => fail
  | Jeq _ (inr _) (inl 0%Z) => fail
  | _ => simple eapply jcond_jump_agree_next
  end : regs_next_ok_db.
(* [Jne r 0] falls through on the integer [0] or a word known to be zero,
   else jumps; [Jeq r 0] the converse. The fact that the word is not zero is
   left to the client when the search does not decide it. *)
#[export] Hint Resolve jnez_jump_agree_next_int | 0 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_next | 1 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_jmp | 2 : regs_next_ok_db.
#[export] Hint Resolve jnez_jump_agree_jmp : regs_next_ok_lax_db.
#[export] Hint Resolve jeqz_jump_agree_jmp_int | 0 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_jmp | 1 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_next | 2 : regs_next_ok_db.
#[export] Hint Resolve jeqz_jump_agree_next : regs_next_ok_lax_db.
