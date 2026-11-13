From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Auipcc

    Auipcc has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

Section auipcc_next_ok.
  Context `{MP : MachineParameters}.

  (** Auipcc writes the PC at an offset address: below the PC, with its
      identifier. *)
  Lemma auipcc_next_ok p0 regs dst imm p g b e a π a' :
    (a + imm)%a = Some a' →
    regs_next_ok (Auipcc dst imm) p0 (Cap p g b e a @@? π) regs dst (Cap p g b e a' @@? π) 1.
  Proof.
    intros Ha'. exists (λ _, true). split.
    - apply lsource_pc; [| done | by intros _ _; left].
      apply capability_monotonicity_base.wle_cap; [done | reflexivity | reflexivity | solve_addr | solve_addr | by left].
    - intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
      by rewrite /regs_effect and_tag_true.
  Qed.

  (** On an address overflow, the PC untagged. *)
  Lemma auipcc_next_ok_overflow p0 regs dst imm p g b e a π :
    (a + imm)%a = None →
    regs_next_ok (Auipcc dst imm) p0 (Cap p g b e a @@? π) regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Ha'. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
    by rewrite /regs_effect and_tag_true.
  Qed.
End auipcc_next_ok.

#[export] Hint Resolve auipcc_next_ok | 0 : regs_next_ok_db.
#[export] Hint Resolve auipcc_next_ok_overflow | 1 : regs_next_ok_db.
