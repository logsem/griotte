From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Jmp

    Jmp has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v] ([wp_regs_jump_0], [wp_regs_jump_1]), from its register
    step in closed form below. *)

Section jmp_jump_agree.
  Context `{MP : MachineParameters}.

  (** Jmp moves the PC by its operand and writes no register. *)
  Lemma jmp_jump_agree p lpc regs ρ imm :
    lz_of_argument regs ρ = Some imm → regs_jump_agree (Jmp ρ) p lpc regs imm.
  Proof.
    intros Himm φ S _ Hc. by rewrite /= (regs_copy_z _ _ _ _ _ Hc Himm) /= /regs_effect.
  Qed.
End jmp_jump_agree.

#[export] Hint Resolve jmp_jump_agree | 0 : regs_next_ok_db.
