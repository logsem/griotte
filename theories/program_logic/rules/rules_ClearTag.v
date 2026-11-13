From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * ClearTag

    ClearTag has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register step in closed form below. *)

Section cleartag_next_ok.
  Context `{MP : MachineParameters}.

  (** ClearTag writes its source untagged, with its identifier. *)
  Lemma cleartag_next_ok dst src p lpc regs v :
    regs !!ₗ src = Some v → regs_next_ok (ClearTag dst src) p lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc. exists (λ _, true).
    split; first (apply lsource_untagged; apply get_tag_clear_tag).
    intros φ S _ Hcopy.
    by rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= clear_tag_and_tag
      /regs_effect and_tag_true.
  Qed.
End cleartag_next_ok.

#[export] Hint Resolve cleartag_next_ok | 0 : regs_next_ok_db.
