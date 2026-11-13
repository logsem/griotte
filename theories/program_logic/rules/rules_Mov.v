From iris.proofmode Require Import proofmode.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Mov

    Mov has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register step in closed form below. *)

Section mov_next_ok.
  Context `{MP : MachineParameters}.

  (** Mov writes its argument: untagged for an immediate, derived from the
      register otherwise. *)
  Lemma mov_next_ok p lpc regs dst ρ v :
    lword_of_argument regs ρ = Some v → regs_next_ok (Mov dst ρ) p lpc regs dst v 1.
  Proof.
    intros Hv. destruct ρ as [z | r]; cbn in Hv.
    - simplify_eq. exists (λ _, true). split; first by apply lsource_untagged.
      intros φ S _ _. by rewrite /regs_effect and_tag_true.
    - exists (λ S, S r). split.
      + destruct v as [w π]. by apply (lsource_derive _ _ _ _ _ Hv).
      + intros φ S _ Hc. by rewrite /= (regs_copy_llookup _ _ _ _ _ Hc Hv) /regs_effect.
  Qed.

  Lemma mov_next_ok_z p lpc regs dst z :
    regs_next_ok (Mov dst (inl z)) p lpc regs dst (WInt z @@? None) 1.
  Proof. by apply mov_next_ok. Qed.

  Lemma mov_next_ok_reg p lpc regs dst r v :
    regs !!ₗ r = Some v → regs_next_ok (Mov dst (inr r)) p lpc regs dst v 1.
  Proof. exact (mov_next_ok p lpc regs dst (inr r) v). Qed.
End mov_next_ok.

#[export] Hint Resolve mov_next_ok_z | 0 : regs_next_ok_db.
#[export] Hint Resolve mov_next_ok_reg | 0 : regs_next_ok_db.
