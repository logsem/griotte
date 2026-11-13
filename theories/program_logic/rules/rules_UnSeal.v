From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * UnSeal

    UnSeal has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

(** The word an UnSeal writes, on any operands: with a sealing range and a
    sealed word, the sealable unsealed, tagged if the range permits it;
    otherwise the second operand untagged. *)
Definition unseal_word (v1 v2 : LWord) : LWord :=
  match v1.(lw), v2.(lw) with
  | WSealRange ta p g b e a, WSealed o sb =>
      WSealable (and_tag_sealable (ta && get_tag_sealable sb && permit_unseal p && withinBounds b e o)
                   (unseal_sb g sb)) @@? v2.(lprov)
  | _, _ => lclear_tag v2
  end.

Lemma unseal_word_not_sealed v1 v2 :
  is_sealr v1.(lw) && is_sealed v2.(lw) = false → unseal_word v1 v2 = lclear_tag v2.
Proof.
  intros Hkind. destruct v1 as [w1 π1], v2 as [w2 π2]; cbn in Hkind.
  destruct w1 as [| [] | | ], w2; cbn in Hkind; try discriminate; done.
Qed.

Section unseal_next_ok.
  Context `{MP : MachineParameters}.

  (** Without a sealing range and a sealed word, the operand loses its
      tag. *)
  Lemma unseal_next_ok_other p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    is_sealr v1.(lw) && is_sealed v2.(lw) = false →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (lclear_tag v2) 1.
  Proof.
    intros H1 H2 Hkind. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2)
      /regs_effect.
    destruct v1 as [ [| [] | | ? [] ] ?], v2 as [ [| [] | | ? [] ] ?]; cbn in Hkind |- *;
      try discriminate; by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.

  (** UnSeal writes [unseal_word] of its operands, derived from the sealed
      word. The sealing range is never stripped. *)
  Lemma unseal_next_ok p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (unseal_word v1 v2) 1.
  Proof.
    intros H1 H2. destruct (is_sealr v1.(lw) && is_sealed v2.(lw)) eqn:Hkind.
    2: { rewrite unseal_word_not_sealed //. by eapply unseal_next_ok_other. }
    destruct v1 as [ [| [|ta p g b e a] | | ] πs]; cbn in Hkind; try discriminate.
    destruct v2 as [ [| | | o sb] π]; cbn in Hkind; try discriminate.
    rewrite /unseal_word /=. exists (λ S, S r2). split.
    { apply (lsource_derive _ _ _ _ _ H2); destruct sb; cbn; try solve [auto];
        by intros [_ Ht]%andb_prop. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2).
    destruct (S r1) eqn:Hs1.
    - rewrite /= /regs_effect.
      destruct (S r2), sb as [t' ? ? ? ? ? | t' ? ? ? ? ?], ta, t', (permit_unseal p),
        (withinBounds b e o); done.
    - exfalso. rewrite /llookup_reg in H1. case_decide; first done.
      destruct (Hcopy r1 _ H1) as [_ Hstrip]. by destruct (Hstrip Hs1).
  Qed.

  (** The sealable is tagged and the range permits unsealing its otype: the
      sealable unsealed, with its tag. *)
  Lemma unseal_next_ok_tagged p0 lpc regs dst r1 r2 p g b e a πs o sb π :
    regs !!ₗ r1 = Some (SealRange p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealed o sb @@? π) →
    get_tag_sealable sb = true →
    permit_unseal p = true →
    withinBounds b e o = true →
    regs_next_ok (UnSeal dst r1 r2) p0 lpc regs dst (WSealable (unseal_sb g sb) @@? π) 1.
  Proof.
    intros H1 H2 Htag Hperm Hwb.
    pose proof (unseal_next_ok p0 lpc regs dst r1 r2 _ _ H1 H2) as Hok.
    by rewrite /unseal_word /= Htag Hperm Hwb /= and_tag_sealable_true in Hok.
  Qed.
End unseal_next_ok.

(* [unseal_next_ok] is not a hint: it has no fact to check and would give
   [unseal_word] where the tagged form gives the sealable; a client names it
   with [iInstr "H" using unseal_next_ok]. *)
#[export] Hint Resolve unseal_next_ok_tagged | 0 : regs_next_ok_db.
#[export] Hint Resolve unseal_next_ok_tagged : regs_next_ok_lax_db.
#[export] Hint Resolve unseal_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 1 (is_sealr _ && is_sealed _ = false) =>
  first [ reflexivity | eassumption ] : regs_next_ok_db.
