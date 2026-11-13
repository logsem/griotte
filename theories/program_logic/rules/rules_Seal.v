From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Seal

    Seal has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section seal_next_ok.
  Context `{MP : MachineParameters}.

  (** A sealing range and a sealable: the sealable sealed at the cursor,
      tagged if the range permits it; derived from the sealable. The sealing
      range is never stripped. *)
  Lemma seal_next_ok p0 lpc regs dst r1 r2 (ta : bool) p g b e a πs sb π :
    regs !!ₗ r1 = Some (WSealRange ta p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealable sb @@? π) →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst
      (WSealed a (and_tag_sealable (ta && get_tag_sealable sb && permit_seal p && withinBounds b e a) sb)
         @@? π) 1.
  Proof.
    intros H1 H2. exists (λ S, S r2). split.
    { apply (lsource_derive _ _ _ _ _ H2); destruct sb; cbn; try solve [auto];
        by intros [_ Ht]%andb_prop. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2).
    destruct (S r1) eqn:Hs1.
    - rewrite /= /regs_effect.
      destruct (S r2), sb as [t' ? ? ? ? ? | t' ? ? ? ? ?], ta, t', (permit_seal p),
        (withinBounds b e a); done.
    - exfalso. rewrite /llookup_reg in H1. case_decide; first done.
      destruct (Hcopy r1 _ H1) as [_ Hstrip]. by destruct (Hstrip Hs1).
  Qed.

  (** The sealable is tagged and the range permits sealing at its cursor:
      the sealable sealed as it is. *)
  Lemma seal_next_ok_tagged p0 lpc regs dst r1 r2 p g b e a πs sb π :
    regs !!ₗ r1 = Some (SealRange p g b e a @@? πs) →
    regs !!ₗ r2 = Some (WSealable sb @@? π) →
    get_tag_sealable sb = true →
    permit_seal p = true →
    withinBounds b e a = true →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst (WSealed a sb @@? π) 1.
  Proof.
    intros H1 H2 Htag Hperm Hwb.
    pose proof (seal_next_ok p0 lpc regs dst r1 r2 true p g b e a πs sb π H1 H2) as Hok.
    by rewrite Htag Hperm Hwb /= and_tag_sealable_true in Hok.
  Qed.

  (** Without a sealing range and a sealable, the sealee loses its tag. *)
  Lemma seal_next_ok_other p0 lpc regs dst r1 r2 v1 v2 :
    regs !!ₗ r1 = Some v1 →
    regs !!ₗ r2 = Some v2 →
    is_sealr v1.(lw) && is_sealb v2.(lw) = false →
    regs_next_ok (Seal dst r1 r2) p0 lpc regs dst (lclear_tag v2) 1.
  Proof.
    intros H1 H2 Hkind. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy H1) (regs_copy_llookup _ _ _ _ _ Hcopy H2)
      /regs_effect.
    destruct v1 as [ [| [] | | ? [] ] ?], v2 as [ [| [] | | ? [] ] ?]; cbn in Hkind |- *;
      try discriminate; by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.
End seal_next_ok.

(* [seal_next_ok] is not a hint: on literal operands it has no fact to check
   and would give the word with its tag as a value; a client names it with
   [iInstr "H" using seal_next_ok]. *)
#[export] Hint Resolve seal_next_ok_tagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seal_next_ok_tagged : regs_next_ok_lax_db.
#[export] Hint Resolve seal_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 1 (is_sealr _ && is_sealb _ = false) =>
  first [ reflexivity | eassumption ] : regs_next_ok_db.
