From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Restrict

    Restrict has no WP rule of its own: [iInstr] steps it with the register
    rules of [rules_regs.v], from its register steps in closed form below. *)

Section restrict_next_ok.
  Context `{MP : MachineParameters}.

  (** A capability takes the decoded permission and locality, tagged if
      they flow to the old ones; derived from the source. *)
  Lemma restrict_next_ok_cap p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    decodePermPair n = (p', g') →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst
      (WCap (t && PermFlowsTo p' p && LocalityFlowsTo g' g) p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn.
      + done.
      + by intros [ [Ht _]%andb_prop _]%andb_prop.
      + intros [ [_ Hflows]%andb_prop _]%andb_prop Hexec.
        eapply (executeAllowed_flowsto p' p); [by rewrite Hflows | exact Hexec].
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= Hdec.
      rewrite /regs_effect. by destruct (S src).
  Qed.

  (** A sealing range, likewise; a sealing range is never executable. *)
  Lemma restrict_next_ok_sr p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    decodeSealPermPair n = (p', g') →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst
      (WSealRange (t && SealPermFlowsTo p' p && LocalityFlowsTo g' g) p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn.
      + done.
      + by intros [ [Ht _]%andb_prop _]%andb_prop.
      + by intros _ Hexec.
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= Hdec.
      rewrite /regs_effect. by destruct (S src).
  Qed.

  (** An integer is unchanged; a sentry or a sealed word loses its tag. *)
  Lemma restrict_next_ok_other p0 lpc regs dst src ρ v n :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some n →
    is_mutable_range v.(lw) = false →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc Hn Hmutable. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_z _ _ _ _ _ Hcopy Hn) /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)
      /regs_effect.
    destruct v as [ [| [] | | ? [] ] ?]; cbn in Hmutable |- *; try discriminate;
      by rewrite ?and_tag_true ?clear_tag_and_tag.
  Qed.

  (** When the flows hold, the tag is kept. *)
  Lemma restrict_next_ok_cap_flows p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    (p', g') = decodePermPair n →
    PermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (WCap t p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec Hp Hg.
    pose proof (restrict_next_ok_cap p0 lpc regs dst src ρ t p g b e a π n p' g'
                  Hsrc Hn (eq_sym Hdec)) as Hok.
    by rewrite Hp Hg !andb_true_r in Hok.
  Qed.

  Lemma restrict_next_ok_sr_flows p0 lpc regs dst src ρ (t : bool) p g b e a π n p' g' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    (p', g') = decodeSealPermPair n →
    SealPermFlowsTo p' p = true →
    LocalityFlowsTo g' g = true →
    regs_next_ok (Restrict dst src ρ) p0 lpc regs dst (WSealRange t p' g' b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Hdec Hp Hg.
    pose proof (restrict_next_ok_sr p0 lpc regs dst src ρ t p g b e a π n p' g'
                  Hsrc Hn (eq_sym Hdec)) as Hok.
    by rewrite Hp Hg !andb_true_r in Hok.
  Qed.
End restrict_next_ok.

(* The forms with the flows first: they give the word with its tag. The
   decoding of a permission is never computed: it comes from the context, or
   stays a side goal with the flows. *)
#[export] Hint Resolve restrict_next_ok_cap_flows | 0 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_cap_flows : regs_next_ok_lax_db.
#[export] Hint Resolve restrict_next_ok_sr_flows | 0 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_sr_flows : regs_next_ok_lax_db.
#[export] Hint Resolve restrict_next_ok_cap | 5 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_sr | 5 : regs_next_ok_db.
#[export] Hint Resolve restrict_next_ok_other | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (decodePermPair _ = _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (_ = decodePermPair _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (decodeSealPermPair _ = _) => eassumption : regs_next_ok_db.
#[export] Hint Extern 0 (_ = decodeSealPermPair _) => eassumption : regs_next_ok_db.
