From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base.
From griotte Require Import rules_regs.

(** * Lea

    Lea has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section lea_next_ok.
  Context `{MP : MachineParameters}.

  (** The word a Lea writes: for a capability or a sealing range, the moved
      cursor, or the untagged original if the cursor overflows; the moved
      integer; the untagged original otherwise. *)
  Definition lea_result (v : LWord) (z : Z) : option LWord :=
    match v.(lw) with
    | WCap t p g b e a =>
        Some (match (a + z)%a with
              | Some a' => WCap t p g b e a'
              | None => Cap⁻ p g b e a
              end @@? v.(lprov))
    | WSealRange t p g b e a =>
        Some (match (a + z)%ot with
              | Some a' => WSealRange t p g b e a'
              | None => SealRange⁻ p g b e a
              end @@? v.(lprov))
    | WInt n => Some (WInt (n + z) @@? v.(lprov))
    | _ => Some (lclear_tag v)
    end.

  (** [lea_result] is defined on every word. *)
  Lemma lea_result_is_Some (w : LWord) (z : Z) : is_Some (lea_result w z).
  Proof. rewrite /lea_result. repeat case_match; eauto. Qed.

  (** Lea writes [lea_result] of its source, derived from the source. *)
  Lemma lea_next_ok p0 lpc regs dst src ρ v z v' :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some z →
    lea_result v z = Some v' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst v' 1.
  Proof.
    intros Hsrc Hz Hres. exists (λ S, S src). destruct v as [w π].
    rewrite /lea_result /= in Hres. split.
    - destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | o [] ]; cbn in Hres;
        simplify_eq; repeat case_match; simplify_eq; rewrite ?/lclear_tag ?/lift_word;
        apply (lsource_derive _ _ _ _ _ Hsrc); cbn; auto; done.
    - intros φ S _ Hc.
      rewrite /= (regs_copy_z _ _ _ _ _ Hc Hz) /= (regs_copy_llookup _ _ _ _ _ Hc Hsrc).
      rewrite /regs_effect.
      destruct (S src); destruct w as [n | [t p g b e a | t p g b e a] | k t p g b e a | o [] ];
        cbn in Hres |- *; simplify_eq; repeat case_match; simplify_eq; done.
  Qed.

  Lemma lea_next_ok_cap p0 lpc regs dst src ρ t p g b e a π z a' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%a = Some a' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WCap t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_cap_overflow p0 lpc regs dst src ρ t p g b e a π z :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%a = None →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_sr p0 lpc regs dst src ρ t p g b e a π z a' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%ot = Some a' →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WSealRange t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_sr_overflow p0 lpc regs dst src ρ t p g b e a π z :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some z →
    (a + z)%ot = None →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hz Ha'. eapply lea_next_ok; [exact Hsrc | exact Hz |].
    by rewrite /lea_result /= Ha'.
  Qed.

  Lemma lea_next_ok_int p0 lpc regs dst src ρ n π z :
    regs !!ₗ src = Some (WInt n @@? π) →
    lz_of_argument regs ρ = Some z →
    regs_next_ok (Lea dst src ρ) p0 lpc regs dst (WInt (n + z) @@? π) 1.
  Proof. intros Hsrc Hz. by eapply lea_next_ok. Qed.
End lea_next_ok.

#[export] Hint Resolve lea_next_ok_cap | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_cap : regs_next_ok_lax_db.
#[export] Hint Resolve lea_next_ok_cap_overflow | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve lea_next_ok_sr_overflow | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [lea_result]: the fact from the context. *)
#[export] Hint Resolve lea_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (lea_result _ _ = Some _) => eassumption : regs_next_ok_db.
