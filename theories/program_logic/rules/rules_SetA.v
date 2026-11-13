From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export rules_base rules_Lea.
From griotte Require Import rules_regs.

(** * SetA

    SetA has no WP rule of its own: [iInstr] steps it with the register rules
    of [rules_regs.v], from its register steps in closed form below. *)

Section seta_next_ok.
  Context `{MP : MachineParameters}.

  (** The word a SetA writes: for a capability or a sealing range, the cursor
      set to the address, or the untagged original if the address is out of
      range; the address itself for an integer; the untagged original
      otherwise. *)
  Definition seta_result (v : LWord) (n : Z) : option LWord :=
    match v.(lw) with
    | WCap t p g b e a =>
        Some (match z_to_addr n with
              | Some a' => WCap t p g b e a'
              | None => Cap⁻ p g b e a
              end @@? v.(lprov))
    | WSealRange t p g b e a =>
        Some (match z_to_otype n with
              | Some a' => WSealRange t p g b e a'
              | None => SealRange⁻ p g b e a
              end @@? v.(lprov))
    | WInt _ => Some (WInt n @@? v.(lprov))
    | _ => Some (lclear_tag v)
    end.

  (** Setting the address to [n] moves the cursor by the difference to [n]. *)
  Lemma seta_result_lea_result (w : LWord) (n : Z) :
    seta_result w n = lea_result w (n - get_a w.(lw)).
  Proof.
    destruct w as [w π]. rewrite /seta_result /lea_result /=.
    destruct_word w; cbn; rewrite ?finz_incr_of_z; repeat f_equal; lia.
  Qed.

  (** SetA writes [seta_result] of its source, derived from the source. *)
  Lemma seta_next_ok p0 lpc regs dst src ρ v n v' :
    regs !!ₗ src = Some v →
    lz_of_argument regs ρ = Some n →
    seta_result v n = Some v' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst v' 1.
  Proof.
    intros Hsrc Hn Hres. exists (λ S, S src). destruct v as [w π].
    rewrite /seta_result /= in Hres. split.
    - destruct w as [m | [t p g b e a | t p g b e a] | k t p g b e a | o [] ]; cbn in Hres;
        simplify_eq; repeat case_match; simplify_eq; rewrite ?/lclear_tag ?/lift_word;
        apply (lsource_derive _ _ _ _ _ Hsrc); cbn; auto; done.
    - intros φ S _ Hc.
      rewrite /= (regs_copy_z _ _ _ _ _ Hc Hn) /= (regs_copy_llookup _ _ _ _ _ Hc Hsrc).
      rewrite /regs_effect.
      destruct (S src); destruct w as [m | [t p g b e a | t p g b e a] | k t p g b e a | o [] ];
        cbn in Hres |- *; simplify_eq; repeat case_match; simplify_eq; done.
  Qed.

  Lemma seta_next_ok_cap p0 lpc regs dst src ρ t p g b e a π n a' :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_addr n = Some a' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WCap t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_cap_invalid p0 lpc regs dst src ρ t p g b e a π n :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_addr n = None →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_sr p0 lpc regs dst src ρ t p g b e a π n a' :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_otype n = Some a' →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WSealRange t p g b e a' @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_sr_invalid p0 lpc regs dst src ρ t p g b e a π n :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n →
    z_to_otype n = None →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc Hn Ha'. eapply seta_next_ok; [exact Hsrc | exact Hn |].
    by rewrite /seta_result /= Ha'.
  Qed.

  Lemma seta_next_ok_int p0 lpc regs dst src ρ m π n :
    regs !!ₗ src = Some (WInt m @@? π) →
    lz_of_argument regs ρ = Some n →
    regs_next_ok (SetA dst src ρ) p0 lpc regs dst (WInt n @@? π) 1.
  Proof. intros Hsrc Hn. by eapply seta_next_ok. Qed.
End seta_next_ok.

#[export] Hint Resolve seta_next_ok_cap | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_cap : regs_next_ok_lax_db.
#[export] Hint Resolve seta_next_ok_cap_invalid | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve seta_next_ok_sr_invalid | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [seta_result]: the fact from the context, directly or as
   a [lea_result]. *)
#[export] Hint Resolve seta_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (seta_result _ _ = Some _) =>
  first [eassumption | rewrite seta_result_lea_result; eassumption] : regs_next_ok_db.
