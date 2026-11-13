From iris.base_logic Require Export invariants gen_heap.
From iris.program_logic Require Export weakestpre ectx_lifting.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import frac.
From griotte Require Export shapes.step.
From griotte Require Import machine_base shapes.regs capability_monotonicity.

(** * The capability instructions

    Lea, SetA, Restrict, Subseg, ClearTag, the Get instructions (GetP, GetL,
    GetB, GetE, GetLen, GetA, GetOType, GetWType, GetTag), Seal, UnSeal and
    Auipcc. Per instruction: its register steps in closed form, lemmas
    concluding [regs_next_ok] or [regs_jump_agree], each registered in
    [regs_next_ok_db] (and its case lemmas in [regs_next_ok_lax_db]) on the
    lines after it; then its rules with a witness, if any. [iInstr] steps
    them with the register rules of [shapes/regs.v]. *)

(** ** Lea *)

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

  Lemma lea_next_ok_cap_untagged p0 lpc regs dst src ρ t p g b e a π z :
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

  Lemma lea_next_ok_sr_untagged p0 lpc regs dst src ρ t p g b e a π z :
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
#[export] Hint Resolve lea_next_ok_cap_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve lea_next_ok_sr_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve lea_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [lea_result]: the fact from the context. *)
#[export] Hint Resolve lea_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (lea_result _ _ = Some _) => eassumption : regs_next_ok_db.

(** ** SetA *)

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

  Lemma seta_next_ok_cap_untagged p0 lpc regs dst src ρ t p g b e a π n :
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

  Lemma seta_next_ok_sr_untagged p0 lpc regs dst src ρ t p g b e a π n :
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
#[export] Hint Resolve seta_next_ok_cap_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_sr : regs_next_ok_lax_db.
#[export] Hint Resolve seta_next_ok_sr_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve seta_next_ok_int | 0 : regs_next_ok_db.
(* Any word, through [seta_result]: the fact from the context, directly or as
   a [lea_result]. *)
#[export] Hint Resolve seta_next_ok | 5 : regs_next_ok_db.
#[export] Hint Extern 0 (seta_result _ _ = Some _) =>
  first [eassumption | rewrite seta_result_lea_result; eassumption] : regs_next_ok_db.

(** ** Restrict *)

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

#[local] Open Scope capability_scope.

(** ** Subseg

    Its rule with a witness, the rebase on an identifier
    ([wp_subseg_rebase]), follows its register steps. *)

(* Discharges [subseg_root_free] on a literal register map. *)
Ltac solve_subseg_root_free :=
  let Hd := fresh "Hd" in let Ha1 := fresh "Ha1" in let Ha2 := fresh "Ha2" in
  let Ht := fresh "Ht" in let Hlt := fresh "Hlt" in
  intros ? ? ? ? ? ? ? ? Hd Ha1 Ha2 Ht Hlt;
  rewrite /laddr_of_argument /lz_of_argument ?/llookup_reg in Ha1, Ha2, Hd;
  simplify_map_eq;
  first [ done | solve_addr | congruence
        | match goal with H : None = None → _ |- _ => by apply H end ].

Section subseg_next_ok.
  Context `{MP : MachineParameters}.

  (** An identifier-less source narrowed to a tagged, non-empty heap result
      needs its new base outside the heap. *)
  Definition subseg_root_free (regs : LReg) (src : RegName) arg1 arg2 : Prop :=
    ∀ t p g b e a a1 a2,
      regs !!ₗ src = Some (WCap t p g b e a @@? None) →
      laddr_of_argument regs arg1 = Some a1 →
      laddr_of_argument regs arg2 = Some a2 →
      (t && isWithin a1 a2 b e && (a1 <=? a2)%a) = true →
      (a1 < a2)%a →
      is_heap_address a1 = false.

  (** Subseg of a capability with representable endpoints writes the new
      bounds, the tag kept only within the old bounds. *)
  Lemma subseg_agree_cap pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    regs_next_agree exec_opt (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π) 1 (λ S, S src).
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= Ha1 Ha2 /regs_effect.
    by destruct (S src).
  Qed.

  Lemma subseg_next_ok_cap pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    subseg_root_free regs src ρ1 ρ2 →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WCap (t && isWithin a1 a2 b e && (a1 <=? a2)%a) p g a1 a2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 Hfree. exists (λ S, S src).
    split; last by eapply subseg_agree_cap.
    assert (regs !! src = Some (WCap t p g b e a @@? π)) as Hsrc'.
    { rewrite /llookup_reg in Hsrc. by case_decide. }
    apply (lsource_reg _ _ _ _ _ Hsrc'); [| done |].
    - destruct (t && isWithin a1 a2 b e && (a1 <=? a2)%a) eqn:Htag; last by apply wle_untagged.
      apply andb_true_iff in Htag as [ [-> Hwithin]%andb_true_iff Hle%Z.leb_le].
      apply isWithin_implies in Hwithin. cbn.
      apply wle_cap; [done | apply PermFlowsToReflexive | apply LocalityFlowsToReflexive
                     | solve_addr | solve_addr | right; solve_addr].
    - intros Hπ Htag. right. cbn in Hπ; subst π. rewrite /heap_authority_base /heap_cap_base /=.
      case_decide as Hlt; last done.
      rewrite (Hfree t p g b e a a1 a2 Hsrc); [done | | | done | done];
        rewrite /laddr_of_argument ?H1 ?H2 //.
  Qed.

  (** A result within the old bounds keeps the tag: the facts of the
      dedicated rules. *)
  Lemma subseg_next_ok_cap_valid pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 a1 a2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = Some a1 →
    z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    (π = None → (a1 < a2)%a → is_heap_address a1 = false) →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (WCap t p g a1 a2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ha1 Ha2 Hwb Hle Hroot.
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    pose proof (subseg_next_ok_cap pl lpc regs dst src ρ1 ρ2 t p g b e a π n1 n2 a1 a2
                  Hsrc H1 H2 Ha1 Ha2) as Hok.
    rewrite Hwb Hle' !andb_true_r in Hok. apply Hok.
    intros t' p' g' b' e' a' a1' a2' Hsrc' Ha1' Ha2' _ Hlt.
    rewrite Hsrc in Hsrc'. simplify_eq.
    rewrite /laddr_of_argument H1 Ha1 in Ha1'.
    rewrite /laddr_of_argument H2 Ha2 in Ha2'.
    simplify_eq.
    by apply Hroot.
  Qed.

  (** Both endpoints from the same operand: an empty result. *)
  Lemma subseg_next_ok_cap_same pl lpc regs dst src ρ (t : bool) p g b e a π n1 a1 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n1 →
    z_to_addr n1 = Some a1 →
    isWithin a1 a1 b e = true →
    regs_next_ok (Subseg dst src ρ ρ) pl lpc regs dst (WCap t p g a1 a1 a @@? π) 1.
  Proof.
    intros Hsrc H1 Ha1 Hwb.
    eapply subseg_next_ok_cap_valid;
      [exact Hsrc | exact H1 | exact H1 | exact Ha1 | exact Ha1 | exact Hwb | solve_addr |].
    intros _ Hlt. exfalso. solve_addr.
  Qed.

  (** [Subseg dst dst dst ρ2]: the base is the address of the capability
      itself (CHERIoT's [csetbounds]). *)
  Lemma subseg_next_ok_cap_base pl lpc regs dst ρ2 (t : bool) p g b e a π n2 a2 :
    regs !!ₗ dst = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n2 = Some a2 →
    isWithin a a2 b e = true →
    (a <= a2)%a →
    (π = None → (a < a2)%a → is_heap_address a = false) →
    regs_next_ok (Subseg dst dst (inr dst) ρ2) pl lpc regs dst (WCap t p g a a2 a @@? π) 1.
  Proof.
    intros Hd H2 Ha2 Hwb Hle Hroot.
    eapply subseg_next_ok_cap_valid; [exact Hd | | exact H2 | apply finz_of_z_to_z | done..].
    by rewrite /lz_of_argument Hd.
  Qed.

  Lemma subseg_next_ok_cap_untagged pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 :
    regs !!ₗ src = Some (WCap t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_addr n1 = None ∨ z_to_addr n2 = None →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Hnone. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= /regs_effect ?and_tag_true.
    destruct Hnone as [-> | ->]; first done. by destruct (z_to_addr n1).
  Qed.

  Lemma subseg_next_ok_sr pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 o1 o2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = Some o1 →
    z_to_otype n2 = Some o2 →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst
      (WSealRange (t && isWithin o1 o2 b e) p g o1 o2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ho1 Ho2. exists (λ S, S src). split.
    - apply (lsource_derive _ _ _ _ _ Hsrc); cbn; [done | by destruct t | done].
    - intros φ S _ Hcopy.
      rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
        (regs_copy_z _ _ _ _ _ Hcopy H2) /= Ho1 Ho2 /regs_effect.
      by destruct (S src).
  Qed.

  (** A result within the old bounds keeps the tag. *)
  Lemma subseg_next_ok_sr_valid pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 o1 o2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = Some o1 →
    z_to_otype n2 = Some o2 →
    isWithin o1 o2 b e = true →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (WSealRange t p g o1 o2 a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Ho1 Ho2 Hwb.
    pose proof (subseg_next_ok_sr pl lpc regs dst src ρ1 ρ2 t p g b e a π n1 n2 o1 o2
                  Hsrc H1 H2 Ho1 Ho2) as Hok.
    by rewrite Hwb andb_true_r in Hok.
  Qed.

  Lemma subseg_next_ok_sr_same pl lpc regs dst src ρ (t : bool) p g b e a π n1 o1 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ = Some n1 →
    z_to_otype n1 = Some o1 →
    isWithin o1 o1 b e = true →
    regs_next_ok (Subseg dst src ρ ρ) pl lpc regs dst (WSealRange t p g o1 o1 a @@? π) 1.
  Proof.
    intros Hsrc H1 Ho1 Hwb.
    by eapply subseg_next_ok_sr_valid; [exact Hsrc | exact H1 | exact H1 | exact Ho1 | exact Ho1 |].
  Qed.

  Lemma subseg_next_ok_sr_untagged pl lpc regs dst src ρ1 ρ2 (t : bool) p g b e a π n1 n2 :
    regs !!ₗ src = Some (WSealRange t p g b e a @@? π) →
    lz_of_argument regs ρ1 = Some n1 →
    lz_of_argument regs ρ2 = Some n2 →
    z_to_otype n1 = None ∨ z_to_otype n2 = None →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (SealRange⁻ p g b e a @@? π) 1.
  Proof.
    intros Hsrc H1 H2 Hnone. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /= (regs_copy_z _ _ _ _ _ Hcopy H1)
      (regs_copy_z _ _ _ _ _ Hcopy H2) /= /regs_effect ?and_tag_true.
    destruct Hnone as [-> | ->]; first done. by destruct (z_to_otype n1).
  Qed.

  (** An integer is unchanged; a sealed word or a sentry loses its tag. *)
  Lemma subseg_next_ok_other pl lpc regs dst src ρ1 ρ2 v :
    regs !!ₗ src = Some v →
    is_mutable_range v.(lw) = false →
    regs_next_ok (Subseg dst src ρ1 ρ2) pl lpc regs dst (lclear_tag v) 1.
  Proof.
    intros Hsrc Hmutable. exists (λ _, true). split.
    { apply lsource_untagged, get_tag_clear_tag. }
    intros φ S _ Hcopy.
    rewrite /= (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc) /regs_effect ?and_tag_true.
    destruct v as [w π]; cbn in Hmutable |- *.
    destruct w as [| [] | | ? [] ]; try discriminate Hmutable; by destruct (S src).
  Qed.

  (** *** Sources with a witness *)

  (** A word below a source register whose new heap authority base, if
      any, is [a1], a heap root of the claim map. *)
  Lemma subseg_root_source regs lpc src v0 v a1 :
    regs !! src = Some v0 →
    v.(lw) ⊑ v0.(lw) →
    v.(lprov) = v0.(lprov) →
    (∀ b', heap_authority_base v.(lw) = Some b' → b' = a1) →
    lsource_witness_ok (λ _ C, C !! a1 = Some HeapRoot) regs lpc
      (λ _, v) (λ S, S src) (λ v', v' = v).
  Proof.
    intros Hsrc Hle Hprov Hbase R C st S Hreg Ha1 Hregs _ _.
    cbn beta in Ha1 |- *.
    destruct (Hregs src v0 Hsrc) as [Hok Hphys].
    split_and!; [| by eapply reg_phys_word_le_and_tag | done].
    destruct (get_tag v.(lw)) eqn:Htag; last by apply reg_word_ok_untagged.
    destruct v as [w π]; cbn in Hle, Hprov, Hbase, Htag; subst π.
    apply reg_word_ok_shrink; [done | by apply word_le_shrinks | done |].
    intros _ _ b' Hab. by rewrite (Hbase b' Hab).
  Qed.

  (** An identifier-less, non-executable capability narrowed to exactly the
      range of a live or painting identifier [ι] takes [ι]; the registry
      entry of [ι] comes from the witness. *)
  Lemma subseg_rebase_source regs lpc src p g b e a a1 a2 ι s :
    regs !! src = Some (Cap p g b e a @@? None) →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    lsource_witness_ok (λ R _, ∃ γ, R !! ι = Some (a1, a2, γ, s)) regs lpc
      (λ _, Cap p g a1 a2 a @@ ι) (λ S, S src) (λ v, v = Cap p g a1 a2 a @@ ι).
  Proof.
    intros Hsrc Hwb Hle Hs Hpx R C st S _ [γ HRι] Hregs _ _.
    destruct (Hregs src _ Hsrc) as [_ Hrel]. cbn beta.
    split_and!; [| | done].
    { eapply reg_word_ok_rebase; [exact HRι | by destruct Hs as [-> | ->] | exact Hpx]. }
    revert Hrel. destruct (S src); intros Hrel; rewrite ?and_tag_true ?and_tag_false in Hrel |- *.
    - apply reg_phys_exact. intros ι' x _ Hι Hx. cbn in Hι. simplify_eq.
      cbn. by intros [-> | ->]; destruct Hs.
    - (* The source is an empty heap capability without authority, and so
         is the result. *)
      destruct Hrel as [ [Heq | [_ [ [(? & ? & ? & _) _] | [Hna [base Hh] ] ] ] ] _];
        cbn in *; try discriminate.
      split; last done. right. split; first done. right.
      assert (is_heap_address b = true) as Hbh.
      { rewrite /heap_cap_base /= in Hh. by destruct (is_heap_address b). }
      assert (¬ (b < e)%a) as Hnlt.
      { intros Hlt. apply Hna. split; first done. exists b.
        apply heap_authority_base_memory_cap_bounds. eauto. }
      apply isWithin_implies in Hwb.
      assert (a1 = b) as -> by solve_addr. assert (a2 = b) as -> by solve_addr.
      split.
      + intros [_ [b' Hab] ].
        apply heap_authority_base_memory_cap_bounds in Hab as (? & [= <- <-] & ? & _).
        solve_addr.
      + rewrite /heap_cap_base /= Hbh. eauto.
  Qed.
End subseg_next_ok.

(* The tag as a value ([subseg_next_ok_cap], [subseg_next_ok_sr]) is not a
   hint: on literal operands it would be found before the forms that keep
   the tag, whose facts the clients prove; a client names it with
   [iInstr "H" using subseg_next_ok_cap]. *)
#[export] Hint Resolve subseg_next_ok_cap_same | 0 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_cap_same | 0 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_cap_valid | 1 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_cap_valid | 1 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_sr_same | 0 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_same | 0 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_sr_valid | 1 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_valid | 1 : regs_next_ok_lax_db.
#[export] Hint Resolve subseg_next_ok_cap_untagged | 5 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_sr_untagged | 5 : regs_next_ok_db.
#[export] Hint Resolve subseg_next_ok_other | 5 : regs_next_ok_db.

(** *** The rule with a witness *)

Section subseg_witness_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** The rebase: an identifier-less source narrowed to exactly the range of
      a non-dead identifier [ι] takes [ι]. The source is not executable,
      since an identified word never is. The allocate step
      ([ghost/registry.v]) gives [alloc_obj] and the status token. *)
  Lemma wp_subseg_rebase E pc_p pc_g pc_b pc_e pc_a pc_π w dst r1 r2 p g b e a w1 n1 w2 n2 a1 a2 pc_a'
      ι q s dq :
    decodeInstrW w.(lw) = Subseg dst dst (inr r1) (inr r2) →
    IsLInt w1 n1 →
    IsLInt w2 n2 →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    z_to_addr n1 = Some a1 → z_to_addr n2 = Some a2 →
    isWithin a1 a2 b e = true →
    (a1 <= a2)%a →
    s = ALive ∨ s = APainting →
    executeAllowed p = false →
    (pc_a + 1)%a = Some pc_a' →
    dst ≠ cnull ->
    r1 ≠ cnull ->
    r2 ≠ cnull ->

    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ dst ↦ᵣ Cap p g b e a @@? None
        ∗ ▷ r1 ↦ᵣ w1
        ∗ ▷ r2 ↦ᵣ w2
        ∗ alloc_obj ι a1 a2
        ∗ ι ↦st{q} s }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ r1 ↦ᵣ w1
          ∗ r2 ↦ᵣ w2
          ∗ dst ↦ᵣ (Cap p g a1 a2 a) @@ ι
          ∗ alloc_obj ι a1 a2
          ∗ ι ↦st{q} s
      }}}.
  Proof.
    iIntros (Hinstr Hw1 Hw2 Hvpc Hn1 Hn2 Hwb Hle Hs Hpx Hpc_a' Hcnull Hcnull' Hcnull'' Φ)
      "(>HPC & >Hpc_a & >Hdst & >Hr1 & >Hr2 & #Hobj & Htok) HΦ".
    destruct (IsLInt_inv _ _ Hw1) as [π1 ->].
    destruct (IsLInt_inv _ _ Hw2) as [π2 ->].
    assert ((a1 <=? a2)%a = true) as Hle' by solve_addr.
    iDestruct (map_of_regs_3 with "Hr1 Hr2 Hdst") as "[Hmap (%Hne12 & %Hne1d & %Hne2d)]".
    set (regs := <[r1 := WInt n1 @@? π1]> (<[r2 := WInt n2 @@? π2]>
                   (<[dst := Cap p g b e a @@? None]> (∅ : LReg)))).
    assert (regs !! dst = Some (Cap p g b e a @@? None)) as Hd.
    { rewrite /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r1) = Some n1) as Hz1.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    assert (lz_of_argument regs (inr r2) = Some n2) as Hz2.
    { rewrite /lz_of_argument llookup_reg_not_cnull // /regs. by simplify_map_eq. }
    pose proof (subseg_agree_cap pc_p (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) regs dst dst
                  (inr r1) (inr r2) true p g b e a None n1 n2 a1 a2
                  ltac:(by rewrite llookup_reg_not_cnull) Hz1 Hz2 Hn1 Hn2) as Hagree.
    rewrite Hwb Hle' in Hagree.
    (* The agreement reads only the physical word: the identifier [ι] of the
       written word is not in it. *)
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ regs dst (λ _, Cap p g a1 a2 a @@ ι) 1 (λ S, S dst)
              (λ v, v = Cap p g a1 a2 a @@ ι) (alloc_obj ι a1 a2 ∗ ι ↦st{q} s)
              (λ R _, ∃ γ, R !! ι = Some (a1, a2, γ, s))
              with "[$HPC $Hpc_a $Hobj $Htok $Hmap]");
      [done | rewrite /regs_instr_ok; by apply sw_of_none | done
      | by eapply subseg_rebase_source | exact Hagree
      | right; rewrite /regs; set_solver+ | |].
    { iIntros (R C) "HR _ [#Hobj' Htok']".
      iDestruct (reg_lookup_obj with "HR Hobj'") as %(γ & s' & HRι).
      iDestruct (reg_lookup_own with "HR Htok'") as %(b' & e' & γ' & HRι').
      rewrite HRι in HRι'. simplify_eq. iPureIntro. by eexists. }
    iIntros "!>" (lpc' regs' retv) "(%Hout & HPC & Hpc_a & [_ Htok] & Hmap)".
    rewrite /regs_outcome (incrementPC_gen_add true _ _ _ _ _ _ _ _ Hpc_a') in Hout.
    destruct Hout as (-> & -> & v & -> & ->).
    rewrite linsert_reg_not_cnull //. subst regs.
    iRegsMap "Hmap"; eauto. iApply "HΦ". iFrame "∗ #".
  Qed.
End subseg_witness_rules.

#[local] Close Scope capability_scope.

(** ** ClearTag *)

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

(** ** Get

    The result functions of the Get instructions ([get_denote]), their
    register steps in closed form, and the rules of GetTag with a witness:
    GetTag observes the tag, which is exact only under a dereference
    witness ([wp_gettag_success], the rule of [iInstr]). *)

Section get_definitions.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (* Generalized denote function, since multiple cases result in similar success *)
  Definition get_denote (i: instr) (w : Word): option Z :=
    match i with
    | GetP _ _ => Some (encodePermSum (get_p w))
    | GetL _ _ => Some (encodeLoc (get_l w))
    | GetB _ _ => Some (get_b w)
    | GetE _ _ => Some (get_e w)
    | GetLen _ _ => Some (get_e w - get_b w)%Z
    | GetA _ _ => Some (get_a w)
    | GetOType _ _ =>
        match w with
        | WSealed o _ => Some (o:Z)
        | _ => Some (-1)%Z
        end
    | GetTag _ _ => Some (Z.b2z (get_tag w))
    | GetWType _ _ => Some (encodeWordType w)
    | _ => None
    end.

  #[global] Arguments get_denote : simpl nomatch.

  Definition is_Get (i: instr) (dst src: RegName) :=
    i = GetP dst src ∨
    i = GetL dst src ∨
    i = GetB dst src ∨
    i = GetE dst src ∨
    i = GetLen dst src ∨
    i = GetA dst src \/
    i = GetOType dst src \/
    i = GetWType dst src \/
    i = GetTag dst src
  .

  (** The words whose physical tag may be cleared while the logical one is
      set: words with an identifier, and heap-based words without
      authority. *)
  Definition tag_strippable (w : LWord) : Prop :=
    get_tag w.(lw) = true ∧
    (is_Some w.(lprov) ∨ (¬ has_authority w.(lw) ∧ is_Some (heap_cap_base w.(lw)))).

  Lemma reg_phys_tag_strippable R (v : LWord) :
    reg_phys R v (clear_tag v.(lw)) → get_tag v.(lw) = true → tag_strippable v.
  Proof.
    intros [ [Heq | [_ [ [(ι & _ & Hι & _) _] | Hh] ] ] _] Ht; split; try done.
    - by rewrite -Heq get_tag_clear_tag in Ht.
    - left. by rewrite Hι.
    - by right.
  Qed.

  Lemma exec_opt_Get i dst src p (pc : Word) (r : Reg) sr m st td (wsrc : Word) :
    is_Get i dst src →
    lookup_reg src r = Some wsrc →
    exec_opt i p (MkExecConf pc r sr m st td) =
      match get_denote i wsrc with
      | Some z => nextPC (update_reg (MkExecConf pc r sr m st td) dst (WInt z))
      | None => None
      end.
  Proof.
    intros Hi Hs. destruct_or! Hi; subst i; cbn; rewrite Hs /=.
    all: destruct wsrc as [| [] | | ? [] ]; cbn; done.
  Qed.

  Lemma get_denote_and_tag i s (w : Word) :
    get_denote i (and_tag s w) =
      match i with
      | GetTag _ _ => Some (Z.b2z (s && get_tag w))
      | _ => get_denote i w
      end.
  Proof.
    destruct i; cbn; try done.
    all: try (by destruct s, w as [| [] | | ? [] ]).
    f_equal. pose proof (encodeWordType_correct (and_tag s w) w) as Heq.
    by destruct w as [| [] | | ? [] ].
  Qed.
End get_definitions.

(* Hints to automate proofs of is_Get *)

Lemma is_Get_GetP dst src : is_Get (GetP dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetL dst src : is_Get (GetL dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetB dst src : is_Get (GetB dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetE dst src : is_Get (GetE dst src) dst src.
Proof. intros; unfold is_Get; eauto. Qed.
Lemma is_Get_GetLen dst src : is_Get (GetLen dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetA dst src : is_Get (GetA dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetOType dst src : is_Get (GetOType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma is_Get_GetWType dst src : is_Get (GetWType dst src) dst src.
Proof. intros; unfold is_Get; eauto; firstorder. Qed.
Lemma getwtype_get_denote `{MachineParameters} r1 r2 w : get_denote (GetWType r1 r2) w = Some (encodeWordType w).
Proof. by destruct_word w ; cbn. Qed.

#[export] Hint Resolve is_Get_GetP : core.
#[export] Hint Resolve is_Get_GetL : core.
#[export] Hint Resolve is_Get_GetB : core.
#[export] Hint Resolve is_Get_GetE : core.
#[export] Hint Resolve is_Get_GetLen : core.
#[export] Hint Resolve is_Get_GetA : core.
#[export] Hint Resolve is_Get_GetOType : core.
#[export] Hint Resolve is_Get_GetWType : core.
#[export] Hint Resolve getwtype_get_denote : core.

Lemma is_Get_GetTag dst src : is_Get (GetTag dst src) dst src.
Proof. unfold is_Get; tauto. Qed.

Lemma gettag_get_denote `{MachineParameters} dst src w :
  get_denote (GetTag dst src) w = Some (Z.b2z (get_tag w)).
Proof. by destruct_word w. Qed.
#[export] Hint Resolve is_Get_GetTag gettag_get_denote : core.

Section get_next_ok.
  Context `{MP : MachineParameters}.

  (** A Get other than GetTag reads the same result on a stripped copy. *)
  Lemma get_denote_and_tag_not_gettag i dst src s (w : Word) :
    is_Get i dst src → i ≠ GetTag dst src → get_denote i (and_tag s w) = get_denote i w.
  Proof.
    intros Hi Hnot. rewrite get_denote_and_tag.
    destruct_or! Hi; subst i; first [done | by destruct Hnot].
  Qed.

  (** A Get other than GetTag writes the denotation of its source,
      untagged. *)
  Lemma get_next_ok i dst src p lpc regs v z :
    is_Get i dst src → i ≠ GetTag dst src →
    regs !!ₗ src = Some v → get_denote i v.(lw) = Some z →
    regs_next_ok i p lpc regs dst (WInt z @@? None) 1.
  Proof.
    intros Hi Hnot Hsrc Hz. exists (λ _, true). split; first by apply lsource_untagged.
    intros [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get i dst src _ _ _ _ _ _ _ _ Hi
                            (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite (get_denote_and_tag_not_gettag i dst src _ _ Hi Hnot) Hz and_tag_true.
  Qed.

  (** GetTag of an untagged word writes 0. *)
  Lemma gettag_next_ok_untagged dst src p lpc regs v :
    regs !!ₗ src = Some v → get_tag v.(lw) = false →
    regs_next_ok (GetTag dst src) p lpc regs dst (WInt 0 @@? None) 1.
  Proof.
    intros Hsrc Ht. exists (λ _, true). split; first by apply lsource_untagged.
    intros [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag dst src) dst src _ _ _ _ _ _ _ _
                            (is_Get_GetTag dst src) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite gettag_get_denote get_tag_and_tag Ht andb_false_r and_tag_true.
  Qed.

  (** GetTag to [cnull] writes nothing. *)
  Lemma gettag_jump_agree_to_cnull src p lpc regs v :
    regs !!ₗ src = Some v → regs_jump_agree (GetTag cnull src) p lpc regs 1.
  Proof.
    intros Hsrc [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag cnull src) cnull src _ _ _ _ _ _ _ _
                            (is_Get_GetTag cnull src) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    rewrite gettag_get_denote. cbv iota. by rewrite update_reg_cnull.
  Qed.
End get_next_ok.

#[export] Hint Extern 0 (_ ≠ GetTag _ _) => discriminate : regs_next_ok_db.
#[export] Hint Resolve gettag_next_ok_untagged | 0 : regs_next_ok_db.
#[export] Hint Resolve gettag_jump_agree_to_cnull | 0 : regs_next_ok_db.
#[export] Hint Resolve get_next_ok | 5 : regs_next_ok_db.

Section gettag_witness_rules.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ} {th : Thread} {CL : CritLink Σ th}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : ExecConf.
  Implicit Types a b : Addr.
  Implicit Types o : OType.
  Implicit Types r : RegName.
  Implicit Types w : LWord.
  Implicit Types reg : gmap RegName LWord.
  Implicit Types ms : gmap Addr LWord.

  (** *** GetTag with a witness and an observation

      The result is the logical tag, or 0 on a word whose tag may be
      cleared. It is exact under a dereference witness for a word with
      authority or without a heap base. A result of 1 on a word with
      authority observes the claim of its base: by its identifier, or as a
      heap root. The claims are read from any resource [P] that bounds the
      claim map, by [Φc]. *)
  Definition gettag_result (dw : deref_witness) (Φc : gmap Addr AddrClaim → Prop)
      (v : LWord) (z : Z) : Prop :=
    (z = Z.b2z (get_tag v.(lw)) ∨ (z = 0%Z ∧ tag_strippable v)) ∧
    (v.(lprov) = deref_id dw → load_exact_cond v → z = Z.b2z (get_tag v.(lw))) ∧
    (z = 1%Z → ∃ C, Φc C ∧
       ∀ b, heap_authority_base v.(lw) = Some b →
         match v.(lprov) with
         | Some ι => C !! b = Some (Claimed ι)
         | None => C !! b = Some HeapRoot
         end).

  (** The source of GetTag: the written integer is a copy of the logical
      tag, with [gettag_result] under the witness facts. *)
  Lemma gettag_source dw Φc regs lpc src wsrc :
    regs !!ₗ src = Some wsrc →
    lsource_witness_ok (λ R C, deref_witness_ok R dw ∧ Φc C) regs lpc
      (λ S, WInt (Z.b2z (S src && get_tag wsrc.(lw)))) (λ _, true)
      (λ v, ∃ z, v = WInt z ∧ gettag_result dw Φc wsrc z).
  Proof.
    intros Hsrc R C st S Hreg [Hdw HΦc] Hregs _ _.
    split_and!; [apply reg_word_ok_int | rewrite and_tag_true; apply reg_phys_lword_of_word |].
    eexists; split; first done.
    destruct (get_tag wsrc.(lw)) eqn:Ht; last first.
    { rewrite andb_false_r /gettag_result Ht. split_and!; [by left | done | done]. }
    assert (src ≠ cnull) as Hne.
    { intros ->. rewrite llookup_reg_cnull in Hsrc. by simplify_eq. }
    rewrite llookup_reg_not_cnull // in Hsrc.
    destruct (Hregs src wsrc Hsrc) as [Hok Hrel].
    rewrite /gettag_result. split_and!.
    - destruct (S src); first by left; rewrite Ht.
      right. split; first done. apply (reg_phys_tag_strippable R); last done.
      by rewrite and_tag_false in Hrel.
    - intros Hπ Hcond. rewrite -Ht -get_tag_and_tag.
      by rewrite (deref_exact _ _ _ _ Hdw Hπ Hcond Hrel).
    - intros Hz. exists C. split; first done. intros b Hab.
      assert (get_tag (and_tag (S src) wsrc.(lw)) = true) as Htw.
      { rewrite get_tag_and_tag Ht. by destruct (S src). }
      pose proof (reg_phys_observe _ _ _ _ _ _ Hreg Hok Hrel Htw Hab) as Hobs.
      destruct (lprov wsrc); [by destruct Hobs as (? & ? & ? & ?) | done].
  Qed.

  (** The agreement of GetTag: it writes the tag of the copy. *)
  Lemma gettag_agree p lpc regs dst src wsrc :
    regs !!ₗ src = Some wsrc →
    regs_next_agree_strip exec_opt (GetTag dst src) p lpc regs dst
      (λ S, WInt (Z.b2z (S src && get_tag wsrc.(lw)))) 1 (λ _, true).
  Proof.
    intros Hsrc [pc r sr m st td] S _ Hcopy.
    rewrite /regs_effect (exec_opt_Get (GetTag dst src) dst src _ _ _ _ _ _ _ _
                            ltac:(unfold is_Get; tauto) (regs_copy_llookup _ _ _ _ _ Hcopy Hsrc)).
    by rewrite and_tag_true /= get_tag_and_tag.
  Qed.

  Lemma wp_GetTag_obs Ep pc_p pc_g pc_b pc_e pc_a pc_π w dst src regs dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    regs_of (GetTag dst src) ⊆ dom regs →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π ∗
        ▷ pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        ▷ [∗ map] k↦y ∈ regs, k ↦ᵣ y }}}
      Instr Executable @ Ep
    {{{ lpc' regs' retv, RET retv;
        ⌜ (∃ (v : LWord) z, retv = NextIV ∧ regs !!ₗ src = Some v ∧ gettag_result dw Φc v z ∧
             incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = Some lpc' ∧
             regs' = <[dst := WInt z]ₗ> regs) ∨
          (retv = FaultedV ∧ incrementPC (Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) = None ∧
             regs' = regs ∧ lpc' = Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π) ⌝ ∗
        PC ↦ₚ lpc' ∗
        pc_a ↦ₐ{dq} w ∗
        deref_witness_res dw ∗
        P ∗
        [∗ map] k↦y ∈ regs', k ↦ᵣ y }}}.
  Proof.
    iIntros (Hdecode Hvpc Dregs HP φ) "(HPC & Hpc_a & Hdw & HPr & Hmap) Hφ".
    assert (is_Some (regs !!ₗ src)) as [wsrc Hsrc].
    { apply (llookup_reg_of_dom {[dst; src]}); last set_solver+.
      by rewrite /regs_of /operands_of in Dregs. }
    iApply (wp_regs_step _ _ _ _ _ _ _ _ _ _ _ dst _ 1 _ _ (deref_witness_res dw ∗ P)
              (λ R C, deref_witness_ok R dw ∧ Φc C) with "[$HPC $Hpc_a $Hdw $HPr $Hmap]");
      [done | rewrite /regs_instr_ok; by apply sw_of_none | done
      | by apply gettag_source | by apply gettag_agree | | |].
    { destruct (decide (dst = cnull)) as [Hdst | Hdst]; [by left | right].
      rewrite /regs_of /operands_of in Dregs. set_solver. }
    { iIntros (R C) "HR HC [Hdw HPr]".
      iDestruct (deref_witness_lookup with "HR Hdw") as %Hdw.
      by iDestruct (HP with "HC HPr") as %HΦc. }
    iIntros "!>" (lpc' regs' retv) "(%Hout & HPC & Hpc_a & [Hdw HPr] & Hmap)".
    iApply "Hφ". iFrame. iPureIntro.
    rewrite /regs_outcome in Hout.
    destruct (incrementPC_gen _ 1) as [lpc_next |] eqn:Hinc.
    - destruct Hout as (-> & -> & v & (z & -> & Hres) & ->). left. by exists wsrc, z.
    - destruct Hout as (-> & -> & ->). right. by split_and!.
  Qed.

  (** [wp_GetTag_obs] on two distinct registers. *)
  Lemma wp_gettag_obs E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq dw
      (P : iProp Σ) (Φc : gmap Addr AddrClaim → Prop) :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ dst →
    src ≠ cnull →
    dst ≠ cnull →
    (∀ C, addr_alloc_auth C -∗ P -∗ ⌜Φc C⌝) →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_witness_res dw
        ∗ P }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z
          ∗ deref_witness_res dw
          ∗ P
          ∗ ⌜gettag_result dw Φc wsrc z⌝ }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hne Hsrc_null Hcnull HP φ) "(>HPC & >Hpc_a & >Hsrc & >Hdst & Hdw & HPr) Hφ".
    iDestruct (map_of_regs_2 with "Hdst Hsrc") as "[Hmap %]".
    iApply (wp_GetTag_obs _ _ _ _ _ _ _ _ _ _ _ _ dw P Φc
      with "[$HPC $Hpc_a $Hdw $HPr $Hmap]"); eauto.
    { rewrite /regs_of /operands_of !dom_insert_L. set_solver+. }
    iNext. iIntros (lpc' regs' retv) "(%Hspec & HPC & Hpc_a & Hdw & HPr & Hmap)".
    destruct Hspec as [(v & z & -> & Hv & Hres & Hinc & ->) | (-> & Hinc & -> & ->)].
    - incrementPC_inv; simplify_map_eq.
      iRegsMap "Hmap"; eauto.
      iApply "Hφ". iFrame. done.
    - exfalso. incrementPC_inv; simplify_map_eq; eauto; try congruence.
  Qed.

  (** GetTag returns the tag, or 0 on a word whose tag may have been
      cleared. *)
  Lemma wp_gettag_lax E dst src pc_p pc_g pc_b pc_e pc_a pc_π w wsrc wdst pc_a' dq :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ wsrc
        ∗ ▷ dst ↦ᵣ wdst }}}
      Instr Executable @ E
      {{{ z, RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ wsrc
          ∗ dst ↦ᵣ WInt z
          ∗ ⌜z = Z.b2z (get_tag wsrc.(lw)) ∨ (z = 0%Z ∧ tag_strippable wsrc)⌝ }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcnull Hcnull' φ) "(HPC & Hpc_a & >Hsrc & >Hdst) Hφ".
    iDestruct (regname_neq with "Hsrc Hdst") as %Hne.
    iApply (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ DerefNoId emp%I (λ _, True)
      with "[$HPC $Hpc_a $Hsrc $Hdst]");
      [done | done | done | done | done | done | by iIntros | done |].
    iIntros "!>" (z) "(HPC & Hpc_a & Hsrc & Hdst & _ & _ & %Hres)".
    iApply "Hφ". iFrame. iPureIntro. apply Hres.
  Qed.

  (** GetTag returns the tag of a word under the dereference resource of its
      identifier, when it has authority or no heap base. *)
  Lemma wp_gettag_success E dst src pc_p pc_g pc_b pc_e pc_a pc_π w ws πs wdst pc_a' dq q :
    decodeInstrW w.(lw) = GetTag dst src →
    isCorrectPC (Cap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    load_exact_cond (ws @@? πs) →
    src ≠ cnull →
    dst ≠ cnull →
    {{{ ▷ PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a @@? pc_π
        ∗ ▷ pc_a ↦ₐ{dq} w
        ∗ ▷ src ↦ᵣ ws @@? πs
        ∗ ▷ dst ↦ᵣ wdst
        ∗ deref_res πs q }}}
      Instr Executable @ E
      {{{ RET NextIV;
          PC ↦ₚ Cap pc_p pc_g pc_b pc_e pc_a' @@? pc_π
          ∗ pc_a ↦ₐ{dq} w
          ∗ src ↦ᵣ ws @@? πs
          ∗ dst ↦ᵣ WInt (Z.b2z (get_tag ws))
          ∗ deref_res πs q }}}.
  Proof.
    iIntros (Hdecode Hvpc Hpca' Hcond Hsrc_null Hcnull φ)
      "(HPC & Hpc_a & >Hsrc & >Hdst & Hdw) Hφ".
    iDestruct (map_of_regs_2 with "Hsrc Hdst") as "[Hmap %Hne]".
    iDestruct (regs_of_map_2 with "Hmap") as "[Hsrc Hdst]"; first done.
    rewrite deref_res_witness.
    iApply (wp_gettag_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ emp%I (λ _, True)
      with "[$HPC $Hpc_a $Hsrc $Hdst $Hdw]"); eauto.
    iNext. iIntros (z) "(HPC & Hpc_a & Hsrc & Hdst & Hdw & _ & %Hres)".
    destruct Hres as (_ & Hexact & _).
    rewrite (Hexact (eq_sym (deref_id_witness_of _ _)) Hcond).
    iApply "Hφ". iFrame.
  Qed.

End gettag_witness_rules.

(** ** Seal *)

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

(** ** UnSeal *)

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

(** ** Auipcc *)

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
      apply capability_monotonicity.wle_cap; [done | reflexivity | reflexivity | solve_addr | solve_addr | by left].
    - intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
      by rewrite /regs_effect and_tag_true.
  Qed.

  (** On an address overflow, the PC untagged. *)
  Lemma auipcc_next_ok_untagged p0 regs dst imm p g b e a π :
    (a + imm)%a = None →
    regs_next_ok (Auipcc dst imm) p0 (Cap p g b e a @@? π) regs dst (Cap⁻ p g b e a @@? π) 1.
  Proof.
    intros Ha'. exists (λ _, true). split; first by apply lsource_untagged.
    intros φ S Hpc _. cbn [exec_opt]. rewrite Hpc. cbn [lw]. rewrite Ha'.
    by rewrite /regs_effect and_tag_true.
  Qed.
End auipcc_next_ok.

#[export] Hint Resolve auipcc_next_ok | 0 : regs_next_ok_db.
#[export] Hint Resolve auipcc_next_ok_untagged | 1 : regs_next_ok_db.
#[export] Hint Resolve auipcc_next_ok : regs_next_ok_lax_db.
