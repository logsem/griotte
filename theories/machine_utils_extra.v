From Coq Require Import ssreflect Eqdep_dec.
From machine_utils Require Export finz.
From iris.proofmode Require Import proofmode.
From cap_machine Require Export solve_addr stdpp_extra.

Definition withinBounds {z} (b e a : finz z): bool :=
  (b <=? a)%f && (a <? e)%f.

Lemma withinBounds_true_iff {z} (b e a : finz z) :
  withinBounds b e a = true ↔ (b <= a)%f ∧ (a < e)%f.
Proof.
  unfold withinBounds. solve_addr.
Qed.

Lemma withinBounds_le_addr {z} (b e a : finz z):
  withinBounds b e a = true →
  (b <= a)%f ∧ (a < e)%f.
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma isWithinBounds_bounds_alt {z} b e (a0 a1 a2 : finz z) :
  withinBounds  b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 ≤ a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma isWithinBounds_bounds_alt' {z} b e (a0 a1 a2 : finz z) :
  withinBounds b e a0 = true →
  withinBounds b e a2 = true →
  (a0 ≤ a1)%Z ∧ (a1 < a2)%Z →
  withinBounds b e a1 = true.
Proof. rewrite !withinBounds_true_iff. solve_addr. Qed.

Lemma le_addr_withinBounds {z} (b e a : finz z):
  (b <= a)%f → (a < e)%f →
  withinBounds b e a = true .
Proof. rewrite withinBounds_true_iff //. Qed.

Lemma le_addr_withinBounds' {z} (b e a : finz z):
  (b <= a)%f ∧ (a < e)%f →
  withinBounds b e a = true .
Proof. intros [? ?]. rewrite withinBounds_true_iff //. Qed.

Lemma withinBounds_InBounds {z} (b e a : finz z) :
  InBounds b e a →
  withinBounds b e a = true.
Proof.
  intros [? ?]. unfold withinBounds.
  apply andb_true_intro.
  split; [apply Z.leb_le;solve_addr | apply Z.ltb_lt;auto].
Qed.

Definition isWithin {z} (n1 n2 b e: finz z) : bool :=
  ((b <=? n1) && (n2 <=? e))%f.

Lemma isWithin_implies {z} (a0 a1 b e : finz z):
  isWithin a0 a1 b e = true →
  (b <= a0 ∧ a1 <= e)%f.
Proof.
  rewrite /isWithin. solve_addr.
Qed.

Lemma isWithin_of_le {z} (a0 a1 b e : finz z):
  (b <= a0 ∧ a1 <= e)%f →
  isWithin a0 a1 b e = true.
Proof.
  rewrite /isWithin. solve_addr.
Qed.

(* Some lemma's to link the implementations of finz.seq_between and withinBounds *)

Lemma finz_0_dist (finz_bound : Z) (f1 f2 : finz finz_bound):
  finz.dist f1 f2 = 0 → (f2 <= f1)%f.
Proof. rewrite /finz.dist. solve_finz. Qed.

Lemma finz_empty_seq_between:
  ∀ (finz_bound : Z) (f1 f2 : finz finz_bound),
    finz.seq_between f1 f2 = [] → (f2 <= f1)%f.
Proof. intros *. rewrite /finz.seq_between /finz.seq.
  destruct (finz.dist f1 f2) eqn:Heq.
  by apply finz_0_dist in Heq.
  intro HFalse; inversion HFalse.
Qed.

Lemma finz_cons_hd (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
  a :: l = finz.seq_between a0 e0 → a = a0.
Proof.
  intros Heql.
  rewrite /finz.seq_between /finz.seq in Heql. destruct (finz.dist a0 e0); inversion Heql; auto. Qed.

Lemma finz_cons_tl (z : Z) (e0 a0 a : finz z) (l : list (finz z)) :
  a :: l = finz.seq_between a0 e0 → ∃ a1, (a0 + 1 = Some a1)%f ∧ l = finz.seq_between a1 e0.
Proof.
  intros Heql.
  assert (a0 < e0)%f as Hlt. {
    rewrite /finz.seq_between /finz.seq in Heql.
    destruct (decide (a0 < e0)%f) as [Hlt | Hnlt]; first auto.
    assert (finz.dist a0 e0 = 0) as HFalse.
    {  apply finz_dist_0; solve_finz. }
    rewrite HFalse /= in Heql. by exfalso. }
  rewrite finz_seq_between_cons in Heql; auto.
  injection Heql as _ Hl.
  assert (a0 + 1 = Some (a0 ^+ 1))%f as Heq. { solve_finz. }
  eexists ; eauto.
Qed.

Lemma seq_between_dist_Some {z : Z} (b0 e0 a0 : finz z):
  withinBounds b0 e0 a0 = true
  → finz.seq_between b0 e0 !! finz.dist b0 a0 = Some a0.
Proof.
  remember (finz.seq_between b0 e0) as l. revert Heql. generalize b0.
  induction l.
  - intros b1 Heql Hwb.
    symmetry in Heql; apply finz_empty_seq_between in Heql.
    rewrite /withinBounds in Hwb.
    exfalso. solve_finz.
  - intros b1 Heql Hwb.
    destruct (decide (b1 = a0)%f) as [-> | ].
    + apply finz_cons_hd in Heql as ->.
      rewrite /finz.dist. by rewrite -Zminus_diag_reverse /=.
    + assert (b1 < a0)%f as Hlt.
      {rewrite /withinBounds in Hwb. solve_finz. }
      apply finz_cons_tl in Heql as (a1' & Hp1 & Hleq).
      assert (withinBounds a1' e0 a0 = true) as Hwb'. { unfold withinBounds in *; solve_finz. }
      specialize (IHl _ Hleq Hwb') as IHl.
      rewrite lookup_cons_ne_0.
      2 : { rewrite /finz.dist. solve_finz. }
      rewrite -IHl; apply (f_equal (λ a, l !! a)).
      rewrite /finz.dist. solve_finz.
Qed.

Global Instance finz_le_preorder `{finz_bound : Z} : PreOrder (@finz.le finz_bound).
Proof.
  apply Build_PreOrder.
  - rewrite /Reflexive. solve_addr.
  - rewrite /Transitive. solve_addr.
Qed.

Global Instance finz_le_ord `{finz_bound : Z} : Ord (@finz finz_bound) :=
  {| le_a := finz.le;
     le_a_decision := finz_le_dec;
     le_a_preorder := finz_le_preorder |}.

Lemma leb_finz_spec { finz_bound : Z } :
  forall (a1 a2 : (@finz finz_bound)),
  reflect (a1 <= a2)%f (a1 <=? a2)%f.
Proof.
  intros.
  apply Z.leb_spec0.
Qed.
