From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import invariants.
From griotte Require Import stdpp_extra.

Lemma NoDup_of_sepL2_exclusive {Σ : gFunctors} {A B: Type} (l1: list A) (l2: list B) (Φ: A -> B -> iProp Σ):
  (∀ a x1 x2, Φ a x1 -∗ Φ a x2 -∗ False) -∗
  ([∗ list] a;x ∈ l1;l2, Φ a x) -∗
  ⌜NoDup l1⌝.
Proof.
  revert l2. induction l1 as [| a1' l1].
  { iIntros (?) "_ _". iPureIntro. constructor. }
  { iIntros (l2) "HΦ H". destruct l2 as [| a2' l2]; [done|]. cbn. iDestruct "H" as "[Ha1 H]".
    iDestruct (IHl1 with "HΦ H") as %?.
    iAssert (⌜a1' ∉ l1⌝)%I as %?.
    { iIntros (Hin). destruct (list_elem_of_lookup_1 _ _ Hin) as [k ?].
      iDestruct (big_sepL2_length with "H") as %Hlen12.
      destruct (lookup_lt_is_Some_2 l2 k).
      { rewrite -Hlen12 -lookup_lt_is_Some; eauto. }
      iDestruct (big_sepL2_lookup with "H") as "Ha1'"; eauto.
      iApply ("HΦ" with "Ha1 Ha1'"). }
    iPureIntro. by constructor. }
Qed.

Lemma big_sepL_elem_of_extract {Σ : gFunctors} { A : Type } (P Q : A -> iProp Σ) (a : A) (l : list A) :
  a ∈ l ->
  NoDup l ->
  (∀ a, P a -∗ Q a) -∗
  ([∗ list] a ∈ l, P a) -∗
  ∃ l', ⌜ l ≡ₚ a::l' ⌝ ∗ ([∗ list] a ∈ l', P a) ∗ (Q a).
Proof.
  iIntros (Ha_in Hnodup) "Himpl Hl".
  apply elem_of_Permutation in Ha_in as [l' Hl'].
  iExists l'; iFrame "%".
  iEval (setoid_rewrite Hl') in "Hl".
  iDestruct "Hl" as "[Ha $]".
  by iApply "Himpl".
Qed.

Lemma big_sepL2_app'
      (PROP : bi) (A B : Type) (Φ : nat → A → B → PROP) (l1 l2 : list A)
      (l1' l2' : list B) :
  (length l1) = (length l1') →
  (([∗ list] k↦y1;y2 ∈ l1;l1', Φ k y1 y2)
     ∗ ([∗ list] k↦y1;y2 ∈ l2;l2', Φ (length l1 + k) y1 y2))%I
   ≡ ([∗ list] k↦y1;y2 ∈ (l1 ++ l2);(l1' ++ l2'), Φ k y1 y2)%I.
Proof.
  intros Hlenl1.
  iSplit.
  - iIntros "[Hl1 Hl2]". iApply (big_sepL2_app with "Hl1 Hl2").
  - iIntros "Happ".
    iAssert (∃ l0' l0'' : list A,
                ⌜(l1 ++ l2) = l0' ++ l0''⌝
                ∧ ([∗ list] k↦y1;y2 ∈ l0';l1', Φ k y1 y2)
                    ∗ ([∗ list] k↦y1;y2 ∈ l0'';l2', Φ (length l1' + k) y1 y2))%I
      with "[Happ]" as (l0' l0'') "(% & Happl0' & Happl0'')".
    { by iApply (big_sepL2_app_inv_r with "Happ"). }
    iDestruct (big_sepL2_length with "Happl0'") as %Hlen1.
    iDestruct (big_sepL2_length with "Happl0''") as %Hlen2.
    rewrite -Hlenl1 in Hlen1.
    assert (l1 = l0' ∧ l2 = l0'') as [Heq1 Heq2]; first by apply app_inj_1.
    simplify_eq; rewrite Hlenl1.
    iFrame.
Qed.

(* Helper lemma for reasoning about the current state of a region map *)
Lemma big_sepM_exists `{Σ : gFunctors} {A B C : Type} `{EqDecision A, Countable A} (m : gmap A B) (φ : A → C -> B → iProp Σ) :
  (([∗ map] a↦b ∈ m, ∃ c, φ a c b) ⊣⊢ (∃ (m' : gmap A C), [∗ map] a↦c;b ∈ m';m, φ a c b))%I.
Proof.
  iSplit.
  - iIntros "Hmap".
    iInduction (m) as [| a x m Hnone] "IH" using map_ind.
    + iExists empty. done.
    + iDestruct (big_sepM_insert with "Hmap") as "[Hc Hmap]"; auto.
      iDestruct "Hc" as (c) "Hc".
      iDestruct ("IH" with "Hmap") as (m') "Hmap".
      iExists (<[a:=c]> m').
      iApply (big_sepM2_insert_2 with "Hc").
      iFrame.
  - iIntros "Hmap".
    iDestruct "Hmap" as (m') "Hmap".
    iInduction (m) as [| a x m Hnone] "IH" using map_ind forall (m').
    + done.
    + iDestruct (big_sepM2_dom with "Hmap") as %Hdom.
      assert (is_Some (m' !! a)) as [ρ Hρ].
      { apply elem_of_dom. rewrite Hdom dom_insert_L.
        apply elem_of_union_l, elem_of_singleton; auto. }
      rewrite -(insert_id m' a ρ); auto.
      rewrite -insert_delete_eq.
      iDestruct (big_sepM2_insert with "Hmap") as "[Hφ Hmap]";[apply lookup_delete_eq|auto|].
      iApply big_sepM_insert;auto.
      iDestruct ("IH" with "Hmap") as "Hmap". iFrame.
Qed.

Global Instance if_persistent `{PROP:bi} (b: bool) (φ1 φ2: PROP) (H1: Persistent φ1) (H2: Persistent φ2):
  Persistent (if b then φ1 else φ2).
Proof.
  destruct b; auto.
Qed.

Definition if_later_P {Σ : gFunctors} (b: bool) (P: iProp Σ) :=
  (if b then ▷ P else P)%I.

Lemma if_later {Σ : gFunctors} (b : bool) (Q Q' : iProp Σ) :
  (if b then ▷ Q else Q') -∗ ▷ (if b then Q else Q').
Proof. iIntros "H". destruct b;auto. Qed.

Lemma if_dec_later {Σ : gFunctors} {C} {eqdec: Decision C} (Q Q' : iProp Σ) :
  (if (decide C) then ▷ Q else Q') -∗ ▷ (if (decide C) then Q else Q').
Proof. iIntros "H". destruct (decide C);auto. Qed.

Ltac iHide0 irisH coqH :=
  let coqH := fresh coqH in
  match goal with
  | h: _ |- context [ environments.Esnoc _ (INamed irisH) ?prop ] =>
      set (coqH := prop)
  end.

Tactic Notation "iHide" constr(irisH) "as" ident(coqH) :=
  iHide0 irisH coqH.
