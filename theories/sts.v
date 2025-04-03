From iris.algebra Require Import auth agree gmap excl.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From stdpp Require Import finite.
From cap_machine Require Import stdpp_extra.
Import uPred.

Class CmptNameG := CmptNameS {
  CmptName : Type;
  CmptName_eq_dec :: EqDecision CmptName;
  CmptName_countable :: Finite CmptName;
  CNames : gset CmptName;
}.

(** The CMRA for the heap of STS.
    We distinguish between the standard and owned sts. *)

(** For shared resources, we register the state. *)

Definition sts_std_stateUR (A B : Type) {eqD: EqDecision A} {count: Countable A} := authUR (gmapUR A (exclR (leibnizO B))).
Definition STS_std_states (A B : Type) {eqD: EqDecision A} {count: Countable A} : Type := gmap A B.

(** For owned resources, we register the state and the transition relation. *)

Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizO positive))).
Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizO ((positive → positive → Prop) * (positive → positive → Prop) * (positive → positive → Prop))))).

Notation STS_states := (gmap positive positive).
Notation STS_rels := (gmap positive ((positive → positive → Prop) * (positive → positive → Prop) * (positive → positive → Prop ))).

(** Standard STS. *)
(** The Standard STS is made up of three relations *)
Class STS_STD (B : Type) :=
  { Rpub : relation B;
    Rpriv : relation B;
    state_permanent : B -> Prop ; (* set of B that have to stay in the domain of the world *)
    dec_state_permanent : forall b, Decision (state_permanent b);
    state_permanent_reachable : forall b b', ¬ (state_permanent b) -> rtc (λ x y, (Rpub x y ∨ Rpriv x y)) b b' ;
    state_permanent_inv : forall b b', state_permanent b
                                         -> rtc (λ x y, (Rpub x y ∨ Rpriv x y)) b b'
                                         -> state_permanent b' ;
  }.

(** The CMRA for the sts collection. *)
Class STS_preG A B Σ `{EqDecision A, Countable A} :=
  { sts_pre_state_inG :: inG Σ sts_stateUR;
    sts_pre_std_state_inG :: inG Σ (sts_std_stateUR A B);
    sts_pre_rel_inG :: inG Σ sts_relUR; }.

Class STSG A B Σ `{EqDecision A, Countable A} `{CName : CmptNameG} :=
  { sts_state_inG :: inG Σ sts_stateUR;
    sts_std_state_inG :: inG Σ (sts_std_stateUR A B);
    sts_rel_inG :: inG Σ sts_relUR;
    γs_std : CmptName -> gname;
    γs_loc : CmptName -> gname;
    γr_loc : CmptName -> gname;}.

Definition STS_preΣ A B `{EqDecision A, Countable A} :=
  #[ GFunctor sts_stateUR;
     GFunctor (sts_std_stateUR A B);
     GFunctor sts_relUR ].

Instance subG_STS_preΣ A B `{EqDecision A, Countable A} {Σ} `{CName : CmptNameG} :
  subG (STS_preΣ A B) Σ → STS_preG A B Σ.
Proof.
  (* hack: solve_inG does not currently unfold [subG X _] where X has more than
     4 parameters. We have 5. *)
  set f := STS_preΣ A B. unfold STS_preΣ in f.
  solve_inG.
Qed.

Section definitionsS.

  (* A now needs to be comparable, so we can distinquish between higher and lower a's *)
  Context {A B E D: Type} {Σ : gFunctors} {eqa: EqDecision A} {a_compare : Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D}
          {CName : CmptNameG} {stsg : STSG A B Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Definition sts_state_std (C : CmptName) (i : A) (x : B) : iProp Σ
    := own (γs_std C) (◯ {[ i := Excl x ]}).

  Definition sts_state_loc (C : CmptName) (i : positive) (y : D) : iProp Σ
    := own (γs_loc C) (◯ {[ i := Excl (encode y) ]}).

  Definition convert_rel {D : Type} `{Countable D} (R : D → D → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  Definition sts_rel_loc (C : CmptName) (i : positive) (R P Q : D → D → Prop) : iProp Σ :=
    own (γr_loc C) (◯ {[ i := to_agree ((convert_rel R,convert_rel P,convert_rel Q)) ]}).

  Definition sts_full C (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (own (A := sts_stateUR) (γs_loc C) (● (Excl <$> fs))
            ∗ own (A := sts_relUR) (γr_loc C) (● (to_agree <$> fr)))%I.
  Definition sts_full_std C (fs : STS_std_states A B) : iProp Σ
    := own (A := sts_std_stateUR A B) (γs_std C) (● (Excl <$> fs))%I.
  Definition sts_full_world (W : WORLD) (C : CmptName) : iProp Σ :=
    (sts_full_std C W.1) ∗ (sts_full C W.2.1 W.2.2).

  (* We will have two kinds of future world relation (here in subset order) :
     - public
     - private
   *)

  Definition related_sts_std_pub (fs gs : STS_std_states A B) : Prop :=
    dom fs ⊆ dom gs ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (Rpub) x y.

  Definition related_sts_std_priv (fs gs : STS_std_states A B) : Prop :=
    (forall i x, fs !! i = Some x -> state_permanent x -> is_Some (gs !! i) )
    ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (λ x y, (Rpub x y ∨ Rpriv x y)) x y.

  Definition related_sts_pub (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom fs ⊆ dom gs ∧
    dom fr ⊆ dom gr ∧
    ∀ i (r1 r2 r1' r2' r3 r3' : positive → positive → Prop), fr !! i = Some (r1,r2,r3) → gr !! i = Some (r1',r2',r3') →
                       r1 = r1' ∧ r2 = r2' ∧ r3 = r3' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc r1 x y)).

  Definition related_sts_priv (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom fs ⊆ dom gs ∧
    dom fr ⊆ dom gr ∧
    ∀ i (r1 r2 r1' r2' r3 r3' : positive → positive → Prop), fr !! i = Some (r1,r2,r3) → gr !! i = Some (r1',r2',r3') →
                       r1 = r1' ∧ r2 = r2' ∧ r3 = r3' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc (λ x y, (r1 x y ∨ r2 x y ∨ r3 x y)) x y)).

  (* Future world relations are only defined when both world have C *)
  Definition related_sts_pub_world (W W' : WORLD) :=
    related_sts_std_pub W.1 W'.1 ∧
    related_sts_pub W.2.1 W'.2.1 W.2.2 W'.2.2.
  Definition related_sts_priv_world (W W' : WORLD) :=
    related_sts_std_priv W.1 W'.1 ∧
    related_sts_priv W.2.1 W'.2.1 W.2.2 W'.2.2.
  (* NOTE new relation, that is public for standard, but private for custom *)
  Definition related_sts_borrow_world (W W' : WORLD) :=
    related_sts_std_pub W.1 W'.1 ∧
    related_sts_priv W.2.1 W'.2.1 W.2.2 W'.2.2.

  Global Instance sts_rel_loc_Persistent C i R P Q : Persistent (sts_rel_loc C i R P Q).
  Proof. apply _. Qed.

  Global Instance sts_rel_loc_Timeless C i R P Q : Timeless (sts_rel_loc C i R P Q).
  Proof. apply _. Qed.

  Global Instance sts_state_std_Timeless C i x : Timeless (sts_state_std C i x).
  Proof. apply _. Qed.
  Global Instance sts_state_loc_Timeless C i x : Timeless (sts_state_loc C i x).
  Proof. apply _. Qed.

  Global Instance sts_full_Timeless C fs fr : Timeless (sts_full C fs fr).
  Proof. apply _. Qed.
  Global Instance sts_full_world_Timeless W C : Timeless (sts_full_world W C).
  Proof. apply _. Qed.

End definitionsS.

Typeclasses Opaque sts_state_std sts_state_loc sts_rel_loc sts_full
            related_sts_pub related_sts_priv.

Lemma convert_rel_of_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  R x y → convert_rel R (encode x) (encode y).
Proof. rewrite /convert_rel. eauto. Qed.

Lemma rel_of_convert_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  convert_rel R (encode x) (encode y) → R x y.
Proof.
  rewrite /convert_rel. intros (?&?&HH1&HH2&?).
  apply encode_inj in HH1.
  apply encode_inj in HH2. subst; eauto.
Qed.

Section pre_STS.
  Context {A B E D: Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D}
          {CName : CmptNameG}
          {sts_preg: STS_preG A B Σ}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  Lemma gen_sts_std_init :
    ⊢ |==> (∃ γsstd, ([∗ set] C ∈ CNames, own (γsstd C) (● ∅ : sts_std_stateUR A B))).
  Proof.
    induction CNames using set_ind_L.
    iModIntro.
    iExists ( λ C, encode C).
    by iApply big_sepS_empty.
    iMod IHg as (?) "IH".
    iMod (own_alloc (A:=sts_std_stateUR A B) (● ∅)) as (γsstd') "Hstd"
    ; first by apply auth_auth_valid.
    iModIntro.
    iExists (λ C, if (bool_decide (C = x)) then γsstd' else γsstd C).
    iApply (big_sepS_union_2 with "[Hstd]").
    - iApply (big_sepS_singleton).
      by rewrite bool_decide_eq_true_2.
    - iApply (big_sepS_mono with "IH").
      iIntros (C HC) "Hstd".
      rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  Lemma gen_sts_state_init :
    ⊢ |==> (∃ γs, ([∗ set] C ∈ CNames, own (γs C) (● ∅ : sts_stateUR))).
  Proof.
    induction CNames using set_ind_L.
    iModIntro.
    iExists ( λ C, encode C).
    by iApply big_sepS_empty.
    iMod IHg as (?) "IH".
    iMod (own_alloc (A:=sts_stateUR) (● ∅)) as (γs') "Hs"
    ; first by apply auth_auth_valid.
    iModIntro.
    iExists (λ C, if (bool_decide (C = x)) then γs' else γs C).
    iApply (big_sepS_union_2 with "[Hs]").
    - iApply (big_sepS_singleton).
      by rewrite bool_decide_eq_true_2.
    - iApply (big_sepS_mono with "IH").
      iIntros (C HC) "Hs".
      rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  Lemma gen_sts_rel_init :
    ⊢ |==> (∃ γr, ([∗ set] C ∈ CNames, own (γr C) (● ∅ : sts_relUR))).
  Proof.
    induction CNames using set_ind_L.
    iModIntro.
    iExists ( λ C, encode C).
    by iApply big_sepS_empty.
    iMod IHg as (?) "IH".
    iMod (own_alloc (A:=sts_relUR) (● ∅)) as (γr') "Hr"
    ; first by apply auth_auth_valid.
    iModIntro.
    iExists (λ C, if (bool_decide (C = x)) then γr' else γr C).
    iApply (big_sepS_union_2 with "[Hr]").
    - iApply (big_sepS_singleton).
      by rewrite bool_decide_eq_true_2.
    - iApply (big_sepS_mono with "IH").
      iIntros (C HC) "Hr".
      rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  Lemma gen_sts_init :
    ⊢ |==> ∃ (stsg : STSG A B Σ), ([∗ set] C ∈ CNames, sts_full_world (∅,(∅,∅)) C) .
  Proof.
    iMod gen_sts_std_init as (γsstd) "Hstd".
    iMod gen_sts_state_init as (γs) "Hs".
    iMod gen_sts_rel_init as (γr) "Hr".
    iModIntro. iExists (Build_STSG _ _ _ _ _ _ _ _ _ _ γsstd γs γr).
    rewrite /sts_full_world /sts_full_std /sts_full /=.
    iDestruct (big_sepS_sep with "[$Hstd $Hs]") as "H".
    iDestruct (big_sepS_sep with "[$Hr $H]") as "H".
    iApply (big_sepS_mono with "H").
    iIntros (C HC) "(Hstd & Hs & Hr)".
    rewrite !fmap_empty.
    iFrame.
  Qed.

End pre_STS.

Section STS.
  Context {A B E D: Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D} {CName : CmptNameG} {stsg : STSG A B Σ}.
  Implicit Types x y : positive.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types c : E.
  Implicit Types d : D.
  Implicit Types fs gs : STS_states.
  Implicit Types fsd gsd : STS_std_states A B.
  Implicit Types fr_pub fr_priv gr_pub gr_priv : STS_rels.
  Implicit Types R : E → E → Prop.
  Implicit Types Q : D → D → Prop.
  Implicit Types Rp : positive → positive → Prop.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* --------------------- REFLEXIVITY --------------------- *)

  Lemma related_sts_pub_refl fs fr : related_sts_pub fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; [..|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_priv_refl fs fr : related_sts_priv fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; [..|split]; trivial.
    intros; simplify_eq;
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_std_pub_refl fsd : related_sts_std_pub fsd fsd.
  Proof.
    split; trivial.
    intros; simplify_eq.
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_std_priv_refl fsd : related_sts_std_priv fsd fsd.
  Proof.
    split; trivial.
    intros; simplify_eq.
    eauto using rtc_refl.
  Qed.

  Lemma related_sts_pub_refl_world W : related_sts_pub_world W W.
  Proof. split;[apply related_sts_std_pub_refl|apply related_sts_pub_refl]. Qed.
  Lemma related_sts_priv_refl_world W : related_sts_priv_world W W.
  Proof. split;[apply related_sts_std_priv_refl|apply related_sts_priv_refl]. Qed.
  Lemma related_sts_borrow_refl_world W : related_sts_borrow_world W W.
  Proof. split;[apply related_sts_std_pub_refl|apply related_sts_priv_refl]. Qed.

  Lemma related_sts_pub_priv fs fr gs gr :
    related_sts_pub fs gs fr gr → related_sts_priv fs gs fr gr.
  Proof.
    rewrite /related_sts_pub /related_sts_priv.
    intros [Hf1 [Hf2 Hf3]].
    do 2 (split; auto). intros.
    specialize (Hf3 i r1 r2 r1' r2' r3 r3' H H0) as (Hr1 & Hr2 & Hr3 & Hrtc); auto.
    subst. repeat (split;auto). intros.
    specialize (Hrtc x y H1 H2).
    inversion Hrtc.
    - left.
    - right with y0; auto.
      apply rtc_or_intro. apply H4.
  Qed.

  Lemma related_sts_std_pub_priv fsd gsd :
    related_sts_std_pub fsd gsd → related_sts_std_priv fsd gsd.
  Proof.
    intros [Hf1 Hf2].
    split;auto.
    - intros i x Hx Hperm_x.
      rewrite -elem_of_dom.
      apply Hf1.
      rewrite elem_of_dom.
      by exists x.
    - intros i x y Hx Hy.
      specialize (Hf2 i x y Hx Hy).
      apply rtc_or_intro. auto.
  Qed.

  Lemma related_sts_pub_priv_world W W' :
    related_sts_pub_world W W' → related_sts_priv_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_priv|apply related_sts_pub_priv];auto.
  Qed.

  Lemma related_sts_pub_borrow_world W W' :
    related_sts_pub_world W W' → related_sts_borrow_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[done|apply related_sts_pub_priv];auto.
  Qed.

  Lemma related_sts_borrow_priv_world W W' :
    related_sts_borrow_world W W' → related_sts_priv_world W W'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_priv|done];auto.
  Qed.
  (* --------------------- TRANSITIVITY --------------------- *)

  Lemma related_sts_pub_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_pub fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
  Qed.

  Lemma related_sts_std_pub_trans fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_std_pub gsd hsd →
    related_sts_std_pub fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  Lemma related_sts_priv_pub_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_std_priv_pub_trans fsd gsd hsd :
    related_sts_std_priv fsd gsd → related_sts_std_pub gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    - intros i x Hx Hperm_x.
      rewrite -elem_of_dom.
      apply Hg1.
      rewrite elem_of_dom.
      eapply Hf1; done.
    - intros i x y Hx Hy.
      pose proof (dec_state_permanent x) as Hdec_x.
      destruct (decide (state_permanent x)) as [Hperma_x|Hperma_x].
      + specialize (Hf1 i x Hx Hperma_x).
        destruct Hf1 as [x' Hx'].
        specialize (Hf2 i x x' Hx Hx').
        specialize (Hg2 i _ _ Hx' Hy).
        clear -Hf2 Hg2.
        eapply rtc_transitive; eauto.
        eapply rtc_or_intro; eauto.
      + destruct (gsd !! i) as [x'|] eqn:Hx'.
        ++ specialize (Hf2 i x x' Hx Hx').
           specialize (Hg2 i _ _ Hx' Hy).
           eapply rtc_transitive; eauto.
           eapply rtc_or_intro; eauto.
        ++ apply (state_permanent_reachable x y Hperma_x).
  Qed.

  Lemma related_sts_pub_priv_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
    apply rtc_or_intro; auto.
  Qed.

  Lemma related_sts_std_pub_priv_trans fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    - intros i x Hx Hperm_x.
      pose proof Hx as Hx_'.
      eapply (elem_of_dom_2 fsd i x) in Hx.
      eapply Hf1 in Hx.
      rewrite elem_of_dom in Hx.
      destruct Hx as [x' Hx].
      assert (state_permanent x') as Hperm_x'.
      { eapply state_permanent_inv; eauto.
        specialize (Hf2 i x x' Hx_' Hx).
        eapply rtc_or_intro; eauto.
      }
      eapply Hg1; eauto.
    - intros i x y Hx Hy.
      assert (is_Some (gsd !! i)) as [x' Hx'].
      { rewrite -elem_of_dom.
        apply Hf1.
        by rewrite elem_of_dom.
      }
      specialize (Hf2 _ _ _ Hx Hx').
      specialize (Hg2 _ _ _ Hx' Hy).
      eapply rtc_transitive; eauto.
      eapply rtc_or_intro; eauto.
  Qed.

  Lemma related_sts_priv_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_priv gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3]] [Hg1 [Hg2 Hg3]]; split; [|split]; try by etrans.
    intros i r1 r2 r1' r2' r3 r3' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i);
      revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2; eauto. destruct x as [[x1 x2] x3].
    edestruct Hf3 as [Heq1 [Heq2 [Heq3 Hrtc]] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 [Heq3 Hrtc']] ] ; eauto; simplify_eq.
    repeat (split;auto).
    intros x y Hx Hy.
    destruct Hf1;eauto.
    etrans;eauto.
  Qed.

  Lemma related_sts_std_priv_trans fsd gsd hsd :
    related_sts_std_priv fsd gsd → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    - intros i x Hx Hperm_x.
      specialize (Hf1 i x Hx Hperm_x).
      destruct Hf1 as [y Hy].
      specialize (Hf2 i x y Hx Hy).
      pose proof (state_permanent_inv x y Hperm_x Hf2) as Hperm_y.
      by specialize (Hg1 i y Hy Hperm_y).
    - intros i x y Hx Hy.
      pose proof (dec_state_permanent x) as Hdec_x.
      destruct (decide (state_permanent x)) as [Hperma_x|Hperma_x].
      + specialize (Hf1 i x Hx Hperma_x).
        destruct Hf1 as [x' Hx'].
        specialize (Hf2 i x x' Hx Hx').
        specialize (Hg2 i _ _ Hx' Hy).
        clear -Hf2 Hg2.
        eapply rtc_transitive; eauto.
      + destruct (gsd !! i) as [x'|] eqn:Hx'.
        ++ specialize (Hf2 i x x' Hx Hx').
           specialize (Hg2 i _ _ Hx' Hy).
           eapply rtc_transitive; eauto.
        ++ apply (state_permanent_reachable x y Hperma_x).
  Qed.

  (* TODO helper for special *)
  (* Helper functions for transitivity of sts pairs *)
  Lemma related_sts_pub_priv_trans_world W W' W'' :
    related_sts_pub_world W W'
    -> related_sts_priv_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_priv_trans with W'.1; auto.
    - apply related_sts_pub_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_pub_trans_world W W' W'' :
    related_sts_priv_world W W'
    -> related_sts_pub_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_pub_trans with W'.1; auto.
    - apply related_sts_priv_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_priv_trans_world W W' W'' :
    related_sts_priv_world W W'
    -> related_sts_priv_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_trans with W'.1; auto.
    - apply related_sts_priv_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Lemma related_sts_pub_trans_world W W' W'' :
    related_sts_pub_world W W'
    -> related_sts_pub_world W' W''
    -> related_sts_pub_world W W''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_trans with W'.1; auto.
    - apply related_sts_pub_trans with W'.2.1 W'.2.2; auto.
  Qed.

  Definition is_permanent_state W i :=
    ∃ b, W.1 !! i = Some b ∧ state_permanent b.

  Lemma related_sts_priv_world_std_sta_is_Some W W' i :
    related_sts_priv_world W W'
    -> is_permanent_state W i
    -> is_Some ((W.1) !! i)
    -> is_Some ((W'.1) !! i).
  Proof.
    intros [ [Hdom _ ] _] Hperm [x Hx].
    destruct Hperm as [x' [Hx' Hperm_x'] ].
    rewrite Hx' in Hx; simplify_eq.
    by specialize (Hdom i x Hx' Hperm_x').
  Qed.

  (* Lemma related_sts_priv_world_std_sta_region_type W W' i ρ : *)
  (*   related_sts_priv_world W W' -> *)
  (*   (W.1) !! i = Some ρ -> *)
  (*   ∃ ρ', (W'.1) !! i = Some ρ'. *)
  (* Proof. *)
  (*   intros Hrelated Hρ. *)
  (*   assert (is_Some ((W'.1) !! i)) as [x Hx]. *)
  (*   { apply related_sts_priv_world_std_sta_is_Some with W; eauto. } *)
  (*   destruct Hrelated as [ [Hdom1 Hrevoked ] _]. *)
  (*   specialize (Hrevoked _ _ _ Hρ Hx). simplify_eq. *)
  (*   eauto. *)
  (* Qed. *)

  Lemma related_sts_pub_empty_world W : related_sts_pub_world (∅, (∅, ∅)) W.
  Proof.
    split; cbn.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
  Qed.

  Lemma related_sts_priv_empty_world W : related_sts_priv_world (∅, (∅, ∅)) W.
  Proof.
    split; cbn.
    - split;auto.
      + intros ; set_solver.
      + intros ; set_solver.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
  Qed.

  Lemma related_sts_borrow_empty_world W : related_sts_borrow_world (∅, (∅, ∅)) W.
  Proof.
    split; cbn.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
  Qed.

  Lemma sts_full_rel_loc W C i Q Q' P :
    sts_full_world W C
    -∗ sts_rel_loc C (A:=A) i Q Q' P
    -∗ ⌜ W.2.2 !! i = Some (convert_rel Q,convert_rel Q',convert_rel P)⌝.
  Proof.
    rewrite /sts_rel_loc /sts_full_world /sts_full.
    destruct W as [Wstd [fs fr]].
    iIntros "[_ [_ H1]] H2 /=".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR. rewrite /= singleton_included_l;
      intros [z [Hz HR]]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) eqn:Heq; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv;
      simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu. intros Hz'%(to_agree_inj (A:=leibnizO _) p _)%leibniz_equiv.
    naive_solver.
  Qed.

  Lemma sts_full_state_std W C a b :
    sts_full_world W C
    -∗ sts_state_std C a b
    -∗ ⌜W.1 !! a = Some b⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std.
    destruct W as [Wsta Wloc].
    iIntros "[H1 _] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid_discrete;
      iPureIntro.
    specialize (Hv a).
    revert HR; rewrite /= singleton_included_l;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (Wsta !! a) eqn:Heq; rewrite Heq /= in Hz Hv; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.

  Lemma sts_full_state_loc W C i d :
    sts_full_world W C
    -∗ sts_state_loc C (A:=A) i d
    -∗ ⌜W.2.1 !! i = Some (encode d)⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_loc.
    destruct W as [Wstd [fs fr] ].
    iIntros "[_ [H1 _]] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= singleton_included_l;
      intros [z [Hz HR]].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq. rewrite -Hz in HR.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
  Qed.


  (* Definition and notation for updating a standard or local state in the STS collection *)
  Definition std_update (W : WORLD) (a : A) (b : B) : WORLD :=
    (<[ a := b]>W.1, W.2).
  Definition loc_alloc (W : WORLD) (i : positive) (d : D)
    (r1 r2 r3 : D → D -> Prop) : WORLD :=
    (W.1,(<[ i := encode d]>W.2.1,
          <[ i := (convert_rel r1,convert_rel r2,convert_rel r3)]>W.2.2)).
  Definition loc_update (W : WORLD) (i : positive) (d : D) :=
    (W.1, ( (<[i := encode d ]>W.2.1), W.2.2)).

  Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_alloc W a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> W").
  Notation "<l[ a := ρ ]l> W" := (loc_update W a ρ) (at level 10, format "<l[ a := ρ ]l> W").

  Definition delete_std (W : WORLD) a : WORLD := (delete a W.1,W.2).

  (* Some practical shorthands for projections *)
  Definition std (W : WORLD) := W.1.
  Definition loc (W : WORLD) := W.2.
  Definition loc1 (W : WORLD) := (loc W).1.
  Definition loc2 (W : WORLD) := (loc W).2.

  Lemma sts_dealloc_std W C a b :
    sts_full_world W C ∗ sts_state_std C a b
    ==∗
    sts_full_world (delete_std W a) C.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std /delete_std.
    destruct W as [fs Wloc].
    iIntros "[ [Hsta Hloc] Hstate]".
    iCombine "Hsta" "Hstate" as "H1".
    iMod (own_update
            (A := sts_std_stateUR A B)
            _ _
            (● (Excl <$> (delete a fs)))
            with "H1") as "H1".
    { apply auth_update_dealloc.
      rewrite fmap_delete /=.
      apply: delete_singleton_local_update. }
    iFrame. iModIntro. done.
  Qed.

  Lemma sts_alloc_std_i W C (a : A) b :
    ⌜a ∉ dom (std W)⌝ -∗ sts_full_world W C ==∗
    sts_full_world (<s[ a := b ]s> W) C ∗ sts_state_std C a b.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std /std /std_update /=.
    destruct W as [fsd Wloc]. rewrite /sts_full_std.
    iIntros (Hfresh1) "[H1 Hloc] /=".
    iMod (own_update
            (A := sts_std_stateUR A B)
            _ _
            (● (Excl <$> <[a :=b]> fsd)
            ⋅ ◯ {[a := Excl b]})
            with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset A)).
      rewrite dom_fmap. auto. }
    iFrame. done.
  Qed.

  Definition fresh_cus_name (W : WORLD) :=
    match W with | (_, (fs, fr) ) => fresh (dom fs ∪ dom fr) end.

  Lemma sts_alloc_loc W C (d : D) (P Q R : D → D → Prop):
    let i := fresh_cus_name W in
    sts_full_world W C ==∗
    sts_full_world (<l[ i := d , (P,(Q,R)) ]l> W) C
    ∗ ⌜i ∉ dom (loc1 W)⌝ ∗ ⌜i ∉ dom (loc2 W)⌝
    ∗ sts_state_loc C (A:=A) i d ∗ sts_rel_loc C (A:=A) i P Q R.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc /loc_alloc.
    destruct W as [Wstd [fs fr]].
    iIntros "[Hstd [H1 H2]] /=".
    assert (fresh (dom fs ∪ dom fr) ∉ (dom fs ∪ dom fr)) as Hfresh.
    { apply is_fresh. }
    apply not_elem_of_union in Hfresh as [Hfs Hfr].
    iMod (own_update
            (A := sts_stateUR)
            _ _
            (● (Excl <$>
                <[fresh (dom fs ∪ dom fr) := encode d]> fs)
             ⋅ ◯ {[fresh (dom fs ∪ dom fr) := Excl (encode d)]})
           with "H1") as "[H1 Hs]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iMod (own_update
            (A := sts_relUR)
            _ _
            (● (to_agree <$>
                <[fresh (dom fs ∪ dom fr) := (convert_rel P,convert_rel Q,convert_rel R)]> fr)
             ⋅ ◯ {[fresh (dom fs ∪ dom fr) := to_agree (convert_rel P,convert_rel Q,convert_rel R)]})
           with "H2") as "[H2 Hr]".
    { apply auth_update_alloc.
      rewrite fmap_insert /=.
      apply: alloc_singleton_local_update; last done.
      apply (not_elem_of_dom (D := gset positive)).
      rewrite dom_fmap.
      auto. }
    iModIntro.
    iFrame.
    repeat iSplit; auto.
  Qed.

  Lemma sts_alloc_loc_alt W C (d : D) (P Q R : D → D → Prop):
    sts_full_world W C ==∗
    ∃ i, sts_full_world (<l[ i := d , (P,(Q,R)) ]l> W) C
         ∗ ⌜i ∉ dom (loc1 W)⌝ ∗ ⌜i ∉ dom (loc2 W)⌝
         ∗ sts_state_loc C (A:=A) i d ∗ sts_rel_loc C (A:=A) i P Q R.
  Proof.
    iIntros "Hstd".
    iMod (sts_alloc_loc with "Hstd") as "Hstd".
    iModIntro; iFrame.
  Qed.

  Lemma sts_update_std W C a b b' :
    sts_full_world W C
    -∗ sts_state_std C a b
    ==∗ sts_full_world (<s[  a := b' ]s> W) C ∗ sts_state_std C a b'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_std with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_state_std /std_update.
    destruct W as [fsd Wloc].
    iDestruct "Hsf" as "[H1 Hloc] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_std_stateUR A B)
            _ _
            (● (<[a := Excl b']> (Excl <$> fsd))
               ⋅ ◯ {[a := Excl b']})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    iFrame. rewrite -fmap_insert; first iModIntro; iFrame.
  Qed.

  Lemma sts_update_loc W C i d d' :
    sts_full_world W C
    -∗ sts_state_loc C (A:=A) i d
    ==∗ sts_full_world (<l[ i := d' ]l> W) C ∗ sts_state_loc C (A:=A) i d'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_loc with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc /loc_update.
    destruct W as [Wstd [fs fr]].
    iDestruct "Hsf" as "[Hdst [H1 H2]] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode d')]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode d')]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      rewrite lookup_fmap Hfs //=.
      by apply exclusive_local_update. }
    rewrite fmap_insert ; first iModIntro; iFrame.
  Qed.

  Lemma related_sts_pub_world_fresh W a ρ :
    a ∉ dom (std W) →
    related_sts_pub_world W (<s[a:=ρ]s> W).
  Proof.
    rewrite /std.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (std W) a) in Hdom_sta.
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite Hdom_sta in Hx. inversion Hx.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_priv_world_fresh W a ρ :
    (forall ρ', rtc (λ x0 y0 : B, Rpub x0 y0 ∨ Rpriv x0 y0) ρ' ρ) ->
    related_sts_priv_world W (<s[a:=ρ]s> W).
  Proof.
    intros Hdom_sta.
    rewrite /related_sts_priv_world /=.
    split;[|apply related_sts_priv_refl].
    rewrite /related_sts_std_priv. split.
    - intros i x Hx _.
      destruct (decide (a = i)); simplify_map_eq; done.
    - (* apply (not_elem_of_dom (std_world W) a) in Hdom_sta. *)
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite lookup_insert in Hy; simplify_eq.
        apply Hdom_sta.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_fresh (W : STS) i k k':
    i ∉ dom W.1 →
    i ∉ dom W.2 →
    related_sts_pub W.1 (<[i:=k]> W.1) W.2 (<[i:=k']> W.2).
  Proof.
    intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub. split;[|split;[auto|] ].
    - apply dom_insert_subseteq.
    - apply dom_insert_subseteq.
    - apply not_elem_of_dom in Hdom_sta.
       apply not_elem_of_dom in Hdom_rel.
       intros j r1 r2 r1' r2' r3 r3' Hr Hr'.
       destruct (decide (j = i)).
      + subst. rewrite Hr in Hdom_rel. done.
      + rewrite lookup_insert_ne in Hr'; auto.
        rewrite Hr in Hr'. inversion Hr'. repeat (split;auto).
        intros x y Hx Hy.
        rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; inversion Hr'; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_fresh_loc W (i x : positive) r1 r2 :
    i ∉ dom (loc W).1 →
    i ∉ dom (loc W).2 →
    related_sts_pub_world W (std W,(<[i:=x]> (loc W).1, <[i:= (r1,r2)]> (loc W).2)).
  Proof.
    rewrite /loc. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) (loc W).1 i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) (loc W).2 i) in Hdom_rel.
      intros j r1' r2' r1'' r2'' r3' r3''  Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left.
  Qed.

End STS.

Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
Notation "<l[ a := ρ , r ]l> W" := (loc_alloc W a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> W").
Notation "<l[ a := ρ ]l> W" := (loc_update W a ρ) (at level 10, format "<l[ a := ρ ]l> W").
