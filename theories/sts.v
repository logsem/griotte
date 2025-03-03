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
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
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
    (match W !! C with
     | Some WC => (sts_full_std C WC.1)
                 ∗ (sts_full C WC.2.1 WC.2.2)
     | None => False
     end
    )%I.

  (* We will have two kinds of future world relation (here in subset order) :
     - public
     - private
   *)

  Definition related_sts_std_pub (fs gs : STS_std_states A B) : Prop :=
    dom fs ⊆ dom gs ∧
    ∀ i x y, fs !! i = Some x → gs !! i = Some y → rtc (Rpub) x y.

  Definition related_sts_std_priv (fs gs : STS_std_states A B) : Prop :=
    dom fs ⊆ dom gs ∧
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
  Definition related_sts_pub_cview (WC WC' : CVIEW) :=
    related_sts_std_pub WC.1 WC'.1 ∧
    related_sts_pub WC.2.1 WC'.2.1 WC.2.2 WC'.2.2.
  Definition related_sts_pub_world (W W' : WORLD) (C : CmptName) :=
    dom W ⊆ dom W' ∧
    forall WC WC', W !! C = Some WC -> W' !! C = Some WC' -> related_sts_pub_cview WC WC'.
  Definition related_sts_priv_cview (WC WC' : CVIEW) :=
    related_sts_std_priv WC.1 WC'.1 ∧
    related_sts_priv WC.2.1 WC'.2.1 WC.2.2 WC'.2.2.
  Definition related_sts_priv_world (W W' : WORLD) (C : CmptName) :=
    dom W ⊆ dom W' ∧
    forall WC WC', W !! C = Some WC -> W' !! C = Some WC' -> related_sts_priv_cview WC WC'.

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
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
  Implicit Types W : WORLD.

  Lemma gen_sts_init :
    ⊢ |==> ∃ (stsg : STSG A B Σ), ([∗ set] C ∈ CNames, sts_full_world {[C := (∅,(∅,∅))]} C) .
  Proof.
    iAssert ([∗ set] C ∈ CNames, ∃ γsstd, own γsstd (● ∅ : sts_std_stateUR A B))%I as "Hstd".
    admit.
    iAssert ([∗ set] C ∈ CNames, ∃ γs, own γsstd (● ∅ : sts_std_stateUR A B))%I as "Hstd".
    admit.
    (* iAssert ([∗ set] C ∈ CNames, ∃ γsstd, own γsstd (● ∅))%I as "Hstd". *)
    (* admit. *)
    iMod (own_alloc (A:=sts_std_stateUR A B) (● ∅)) as (γsstd) "Hstd". by apply auth_auth_valid.
    (* iMod (own_alloc (A:=sts_stateUR) (● ∅)) as (γs) "Hs". by apply auth_auth_valid. *)
    (* iMod (own_alloc (A:=sts_relUR) (● ∅)) as (γr) "Hr". by apply auth_auth_valid. *)
    (* iModIntro. iExists (Build_STSG _ _ _ _ _ _ _ _ _ _ _ _ _). *)
    (* rewrite /sts_full_world /sts_full_std /sts_full /=. *)
    (* rewrite lookup_insert. *)
    (* rewrite !fmap_empty. iFrame. *)
  Admitted.
  (* Qed. *)

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
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).
  Implicit Types WC : CVIEW.
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

  Lemma related_sts_pub_refl_cview WC : related_sts_pub_cview WC WC.
  Proof. split;[apply related_sts_std_pub_refl|apply related_sts_pub_refl]. Qed.
  Lemma related_sts_priv_refl_cview WC : related_sts_priv_cview WC WC.
  Proof. split;[apply related_sts_std_priv_refl|apply related_sts_priv_refl]. Qed.
  Lemma related_sts_pub_refl_world W C : related_sts_pub_world W W C.
  Proof.
    split;trivial.
    intros; simplify_eq.
    apply related_sts_pub_refl_cview.
  Qed.
  Lemma related_sts_priv_refl_world W C : related_sts_priv_world W W C.
  Proof.
    split;trivial.
    intros; simplify_eq.
    apply related_sts_priv_refl_cview.
  Qed.

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
    split;auto. intros i x y Hx Hy.
    specialize (Hf2 i x y Hx Hy).
    apply rtc_or_intro. auto.
  Qed.

  Lemma related_sts_pub_priv_cview WC WC' :
    related_sts_pub_cview WC WC' → related_sts_priv_cview WC WC'.
  Proof.
    intros [Hrel Hrel'].
    split;[apply related_sts_std_pub_priv|apply related_sts_pub_priv];auto.
  Qed.
  Lemma related_sts_pub_priv_world W W' C :
    related_sts_pub_world W W' C → related_sts_priv_world W W' C.
  Proof.
    intros [Hdom Hpub].
    split;trivial.
    intros WC WC' HWC HWC'.
    apply related_sts_pub_priv_cview.
    by apply Hpub.
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
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
    apply rtc_or_intro; auto.
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
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
    apply rtc_or_intro; auto.
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
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  (* Helper functions for transitivity of sts pairs *)
  Lemma related_sts_pub_priv_trans_cview WC WC' WC'' :
    related_sts_pub_cview WC WC'
    -> related_sts_priv_cview WC' WC''
    -> related_sts_priv_cview WC WC''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_priv_trans with WC'.1; auto.
    - apply related_sts_pub_priv_trans with WC'.2.1 WC'.2.2; auto.
  Qed.
  Lemma related_sts_pub_priv_trans_world W W' W'' C :
    related_sts_pub_world W W' C
    -> related_sts_priv_world W' W'' C
    -> related_sts_priv_world W W'' C.
  Proof.
    intros [Hdom Hpub] [Hdom' Hpriv].
    split; first (etrans;eauto).
    intros WC WC'' HWC HWC''.
    ospecialize (Hdom C _); first (rewrite elem_of_dom; naive_solver).
    rewrite elem_of_dom in Hdom; destruct Hdom as [WC' HWC'].
    eapply related_sts_pub_priv_trans_cview with (WC':= WC').
    + by eapply Hpub.
    + by eapply Hpriv.
  Qed.

  Lemma related_sts_priv_pub_trans_cview WC WC' WC'' :
    related_sts_priv_cview WC WC'
    -> related_sts_pub_cview WC' WC''
    -> related_sts_priv_cview WC WC''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_pub_trans with WC'.1; auto.
    - apply related_sts_priv_pub_trans with WC'.2.1 WC'.2.2; auto.
  Qed.
  Lemma related_sts_priv_pub_trans_world W W' W'' C :
    related_sts_priv_world W W' C
    -> related_sts_pub_world W' W'' C
    -> related_sts_priv_world W W'' C.
  Proof.
    intros [Hdom Hpub] [Hdom' Hpriv].
    split; first (etrans;eauto).
    intros WC WC'' HWC HWC''.
    ospecialize (Hdom C _); first (rewrite elem_of_dom; naive_solver).
    rewrite elem_of_dom in Hdom; destruct Hdom as [WC' HWC'].
    eapply related_sts_priv_pub_trans_cview with (WC':= WC').
    + by eapply Hpub.
    + by eapply Hpriv.
  Qed.

  Lemma related_sts_priv_trans_cview WC WC' WC'' :
    related_sts_priv_cview WC WC'
    -> related_sts_priv_cview WC' WC''
    -> related_sts_priv_cview WC WC''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_priv_trans with WC'.1; auto.
    - apply related_sts_priv_trans with WC'.2.1 WC'.2.2; auto.
  Qed.
  Lemma related_sts_priv_trans_world W W' W'' C :
    related_sts_priv_world W W' C
    -> related_sts_priv_world W' W'' C
    -> related_sts_priv_world W W'' C.
  Proof.
    intros [Hdom Hpub] [Hdom' Hpriv].
    split; first (etrans;eauto).
    intros WC WC'' HWC HWC''.
    ospecialize (Hdom C _); first (rewrite elem_of_dom; naive_solver).
    rewrite elem_of_dom in Hdom; destruct Hdom as [WC' HWC'].
    eapply related_sts_priv_trans_cview with (WC':= WC').
    + by eapply Hpub.
    + by eapply Hpriv.
  Qed.

  Lemma related_sts_pub_trans_cview WC WC' WC'' :
    related_sts_pub_cview WC WC'
    -> related_sts_pub_cview WC' WC''
    -> related_sts_pub_cview WC WC''.
  Proof.
    intros [Hpub_std Hpub_loc] [Hpriv_std Hpriv_loc].
    split.
    - apply related_sts_std_pub_trans with WC'.1; auto.
    - apply related_sts_pub_trans with WC'.2.1 WC'.2.2; auto.
  Qed.
  Lemma related_sts_pub_trans_world W W' W'' C :
    related_sts_pub_world W W' C
    -> related_sts_pub_world W' W'' C
    -> related_sts_pub_world W W'' C.
  Proof.
    intros [Hdom Hpub] [Hdom' Hpriv].
    split; first (etrans;eauto).
    intros WC WC'' HWC HWC''.
    ospecialize (Hdom C _); first (rewrite elem_of_dom; naive_solver).
    rewrite elem_of_dom in Hdom; destruct Hdom as [WC' HWC'].
    eapply related_sts_pub_trans_cview with (WC':= WC').
    + by eapply Hpub.
    + by eapply Hpriv.
  Qed.

  Lemma related_sts_priv_cview_std_sta_is_Some WC WC' i :
    related_sts_priv_cview WC WC' -> is_Some ((WC.1) !! i) -> is_Some ((WC'.1) !! i).
  Proof.
    intros [ [Hdom1 _ ] _] Hsome.
    rewrite -elem_of_dom.
    rewrite -elem_of_dom in Hsome.
    apply elem_of_subseteq in Hdom1. auto.
  Qed.

  Lemma related_sts_priv_cview_std_sta_region_type WC WC' i ρ :
    related_sts_priv_cview WC WC' ->
    (WC.1) !! i = Some ρ ->
    ∃ ρ', (WC'.1) !! i = Some ρ'.
  Proof.
    intros Hrelated Hρ.
    assert (is_Some ((WC'.1) !! i)) as [x Hx].
    { apply related_sts_priv_cview_std_sta_is_Some with WC; eauto. }
    destruct Hrelated as [ [Hdom1 Hrevoked ] _].
    specialize (Hrevoked _ _ _ Hρ Hx). simplify_eq.
    eauto.
  Qed.

  Lemma related_sts_pub_empty_cview WC : related_sts_pub_cview (∅, (∅, ∅)) WC.
  Proof.
    split; cbn.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
    - split;auto.
      + rewrite dom_empty_L; set_solver.
      + intros ; set_solver.
  Qed.

  Lemma related_sts_priv_empty_cview WC : related_sts_priv_cview (∅, (∅, ∅)) WC.
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
    -∗ ⌜ ∃ WC, W !! C = Some WC /\ WC.2.2 !! i = Some (convert_rel Q,convert_rel Q',convert_rel P)⌝.
  Proof.
    rewrite /sts_rel_loc /sts_full_world /sts_full.
    destruct (W !! C) as [WC|]; last (by iIntros "?").
    destruct WC as [Wstd [fs fr]].
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
    -∗ ⌜∃ WC, W !! C = Some WC /\ WC.1 !! a = Some b⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std.
    destruct (W !! C) as [WC|]; last (by iIntros "?").
    destruct WC as [Wsta Wloc].
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
    -∗ ⌜∃ WC, W !! C = Some WC /\ WC.2.1 !! i = Some (encode d)⌝.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_loc.
    destruct (W !! C) as [WC|]; last (by iIntros "?").
    destruct WC as [Wstd [fs fr] ].
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
  Definition std_update_cview (WC : CVIEW) (a : A) (b : B) : CVIEW :=
    (<[ a := b]>WC.1, WC.2).
  Definition loc_alloc_cview (WC : CVIEW) (i : positive) (d : D)
    (r1 r2 r3 : D → D -> Prop) : CVIEW :=
    (WC.1,(<[ i := encode d]>WC.2.1,
          <[ i := (convert_rel r1,convert_rel r2,convert_rel r3)]>WC.2.2)).
  Definition loc_update_cview (WC : CVIEW) (i : positive) (d : D) :=
    (WC.1, ( (<[i := encode d ]>WC.2.1), WC.2.2)).

  Notation "<s[ a := ρ ]s> WC" := (std_update_cview WC a ρ) (at level 10, format "<s[ a := ρ ]s> WC").
  Notation "<l[ a := ρ , r ]l> WC" := (loc_alloc_cview WC a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> WC").
  Notation "<l[ a := ρ ]l> WC" := (loc_update_cview WC a ρ) (at level 10, format "<l[ a := ρ ]l> WC").

  Definition std_update (W : WORLD) (C : CmptName) (a : A) (b : B) : WORLD :=
    match W !! C with
    | Some WC => (<[ C := (<s[a := b ]s> WC) ]> W)
    | None => (<[ C := (<s[a := b ]s> (∅,(∅,∅)) ) ]> W)
    end.

  Definition loc_alloc (W : WORLD) (C : CmptName) (a : positive) (d : D)
    (r1 r2 r3 : D → D -> Prop) : WORLD :=
    match W !! C with
    | Some WC => (<[ C := (<l[ a := d , (r1,(r2,r3)) ]l> WC) ]> W)
    | None => (<[ C := (<l[ a := d , (r1,(r2,r3)) ]l> (∅,(∅,∅))) ]> W)
    end.

  Definition loc_update (W : WORLD) (C : CmptName) (a : positive) (d : D) : WORLD :=
    match W !! C with
    | Some WC => (<[ C := (<l[ a := d ]l> WC) ]> W)
    | None => (<[ C := (<l[ a := d ]l> (∅,(∅,∅))) ]> W)
    end.

  Notation "<s[ ( C , a ) := ρ ]s> W" := (std_update W C a ρ) (at level 10, format "<s[ ( C , a ) := ρ ]s> W").
  Notation "<l[ ( C , a ) := ρ , r ]l> W" := (loc_alloc W C a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ ( C , a ) := ρ , r ]l> W").
  Notation "<l[ ( C , a ) := ρ ]l> W" := (loc_update W C a ρ) (at level 10, format "<l[ ( C , a ) := ρ ]l> W").

  Definition delete_std_cview (WC : CVIEW) a : CVIEW := (delete a WC.1,WC.2).
  Definition delete_std (W : WORLD) (C : CmptName) a : WORLD :=
    match W !! C with
    | Some WC => <[ C := delete_std_cview WC a ]> W
    | None => W
    end.

  (* Some practical shorthands for projections *)
  Definition std_cview (WC : CVIEW) := WC.1.
  Definition loc (WC : CVIEW) := WC.2.
  Definition loc1 (WC : CVIEW) := (loc WC).1.
  Definition loc2 (WC : CVIEW) := (loc WC).2.

  Definition std (W : WORLD) (C : CmptName) :=
    match W !! C with
    | Some WC => std_cview WC
    | None => ∅
    end.

  Definition locWORLD (W : WORLD) (C : CmptName) :=
    match W !! C with
    | Some WC => loc WC
    | None => (∅,∅)
    end.

  Definition loc1WORLD (W : WORLD) (C : CmptName) :=
    match W !! C with
    | Some WC => loc1 WC
    | None => ∅
    end.
  Definition loc2WORLD (W : WORLD) (C : CmptName) :=
    match W !! C with
    | Some WC => loc2 WC
    | None => ∅
    end.

  Lemma sts_dealloc_std W C a b :
    sts_full_world W C ∗ sts_state_std C a b
    ==∗
    sts_full_world (delete_std W C a) C.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std /delete_std.
    destruct (W !! C) as [WC|]; last (by iIntros "[? ?]").
    destruct WC as [fs Wloc].
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
    rewrite lookup_insert.
    iFrame. iModIntro. done.
  Qed.

  Lemma sts_alloc_std_i W C (a : A) b :
    ⌜a ∉ dom (std W C)⌝ -∗ sts_full_world W C ==∗
    sts_full_world (<s[ ( C , a ) := b ]s> W) C ∗ sts_state_std C a b.
  Proof.
    rewrite /sts_full_world /sts_full /sts_state_std /std /std_update /=.
    destruct (W !! C) as [WC|]; last (by iIntros "? ?").
    destruct WC as [fsd Wloc]. rewrite /sts_full_std.
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
    rewrite lookup_insert.
    iFrame. done.
  Qed.

  Lemma sts_alloc_loc W C (d : D) (P Q R : D → D → Prop):
    sts_full_world W C ==∗
    ∃ i, sts_full_world (<l[ (C,i) := d , (P,(Q,R)) ]l> W) C
         ∗ ⌜i ∉ dom (loc1WORLD W C)⌝ ∗ ⌜i ∉ dom (loc2WORLD W C)⌝
         ∗ sts_state_loc C (A:=A) i d ∗ sts_rel_loc C (A:=A) i P Q R.
  Proof.
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc /loc_alloc /loc1WORLD /loc2WORLD.
    destruct (W !! C) as [WC|]; last (by iIntros "?").
    destruct WC as [Wstd [fs fr]].
    iIntros "[Hstd [H1 H2]] /=".
    assert (fresh (dom fs ∪ dom fr) ∉
                    (dom fs ∪ dom fr)) as Hfresh.
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
    iExists _; rewrite lookup_insert ;iFrame.
    repeat iSplit; auto.
  Qed.

  Lemma sts_update_std W C a b b' :
    sts_full_world W C
    -∗ sts_state_std C a b
    ==∗ sts_full_world (<s[ ( C , a ) := b' ]s> W) C ∗ sts_state_std C a b'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_std with "Hsf Hi") as %Hfs.
    destruct Hfs as (WC & HWC & Hfs).
    rewrite /sts_full_world /sts_full /sts_state_std /std_update HWC lookup_insert /=.
    destruct WC as [fsd Wloc].
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
    ==∗ sts_full_world (<l[ (C,i) := d' ]l> W) C ∗ sts_state_loc C (A:=A) i d'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_loc with "Hsf Hi") as %Hfs.
    destruct Hfs as (WC & HWC & Hfs).
    rewrite /sts_full_world /sts_full /sts_rel_loc /sts_state_loc /loc_update HWC lookup_insert /=.
    destruct WC as [Wstd [fs fr]].
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

  Lemma dom_std_update W C a ρ :
    dom W ⊆ dom (<s[(C,a):=ρ]s>W).
  Proof.
    rewrite /std_update.
    destruct (W !! C); rewrite dom_insert_L; set_solver.
  Qed.

  Lemma related_sts_pub_cview_fresh WC a ρ :
    a ∉ dom (std_cview WC) →
    related_sts_pub_cview WC (<s[a:=ρ]s> WC).
  Proof.
    rewrite /std.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;[|apply related_sts_pub_refl].
    rewrite /related_sts_pub. split.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (std_cview WC) a) in Hdom_sta.
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite Hdom_sta in Hx. inversion Hx.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_priv_cview_fresh WC a ρ :
    (forall ρ', rtc (λ x0 y0 : B, Rpub x0 y0 ∨ Rpriv x0 y0) ρ' ρ) ->
    related_sts_priv_cview WC (<s[a:=ρ]s> WC).
  Proof.
    intros Hdom_sta.
    rewrite /related_sts_priv_world /=.
    split;[|apply related_sts_priv_refl].
    rewrite /related_sts_std_priv. split.
    - rewrite dom_insert_L. set_solver.
    -
      (* apply (not_elem_of_dom (std_cview WC) a) in Hdom_sta. *)
      intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite lookup_insert in Hy; simplify_eq.
        apply Hdom_sta.
      + rewrite lookup_insert_ne in Hy;auto.
        rewrite Hx in Hy.
        inversion Hy; subst.
        left.
  Qed.

  Lemma related_sts_pub_world_fresh W C a ρ :
    a ∉ dom (std W C) →
    related_sts_pub_world W (<s[(C,a):=ρ]s> W) C.
  Proof.
    rewrite /std.
    intros Hdom_sta.
    rewrite /related_sts_pub_world /=.
    split;first apply dom_std_update.
    intros WC WC' HWC HWC'.
    rewrite /std_update HWC lookup_insert in HWC'; simplify_eq.
    rewrite HWC in Hdom_sta.
    by apply related_sts_pub_cview_fresh.
  Qed.

  Lemma related_sts_priv_world_fresh W C a ρ :
    (forall ρ', rtc (λ x0 y0 : B, Rpub x0 y0 ∨ Rpriv x0 y0) ρ' ρ) ->
    related_sts_priv_world W (<s[(C,a):=ρ]s> W) C.
  Proof.
    rewrite /std.
    intros Hdom_sta.
    rewrite /related_sts_priv_world /=.
    split;first apply dom_std_update.
    intros WC WC' HWC HWC'.
    rewrite /std_update HWC lookup_insert in HWC'; simplify_eq.
    by apply related_sts_priv_cview_fresh.
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

  Lemma related_sts_pub_cview_fresh_loc WC (i x : positive) r1 r2 :
    i ∉ dom (loc WC).1 →
    i ∉ dom (loc WC).2 →
    related_sts_pub_cview WC (std_cview WC,(<[i:=x]> (loc WC).1, <[i:= (r1,r2)]> (loc WC).2)).
  Proof.
    rewrite /loc. intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) (loc WC).1 i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) (loc WC).2 i) in Hdom_rel.
      intros j r1' r2' r1'' r2'' r3' r3''  Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left.
  Qed.

End STS.

Notation "<s[ a := ρ ]s> WC" := (std_update_cview WC a ρ) (at level 10, format "<s[ a := ρ ]s> WC").
Notation "<l[ a := ρ , r ]l> WC" := (loc_alloc_cview WC a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ a := ρ , r ]l> WC").
Notation "<l[ a := ρ ]l> WC" := (loc_update_cview WC a ρ) (at level 10, format "<l[ a := ρ ]l> WC").
Notation "<s[ ( C , a ) := ρ ]s> W" := (std_update W C a ρ) (at level 10, format "<s[ ( C , a ) := ρ ]s> W").
Notation "<l[ ( C , a ) := ρ , r ]l> W" := (loc_alloc W C a ρ r.1 r.2.1 r.2.2) (at level 10, format "<l[ ( C , a ) := ρ , r ]l> W").
Notation "<l[ ( C , a ) := ρ ]l> W" := (loc_update W C a ρ) (at level 10, format "<l[ ( C , a ) := ρ ]l> W").
