From iris.algebra Require Import auth agree gmap excl excl_auth gset.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From stdpp Require Import finite.
From griotte Require Import stdpp_extra addresses resources.
From griotte Require Export compartment_names.
Import uPred.

(** The CMRA for the heap of STS.
    We distinguish between the standard and owned sts. The state of a
    standard key is read off the world: it has no ghost state. *)

Definition STS_std_states (A B : Type) {eqD: EqDecision A} {count: Countable A} : Type := gmap A B.

Notation STS_states := (gmap positive positive).
Notation STS_rels := (gmap positive ((positive → positive → Prop) * (positive → positive → Prop))).

(** Standard STS. *)
(** The Standard STS is made up of three relations *)
Class STS_STD (B : Type) :=
  { Rpub : relation B;
    Rpriv : relation B;
  }.
#[export] Hint Mode STS_STD ! : typeclass_instances.

(** A world: the standard STS and the custom STSs (states and relations). *)
Record World (A B : Type) {eqA : EqDecision A} {countA : Countable A} := MkWorld {
  std : leibnizO (STS_std_states A B);
  cus : leibnizO (STS_states * STS_rels);
}.
Arguments MkWorld {_ _ _ _} _ _.
Arguments std {_ _ _ _} _.
Arguments cus {_ _ _ _} _.

#[global] Instance World_inhabited (A B : Type)
  {eqA : EqDecision A} {countA : Countable A} : Inhabited (World A B) :=
  populate (MkWorld ∅ (∅, ∅)).

#[global] Instance World_empty (A B : Type)
  {eqA : EqDecision A} {countA : Countable A} : Empty (World A B) :=
  MkWorld ∅ (∅, ∅).

Section definitionsS.

  (* A now needs to be comparable, so we can distinquish between higher and lower a's *)
  Context {A B E D : Type} {Σ : gFunctors}
          {eqa: EqDecision A} {a_compare : Ord A} {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D}
          {CName : CmptNameG} {th : Thread}
.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (leibnizO (World A B)).

  (* Some practical shorthands for projections *)
  Notation loc W := (cus (W : WORLD)).1.
  Notation wrel W := (cus (W : WORLD)).2.

  Definition convert_rel {D : Type} `{Countable D} (R : D → D → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

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
    ∀ i (rpub rpriv rpub' rpriv' : positive → positive → Prop), fr !! i = Some (rpub,rpriv) → gr !! i = Some (rpub',rpriv') →
                       rpub = rpub' ∧ rpriv = rpriv' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc rpub x y)).

  Definition related_sts_priv (fs gs : STS_states) (fr gr : STS_rels) : Prop :=
    dom fs ⊆ dom gs ∧
    dom fr ⊆ dom gr ∧
    ∀ i (rpub rpriv rpub' rpriv' : positive → positive → Prop), fr !! i = Some (rpub,rpriv) → gr !! i = Some (rpub',rpriv') →
                       rpub = rpub' ∧ rpriv = rpriv' ∧
                       (∀ x y, fs !! i = Some x → gs !! i = Some y → (rtc (λ x y, (rpub x y ∨ rpriv x y)) x y)).

  (* Future world relations are only defined when both world have C *)
  Definition related_sts_pub_world (W W' : WORLD) :=
    related_sts_std_pub (std W) (std W') ∧
    related_sts_pub (loc W) (loc W') (wrel W) (wrel W').

  Definition related_sts_priv_world (W W' : WORLD) :=
    related_sts_std_priv (std W) (std W') ∧
    related_sts_priv (loc W) (loc W') (wrel W) (wrel W').

End definitionsS.

(* Some practical shorthands for projections *)
Notation loc W := (cus W).1.
Notation wrel W := (cus W).2.

#[export] Typeclasses Opaque related_sts_pub related_sts_priv.

Lemma convert_rel_of_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  R x y → convert_rel R (encode x) (encode y).
Proof. rewrite /convert_rel. eauto. Qed.

Section STS.
  Context {A B E D : Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D} {CName : CmptNameG}
          {th : Thread}.
  Implicit Types x y : positive.
  Implicit Types a : A.
  Implicit Types b : B.
  Implicit Types e : E.
  Implicit Types d : D.
  Implicit Types fs gs : STS_states.
  Implicit Types fsd gsd : STS_std_states A B.
  Implicit Types fr_pub fr_priv gr_pub gr_priv : STS_rels.
  Implicit Types fd gd : nat.
  Implicit Types R : E → E → Prop.
  Implicit Types rpub rpriv Q : D → D → Prop.
  Implicit Types Rp : positive → positive → Prop.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (leibnizO (World A B)).
  Implicit Types W : WORLD.

  (* --------------------- REFLEXIVITY --------------------- *)

  Lemma related_sts_pub_refl fs fr : related_sts_pub fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; trivial.
    intros; simplify_eq; eauto using rtc_refl.
  Qed.

  Lemma related_sts_priv_refl fs fr : related_sts_priv fs fs fr fr.
  Proof.
    split; [|split]; trivial.
    intros; simplify_eq.
    split; [|split]; trivial.
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
  Proof. split;[ apply related_sts_std_pub_refl
                | apply related_sts_pub_refl].
  Qed.
  Lemma related_sts_priv_refl_world W : related_sts_priv_world W W.
  Proof. split;[ apply related_sts_std_priv_refl
                | apply related_sts_priv_refl].
  Qed.

  (** Every world is a public future of the empty world. *)
  Lemma related_sts_pub_world_empty W : related_sts_pub_world ∅ W.
  Proof.
    split; cbn.
    - split; [rewrite dom_empty_L; set_solver|]. intros i x y Hx. by rewrite lookup_empty in Hx.
    - split_and!; [rewrite dom_empty_L; set_solver|rewrite dom_empty_L; set_solver|].
      intros i rpub rpriv rpub' rpriv' Hr. by rewrite lookup_empty in Hr.
  Qed.

  Lemma related_sts_pub_priv fs fr gs gr :
    related_sts_pub fs gs fr gr → related_sts_priv fs gs fr gr.
  Proof.
    rewrite /related_sts_pub /related_sts_priv.
    intros [Hf1 [Hf2 Hf3] ].
    do 2 (split; auto). intros i rpub rpriv rpub' rpriv' H H0.
    specialize (Hf3 i rpub rpriv rpub' rpriv' H H0) as (Hrpub & Hrpriv & Hrtc); auto.
    subst. repeat (split;auto).
    intros x y Hpub Hpriv.
    specialize (Hrtc x y Hpub Hpriv).
    inversion Hrtc as [| x0 y0 r Hr Hrtc'].
    - left.
    - right with y0; auto; simplify_eq; apply rtc_or_intro; apply Hrtc'.
  Qed.

  Lemma related_sts_std_pub_priv fsd gsd :
    related_sts_std_pub fsd gsd → related_sts_std_priv fsd gsd.
  Proof.
    intros [Hf1 Hf2].
    split;auto. intros i x y Hx Hy.
    specialize (Hf2 i x y Hx Hy).
    apply rtc_or_intro. auto.
  Qed.

  Lemma related_sts_pub_priv_world W W' :
    related_sts_pub_world W W' → related_sts_priv_world W W'.
  Proof.
    intros (Hrel & Hrel').
    split;[apply related_sts_std_pub_priv|apply related_sts_pub_priv];auto.
  Qed.

  (* --------------------- TRANSITIVITY --------------------- *)

  Lemma related_sts_pub_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_pub fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3] ] [Hg1 [Hg2 Hg3] ]; split; [|split]; try by etrans.
    intros i rpub rpriv rpub' rpriv' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i)
    ; revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2 as [[x1 x2] Hrtc2] ; eauto.
    edestruct Hf3 as [Heq1 [Heq2 Hrtc3] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 Hrtc4] ] ; eauto; simplify_eq.
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
    specialize (Hf1 i); revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  Lemma related_sts_priv_pub_trans fs fr gs gr hs hr :
    related_sts_priv fs gs fr gr → related_sts_pub gs hs gr hr →
    related_sts_priv fs hs fr hr.
  Proof.
    intros [Hf1 [Hf2 Hf3] ] [Hg1 [Hg2 Hg3] ]; split; [|split]; try by etrans.
    intros i rpub rpriv rpub' rpriv' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i); revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2 as [[x1 x2] Hrtc2] ; eauto.
    edestruct Hf3 as [Heq1 [Heq2 Hrtc3] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 Hrtc4] ] ; eauto; simplify_eq.
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
    specialize (Hf1 i); revert Hf1; rewrite !elem_of_dom; intros Hf1.
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
    intros [Hf1 [Hf2 Hf3] ] [Hg1 [Hg2 Hg3] ]; split; [|split]; try by etrans.
    intros i rpub rpriv rpub' rpriv' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i)
    ; revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2 as [[x1 x2] Hrtc2] ; eauto.
    edestruct Hf3 as [Heq1 [Heq2 Hrtc3] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 Hrtc4] ] ; eauto; simplify_eq.
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
    specialize (Hf1 i); revert Hf1; rewrite !elem_of_dom; intros Hf1.
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
    intros [Hf1 [Hf2 Hf3] ] [Hg1 [Hg2 Hg3] ]; split; [|split]; try by etrans.
    intros i rpub rpriv rpub' rpriv' Hfr Hhr.
    specialize (Hf1 i); specialize (Hf2 i)
    ; revert Hf1 Hf2; rewrite !elem_of_dom; intros Hf1 Hf2.
    destruct Hf2 as [[x1 x2] Hrtc2] ; eauto.
    edestruct Hf3 as [Heq1 [Heq2 Hrtc3] ] ; eauto; simplify_eq.
    edestruct Hg3 as [Heq1 [Heq2 Hrtc4] ] ; eauto; simplify_eq.
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
    specialize (Hf1 i); revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto.
  Qed.

  (* Helper functions for transitivity of sts pairs *)
  Lemma related_sts_pub_priv_trans_world W W' W'' :
    related_sts_pub_world W W'
    -> related_sts_priv_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros (Hpub_std & Hpub_loc) (Hpriv_std & Hpriv_loc).
    split.
    - apply related_sts_std_pub_priv_trans with (std W'); auto.
    - apply related_sts_pub_priv_trans with (loc W') (wrel W'); auto.
  Qed.


  Lemma related_sts_priv_pub_trans_world W W' W'' :
    related_sts_priv_world W W'
    -> related_sts_pub_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros (Hpriv_std & Hpriv_loc) (Hpub_std & Hpub_loc).
    split.
    - apply related_sts_std_priv_pub_trans with (std W'); auto.
    - apply related_sts_priv_pub_trans with (loc W') (wrel W'); auto.
  Qed.

  Lemma related_sts_priv_trans_world W W' W'' :
    related_sts_priv_world W W'
    -> related_sts_priv_world W' W''
    -> related_sts_priv_world W W''.
  Proof.
    intros (Hpub_std & Hpub_loc) (Hpriv_std & Hpriv_loc).
    split.
    - apply related_sts_std_priv_trans with (std W'); auto.
    - apply related_sts_priv_trans with (loc W') (wrel W'); auto.
  Qed.

  Lemma related_sts_pub_trans_world W W' W'' :
    related_sts_pub_world W W'
    -> related_sts_pub_world W' W''
    -> related_sts_pub_world W W''.
  Proof.
    intros (Hpub_std & Hpub_loc) (Hpriv_std & Hpriv_loc).
    split.
    - apply related_sts_std_pub_trans with (std W'); auto.
    - apply related_sts_pub_trans with (loc W') (wrel W'); auto.
  Qed.


  (* Definition and notation for updating a standard or local state in the STS collection *)
  Definition std_update (W : WORLD) (a : A) (b : B) : WORLD :=
    MkWorld (<[ a := b]>(std W)) (cus W).
  Definition loc_alloc (W : WORLD) (i : positive) (d : D)
    (rpub rpriv : D → D -> Prop) : WORLD :=
    MkWorld (std W) (<[ i := encode d]>(loc W),
              <[ i := (convert_rel rpub,convert_rel rpriv)]>(wrel W)).
  Definition loc_update (W : WORLD) (i : positive) (d : D) : WORLD :=
    MkWorld (std W) ( (<[i := encode d ]>(loc W)), wrel W).

  Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
  Notation "<l[ a := ρ , r ]l> W" := (loc_alloc W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").
  Notation "<l[ a := ρ ]l> W" := (loc_update W a ρ) (at level 10, format "<l[ a := ρ ]l> W").


  Definition fresh_cus_name (W : WORLD) :=
    match W with | MkWorld _ (fs, fr) => fresh (dom fs ∪ dom fr) end.

  Lemma related_sts_pub_world_fresh W a ρ :
    a ∉ dom (std W) →
    related_sts_pub_world W (<s[a:=ρ]s> W).
  Proof.
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


  Lemma related_sts_pub_world_fresh_loc W (i x : positive) (rpub rpriv : positive -> positive -> Prop) :
    i ∉ dom (loc W) →
    i ∉ dom (wrel W) →
    related_sts_pub_world W (MkWorld (std W) (<[i:=x]> (loc W), <[i:= (rpub,rpriv)]> (wrel W))).
  Proof.
    intros Hdom_sta Hdom_rel.
    rewrite /related_sts_pub_world /=.
    split;[apply related_sts_std_pub_refl|].
    rewrite /related_sts_pub. split;[|split].
    - rewrite dom_insert_L. set_solver.
    - rewrite dom_insert_L. set_solver.
    - apply (not_elem_of_dom (D:=gset positive) (loc W) i) in Hdom_sta.
      apply (not_elem_of_dom (D:=gset positive) (wrel W) i) in Hdom_rel.
      intros j rpub' rpriv' rpub'' rpriv'' Hr' Hr''.
      destruct (decide (j = i)).
      + subst. rewrite Hdom_rel in Hr'. inversion Hr'.
      + simplify_map_eq. repeat split;auto.
        intros x' y Hx' Hy. simplify_map_eq. left.
  Qed.

  Lemma related_sts_priv_world_loc_update
    (W : WORLD) (i : positive) (d d' : D)
    (rpub rpriv : positive -> positive -> Prop)
    :
    loc W !! i = Some (encode d) ->
    wrel W !! i = Some (rpub,rpriv) ->
    (rpub (encode d) (encode d') ∨ rpriv (encode d) (encode d')) ->
    related_sts_priv_world W (<l[i:=d']l>W).
  Proof.
    intros Hloc Hrel Hr.
    split; first apply related_sts_std_priv_refl.
    split;[set_solver+|split;[set_solver+|] ].
    intros ???????; cbn in *; simplify_eq.
    repeat (split;first done).
    intros ????; cbn in *; simplify_eq.
    destruct (decide (i = i0)); simplify_map_eq.
    - by apply rtc_once.
    - by apply rtc_refl.
  Qed.

End STS.

Notation "<s[ a := ρ ]s> W" := (std_update W a ρ) (at level 10, format "<s[ a := ρ ]s> W").
Notation "<l[ a := ρ , r ]l> W" := (loc_alloc W a ρ r.1 r.2) (at level 10, format "<l[ a := ρ , r ]l> W").
Notation "<l[ a := ρ ]l> W" := (loc_update W a ρ) (at level 10, format "<l[ a := ρ ]l> W").
