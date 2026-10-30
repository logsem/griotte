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

(** For owned resources, we register the state and the transition relation. *)

Definition sts_stateUR := authUR (gmapUR positive (exclR (leibnizO positive))).
Definition sts_relUR :=
  authUR (gmapUR positive (agreeR (leibnizO ((positive → positive → Prop) * (positive → positive → Prop) )))).

Notation STS_states := (gmap positive positive).
Notation STS_rels := (gmap positive ((positive → positive → Prop) * (positive → positive → Prop))).

(** Standard STS. *)
(** The Standard STS is made up of three relations *)
Class STS_STD (B : Type) :=
  { Rpub : relation B;
    Rpriv : relation B;
  }.
#[export] Hint Mode STS_STD ! : typeclass_instances.


(** The CMRA for the sts collection: the custom STSs. *)
Class STS_preG (Σ : gFunctors) :=
  { sts_pre_state_inG :: inG Σ sts_stateUR;
    sts_pre_rel_inG :: inG Σ sts_relUR; }.
#[export] Hint Mode STS_preG - : typeclass_instances.

(** The custom STSs of a thread and a compartment. *)
Class STSG (Σ : gFunctors) `{CName : CmptNameG} :=
  { sts_state_inG :: inG Σ sts_stateUR;
    sts_rel_inG :: inG Σ sts_relUR;
    γs_loc : Thread -> CmptName -> gname;
    γr_loc : Thread -> CmptName -> gname;
}.
#[export] Hint Mode STSG - - : typeclass_instances.

Definition STS_preΣ :=
  #[ GFunctor sts_stateUR;
     GFunctor sts_relUR
].

#[export] Instance subG_STS_preΣ {Σ} :
  subG STS_preΣ Σ → STS_preG Σ.
Proof. solve_inG. Qed.

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
          {CName : CmptNameG} {stsg : STSG Σ} {th : Thread}
.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (leibnizO (World A B)).

  (* Some practical shorthands for projections *)
  Notation loc W := (cus (W : WORLD)).1.
  Notation wrel W := (cus (W : WORLD)).2.

  (** The custom STSs belong to the section's thread [th]. *)
  Definition sts_state_loc_def (C : CmptName) (i : positive) (y : D) : iProp Σ
    := own (γs_loc th C) (◯ {[ i := Excl (encode y) ]}).
  #[local] Definition sts_state_loc_aux : seal (@sts_state_loc_def). Proof. by eexists. Qed.
  Definition sts_state_loc := sts_state_loc_aux.(unseal).
  #[local] Definition sts_state_loc_unseal : @sts_state_loc = @sts_state_loc_def := sts_state_loc_aux.(seal_eq).

  Definition convert_rel {D : Type} `{Countable D} (R : D → D → Prop) : positive → positive → Prop :=
    λ x y, ∃ a b, x = encode a ∧ y = encode b ∧ R a b.

  Definition sts_rel_loc_def (C : CmptName) (i : positive) (rpub rpriv : D → D → Prop) : iProp Σ :=
    own (γr_loc th C) (◯ {[ i := to_agree ((convert_rel rpub,convert_rel rpriv)) ]}).
  #[local] Definition sts_rel_loc_aux : seal (@sts_rel_loc_def). Proof. by eexists. Qed.
  Definition sts_rel_loc := sts_rel_loc_aux.(unseal).
  #[local] Definition sts_rel_loc_unseal : @sts_rel_loc = @sts_rel_loc_def := sts_rel_loc_aux.(seal_eq).

  Definition sts_full_def C (fs : STS_states) (fr : STS_rels) : iProp Σ
    := (own (A := sts_stateUR) (γs_loc th C) (● (Excl <$> fs))
            ∗ own (A := sts_relUR) (γr_loc th C) (● (to_agree <$> fr)))%I.
  #[local] Definition sts_full_aux : seal (@sts_full_def). Proof. by eexists. Qed.
  Definition sts_full := sts_full_aux.(unseal).
  #[local] Definition sts_full_unseal : @sts_full = @sts_full_def := sts_full_aux.(seal_eq).
  Definition sts_full_world (W : WORLD) (C : CmptName) : iProp Σ :=
    sts_full C (loc W) (wrel W).

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

  #[global] Instance sts_rel_loc_Persistent C i rpub rpriv : Persistent (sts_rel_loc C i rpub rpriv).
  Proof. rewrite sts_rel_loc_unseal /sts_rel_loc_def. apply _. Qed.

  #[global] Instance sts_rel_loc_Timeless C i rpub rpriv : Timeless (sts_rel_loc C i rpub rpriv).
  Proof. rewrite sts_rel_loc_unseal /sts_rel_loc_def. apply _. Qed.

  #[global] Instance sts_state_loc_Timeless C i x : Timeless (sts_state_loc C i x).
  Proof. rewrite sts_state_loc_unseal /sts_state_loc_def. apply _. Qed.

  #[global] Instance sts_full_Timeless C fs fr : Timeless (sts_full C fs fr).
  Proof. rewrite sts_full_unseal /sts_full_def. apply _. Qed.
  #[global] Instance sts_full_world_Timeless W C : Timeless (sts_full_world W C).
  Proof. apply _. Qed.
End definitionsS.

(* Some practical shorthands for projections *)
Notation loc W := (cus W).1.
Notation wrel W := (cus W).2.

#[export] Typeclasses Opaque related_sts_pub related_sts_priv.

Lemma convert_rel_of_rel {A} `{EqDecision A, Countable A} (R: A -> A -> Prop) x y:
  R x y → convert_rel R (encode x) (encode y).
Proof. rewrite /convert_rel. eauto. Qed.

(** One name per user thread: [nth k xs d] names the user thread [k], for
    [k < nthreads]. *)
Lemma alloc_thread_names {Σ : gFunctors} {X : Type} (P : X → iProp Σ) (d : X) (nthreads : nat) :
  (⊢ |==> ∃ x, P x) →
  ⊢ |==> ∃ xs : list X, [∗ list] k ∈ seq 0 nthreads, P (nth k xs d).
Proof.
  intros Halloc.
  assert (⊢ |==> ∃ xs : list X, ⌜length xs = nthreads⌝ ∗ [∗ list] k ∈ seq 0 nthreads, P (nth k xs d))
    as Hn; last first.
  { iMod Hn as (xs) "[_ Hxs]". by iExists xs. }
  induction nthreads as [|nthreads IH].
  - iModIntro. iExists []. by iSplit.
  - iMod IH as (xs Hlen) "Hxs".
    iMod Halloc as (x) "Hx".
    iModIntro. iExists (xs ++ [x]).
    rewrite length_app Hlen (seq_S nthreads 0) big_sepL_app big_sepL_singleton /=.
    iSplit; first (iPureIntro; lia).
    rewrite -{3}Hlen nth_middle. iFrame "Hx".
    iApply (big_sepL_impl with "Hxs"). iIntros "!>" (i k Hk) "H".
    apply lookup_seq in Hk as [-> Hi]. rewrite app_nth1 //; lia.
Qed.

Section pre_STS.
  Context {A B E D : Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D}
          {CName : CmptNameG}
          {sts_preg: STS_preG Σ}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states A B)).
  Notation WORLD := (leibnizO (World A B)).
  Implicit Types W : WORLD.

  Lemma gen_sts_state_init :
    ⊢ |==> (∃ γs, ([∗ set] C ∈ CNames, own (γs C) (● ∅ : sts_stateUR))).
  Proof.
    induction CNames as [|C CNames HCNames IHg] using set_ind_L.
    - iModIntro.
      iExists ( λ C, encode C).
      by iApply big_sepS_empty.
    - iMod IHg as (γs) "IH".
      iMod (own_alloc (A:=sts_stateUR) (● ∅)) as (γs') "Hs"
      ; first by apply auth_auth_valid.
      iModIntro.
      iExists (λ C', if (bool_decide (C' = C)) then γs' else γs C').
      iApply (big_sepS_union_2 with "[Hs]").
      + iApply (big_sepS_singleton).
        by rewrite bool_decide_eq_true_2.
      + iApply (big_sepS_mono with "IH").
        iIntros (C' HC') "Hs".
        rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  Lemma gen_sts_rel_init :
    ⊢ |==> (∃ γr, ([∗ set] C ∈ CNames, own (γr C) (● ∅ : sts_relUR))).
  Proof.
    induction CNames as [|C CNames HCNames IHg] using set_ind_L.
    - iModIntro.
      iExists ( λ C, encode C).
      by iApply big_sepS_empty.
    - iMod IHg as (γr) "IH".
      iMod (own_alloc (A:=sts_relUR) (● ∅)) as (γr') "Hr"
      ; first by apply auth_auth_valid.
      iModIntro.
      iExists (λ C', if (bool_decide (C' = C)) then γr' else γr C').
      iApply (big_sepS_union_2 with "[Hr]").
      + iApply (big_sepS_singleton).
        by rewrite bool_decide_eq_true_2.
      + iApply (big_sepS_mono with "IH").
        iIntros (C' HC') "Hr".
        rewrite bool_decide_eq_false_2; [done|set_solver].
  Qed.

  (** The custom STSs of the user threads [k], for [k < nthreads]: one
      pair of names each. The context-switch thread and the other user
      threads share a pair of names that is allocated and dropped. *)
  Lemma gen_sts_init (nthreads : nat) :
    ⊢ |==> ∃ (stsg : STSG Σ),
      [∗ list] k ∈ seq 0 nthreads, [∗ set] C ∈ CNames,
        sts_full_world (th := UserThread k) (MkWorld ∅ (∅,∅) : World A B) C.
  Proof.
    set (Pn := λ γ : (CmptName → gname) * (CmptName → gname),
      ([∗ set] C ∈ CNames, own (γ.1 C) (● ∅ : sts_stateUR) ∗ own (γ.2 C) (● ∅ : sts_relUR))%I).
    assert (⊢ |==> ∃ γ, Pn γ) as Halloc.
    { iMod gen_sts_state_init as (γs) "Hs".
      iMod gen_sts_rel_init as (γr) "Hr".
      iModIntro. iExists (γs, γr). rewrite /Pn /=.
      iApply big_sepS_sep. iFrame. }
    iMod Halloc as ([γsd γrd]) "_".
    iMod (alloc_thread_names Pn (γsd, γrd) nthreads Halloc) as (γss) "Hn".
    iModIntro.
    iExists {| sts_state_inG := _; sts_rel_inG := _;
               γs_loc := λ th, match th with UserThread k => nth k (map fst γss) γsd | CtxSwitch => γsd end;
               γr_loc := λ th, match th with UserThread k => nth k (map snd γss) γrd | CtxSwitch => γrd end |}.
    iApply (big_sepL_impl with "Hn"). iIntros "!>" (i k _) "Hk".
    rewrite /sts_full_world sts_full_unseal /sts_full_def /Pn /=.
    rewrite -(map_nth fst γss (γsd, γrd) k) -(map_nth snd γss (γsd, γrd) k) /= !fmap_empty.
    done.
  Qed.

End pre_STS.

Section STS.
  Context {A B E D : Type} {Σ : gFunctors} {eqa: EqDecision A} {compare_a: Ord A}
          {count: Countable A}
          {sts_std: STS_STD B} {eqc : EqDecision E} {countC: Countable E}
          {eqd : EqDecision D} {countD: Countable D} {CName : CmptNameG} {stsg : STSG Σ}
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




  Lemma sts_full_rel_loc W C i rpub rpriv:
    sts_full_world W C
    -∗ sts_rel_loc C i rpub rpriv
    -∗ ⌜ wrel W !! i = Some (convert_rel rpub,convert_rel rpriv)⌝.
  Proof.
    rewrite sts_rel_loc_unseal /sts_rel_loc_def /sts_full_world sts_full_unseal /sts_full_def.
    destruct W as [Wstd [fs fr] ].
    iIntros "[_ H1] H2 /=".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR. rewrite /= singleton_included_l;
      intros [z [Hz HR] ]; revert HR; rewrite Some_included_total; intros HR.
    rewrite lookup_fmap in Hz, Hv.
    destruct (fr !! i) as [p|] eqn:Heq; last by inversion Hz.
    revert Hv; rewrite Hz; intros [u Hu]%to_agree_uninj.
    revert HR; rewrite -Hu; intros HR%to_agree_included%leibniz_equiv; simplify_eq.
    inversion Hz as [? ? Hz'|]; simplify_eq.
    revert Hz'; rewrite -Hu. intros Hz'%(to_agree_inj (A:=leibnizO _) p _)%leibniz_equiv.
    naive_solver.
  Qed.

  Lemma sts_full_state_loc W C i d :
    sts_full_world W C
    -∗ sts_state_loc C i d
    -∗ ⌜loc W !! i = Some (encode d)⌝.
  Proof.
    rewrite /sts_full_world sts_full_unseal /sts_full_def sts_state_loc_unseal /sts_state_loc_def.
    destruct W as [Wstd [fs gs] ].
    iIntros "[H1 _] H2".
    iDestruct (own_valid_2 with "H1 H2") as %[HR Hv]%auth_both_valid_discrete;
      iPureIntro.
    specialize (Hv i).
    revert HR; rewrite /= singleton_included_l;
      intros [z [Hz HR] ].
    rewrite lookup_fmap in Hz Hv.
    destruct (fs !! i) eqn:Heq; last by inversion Hz.
    apply leibniz_equiv in Hz; simplify_eq. rewrite -Hz in HR.
    apply Some_included_exclusive in HR; auto; last by typeclasses eauto.
    apply leibniz_equiv in HR; simplify_eq; eauto.
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

  Lemma fresh_name_notin (W : WORLD) (ι : positive) :
    ι ∈ dom (loc W) ∨ ι ∈ dom (wrel W)
    -> ι ≠ fresh_cus_name W.
  Proof.
    intros Hι.
    destruct W as [Wsta [ Wcus_loc Wcus_rel ] ]; cbn in *.
    pose proof ( is_fresh ( (dom Wcus_loc ∪ dom Wcus_rel) ) ).
    set_solver.
  Qed.

  Lemma sts_alloc_loc W C (d : D) (rpub rpriv : D → D → Prop):
    let i := fresh_cus_name W in
    sts_full_world W C ==∗
    sts_full_world (<l[ i := d , (rpub,rpriv) ]l> W) C
    ∗ ⌜i ∉ dom (loc W)⌝ ∗ ⌜i ∉ dom (wrel W)⌝
    ∗ sts_state_loc C i d ∗ sts_rel_loc C i rpub rpriv.
  Proof.
    rewrite /sts_full_world sts_full_unseal /sts_full_def sts_rel_loc_unseal /sts_rel_loc_def sts_state_loc_unseal /sts_state_loc_def /loc_alloc.
    destruct W as [Wstd [fs fr] ].
    iIntros "[H1 H2] /=".
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
                <[fresh (dom fs ∪ dom fr) := (convert_rel rpub,convert_rel rpriv)]> fr)
             ⋅ ◯ {[fresh (dom fs ∪ dom fr) := to_agree (convert_rel rpub,convert_rel rpriv)]})
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


  Lemma sts_update_loc W C i d d' :
    sts_full_world W C
    -∗ sts_state_loc C i d
    ==∗ sts_full_world (<l[ i := d' ]l> W) C ∗ sts_state_loc C i d'.
  Proof.
    iIntros "Hsf Hi".
    iDestruct (sts_full_state_loc with "Hsf Hi") as %Hfs.
    rewrite /sts_full_world sts_full_unseal /sts_full_def sts_state_loc_unseal /sts_state_loc_def /loc_update.
    destruct W as [Wstd [fs fr] ].
    iDestruct "Hsf" as "[H1 H2] /=".
    iCombine "H1" "Hi" as "H1".
    iMod (own_update (A := sts_stateUR)
            _ _
            (● (<[i := Excl (encode d')]> (Excl <$> fs))
               ⋅ ◯ {[i := Excl (encode d')]})
            with "H1") as "[H1 Hs]".
    { apply auth_update.
      apply: singleton_local_update; eauto.
      + rewrite lookup_fmap Hfs //=.
      + by apply exclusive_local_update.
    }
    rewrite fmap_insert ; first iModIntro; iFrame.
  Qed.

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

  Lemma related_sts_priv_world_fresh W a ρ :
    (forall ρ', rtc (λ x0 y0 : B, Rpub x0 y0 ∨ Rpriv x0 y0) ρ' ρ) ->
    related_sts_priv_world W (<s[a:=ρ]s> W).
  Proof.
    intros Hdom_sta.
    rewrite /related_sts_priv_world /=.
    split;[|apply related_sts_priv_refl].
    rewrite /related_sts_std_priv. split.
    - rewrite dom_insert_L; set_solver.
    - intros i x y Hx Hy.
      destruct (decide (a = i)).
      + subst. rewrite lookup_insert_eq in Hy; simplify_eq.
        apply Hdom_sta.
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
