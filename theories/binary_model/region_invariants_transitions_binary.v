From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From cap_machine.binary_model Require Export region_invariants_binary.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.


Section transitions.
  Context {Σ:gFunctors} {memg:memG Σ} {regg:regG Σ} 
          {stsg : STSG Addr region_type Σ} {heapg : heapG Σ}
          `{MachineParameters}.

  Implicit Types fsd gsd hsd : STS_std_states Addr region_type.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

  (* --------------------------------------------------------------------------------- *)
  (* --------------------- TRANSITIVITY LEMMA TO MOVE TO STS.V ----------------------- *)

  Lemma related_sts_pub_pub_plus_trans fs fr gs gr hs hr :
    related_sts_pub fs gs fr gr → related_sts_pub_plus gs hs gr hr →
    related_sts_pub_plus fs hs fr hr.
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

  Lemma related_sts_std_pub_pub_plus_trans fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_std_pub_plus gsd hsd →
    related_sts_std_pub_plus fsd hsd.
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

  Lemma related_sts_pub_pub_plus_trans_world W W' W'' :
    related_sts_pub_world W W' → related_sts_pub_plus_world W' W''
    → related_sts_pub_plus_world W W''.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_pub_pub_plus_trans with W'.1;auto.
    - apply related_sts_pub_pub_plus_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_std_pub_a_trans a fsd gsd hsd :
    related_sts_std_pub fsd gsd → related_sts_a gsd hsd a →
    related_sts_a fsd hsd a.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto. eapply rtc_implies;eauto.
    intros r q Hr. destruct (decide (le_a a i));auto.
  Qed.

  Lemma related_sts_std_a_refl a fsd :
    related_sts_a fsd fsd a.
  Proof.
    apply related_sts_pub_a.
    apply related_sts_std_pub_refl. 
  Qed. 

  Lemma related_sts_std_a_pub_plus_trans a fsd gsd hsd :
    related_sts_a fsd gsd a → related_sts_std_pub_plus gsd hsd →
    related_sts_std_pub_plus fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto. eapply rtc_implies;[|apply Hf2].
    intros r q Hr. destruct (decide (le_a a i));auto.
  Qed.

  Lemma related_sts_std_a_priv_trans a fsd gsd hsd :
    related_sts_a fsd gsd a → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto. eapply rtc_implies;[|apply Hf2].
    intros r q. destruct (decide (le_a a i));auto.
    intros [? | ?];auto. 
  Qed.

  Lemma related_sts_std_pub_plus_priv_trans fsd gsd hsd :
    related_sts_std_pub_plus fsd gsd → related_sts_std_priv gsd hsd →
    related_sts_std_priv fsd hsd.
  Proof.
    intros [Hf1 Hf2] [Hg1 Hg2]; split; try by etrans.
    intros i x y Hx Hy.
    specialize (Hf1 i);
      revert Hf1; rewrite !elem_of_dom; intros Hf1.
    destruct Hf1 as [x0 Hx0]; eauto.
    specialize (Hf2 i x x0 Hx Hx0); simplify_eq.
    specialize (Hg2 i x0 y Hx0 Hy); simplify_eq.
    etrans;eauto. eapply rtc_implies;[|apply Hf2].
    intros r q. intros [? | ?];auto.
  Qed.

  Lemma related_sts_std_pub_plus_trans fsd gsd hsd :
    related_sts_std_pub_plus fsd gsd → related_sts_std_pub_plus gsd hsd →
    related_sts_std_pub_plus fsd hsd.
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

  Lemma related_sts_pub_plus_trans fs fr gs gr hs hr :
    related_sts_pub_plus fs gs fr gr → related_sts_pub_plus gs hs gr hr →
    related_sts_pub_plus fs hs fr hr.
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

  Lemma related_sts_pub_plus_priv_trans fs fr gs gr hs hr :
    related_sts_pub_plus fs gs fr gr → related_sts_priv gs hs gr hr →
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
    etrans;eauto. eapply rtc_implies;[|apply Hrtc];auto.
    intros r q [Hr | Hr];auto. 
  Qed.

  Lemma related_sts_pub_a_trans_world W W' W'' a :
    related_sts_pub_world W W' → related_sts_a_world W' W'' a
    → related_sts_a_world W W'' a.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_pub_a_trans with W'.1;auto.
    - apply related_sts_pub_pub_plus_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_a_pub_plus_trans_world W W' W'' a :
    related_sts_a_world W W' a → related_sts_pub_plus_world W' W''
    → related_sts_pub_plus_world W W''.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_a_pub_plus_trans with a W'.1;auto.
    - apply related_sts_pub_plus_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_a_priv_trans_world W W' W'' a :
    related_sts_a_world W W' a → related_sts_priv_world W' W''
    → related_sts_priv_world W W''.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_a_priv_trans with a W'.1;auto.
    - apply related_sts_pub_plus_priv_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_a_trans_world W W' W'' a :
    related_sts_a_world W W' a → related_sts_a_world W' W'' a →
    related_sts_a_world W W'' a.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_a_trans_left with W'.1 a;auto. done.
    - apply related_sts_pub_plus_trans with W'.2.1 W'.2.2;auto.
  Qed.


  Lemma related_sts_pub_plus_priv_trans_world W W' W'' :
    related_sts_pub_plus_world W W' → related_sts_priv_world W' W'' →
    related_sts_priv_world W W''.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_pub_plus_priv_trans with W'.1;auto.
    - apply related_sts_pub_plus_priv_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_pub_plus_trans_world W W' W'' :
    related_sts_pub_plus_world W W' → related_sts_pub_plus_world W' W'' →
    related_sts_pub_plus_world W W''.
  Proof.
    intros [Hrel Hrel'] [Hrel2 Hrel2'].
    split.
    - apply related_sts_std_pub_plus_trans with W'.1;auto.
    - apply related_sts_pub_plus_trans with W'.2.1 W'.2.2;auto.
  Qed.

  Lemma related_sts_a_refl_world W a :
    related_sts_a_world W W a.
  Proof. 
    split.
    - apply related_sts_std_a_refl.
    - apply related_sts_pub_plus_refl.
  Qed.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)

  Lemma std_rel_pub_Permanent x :
    std_rel_pub Permanent x → x = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Permanent x y :
    x = Permanent →
    rtc std_rel_pub x y → y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_pub_Permanent; auto.
  Qed.

  Lemma std_rel_pub_plus_Permanent x :
    std_rel_pub_plus Permanent x → x = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_plus_rtc_Permanent x y :
    x = Permanent →
    rtc (λ x y : region_type, std_rel_pub x y ∨ std_rel_pub_plus x y) x y →
    y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc as [|x y z Hrel];auto.
    subst. destruct Hrel as [Hpub | Hpubp]. 
    - apply std_rel_pub_Permanent in Hpub. auto.
    - apply std_rel_pub_plus_Permanent in Hpubp. auto.
  Qed.

  Lemma std_rel_priv_Permanent x :
    std_rel_priv Permanent x → x = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Permanent x y :
    x = Permanent →
    rtc std_rel_priv x y → y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Permanent; auto.
  Qed.

  Lemma std_rel_priv_Revoked x :
    std_rel_priv Revoked x → x = Revoked.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Revoked x y :
    x = Revoked →
    rtc std_rel_priv x y → y = Revoked.
  Proof.
    intros Hx Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Revoked; auto.
  Qed.

  Lemma std_rel_priv_Monostatic x g :
    std_rel_priv (Monostatic g) x → x = Monostatic g.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Monostatic x y g :
    x = Monostatic g →
    rtc std_rel_priv x y → y = Monostatic g.
  Proof.
    intros Hx Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Monostatic; auto.
  Qed.

  Lemma std_rel_rtc_Permanent x y :
    x = Permanent →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x y →
    y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc as [|x y z Hrel];auto.
    subst. destruct Hrel as [Hrel | [Hrel | Hrel] ].
    - apply std_rel_pub_Permanent in Hrel. auto.
    - apply std_rel_pub_plus_Permanent in Hrel. auto.
    - apply std_rel_priv_Permanent in Hrel. auto.
  Qed.

  Lemma std_rel_pub_Monotemporary x :
    std_rel_pub Monotemporary x → x = Monotemporary.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Monotemporary x y :
    x = Monotemporary →
    rtc std_rel_pub x y → y = Monotemporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply IHHrtc. apply std_rel_pub_Monotemporary; auto.
  Qed.

  Lemma std_rel_pub_Revoked x :
    std_rel_pub Revoked x → x = Permanent ∨ x = Monotemporary.
  Proof.
    intros Hrel.
    inversion Hrel; auto.
  Qed.

  Lemma std_rel_pub_rtc_Revoked x y :
    x = Revoked →
    rtc std_rel_pub x y → y = Permanent ∨ y = Monotemporary ∨ y = Revoked.
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto.
    apply std_rel_pub_Revoked in H0 as [-> | ->];auto.
    - left. eapply std_rel_pub_rtc_Permanent;eauto.
    - right. left. eapply std_rel_pub_rtc_Monotemporary;eauto.
  Qed.

  Lemma std_rel_pub_Monostatic x g :
    std_rel_pub (Monostatic g) x → x = Monostatic g.
  Proof.
    intros Hrel.
    inversion Hrel. 
  Qed.

  Lemma std_rel_pub_Uninitialized x w :
    std_rel_pub (Uninitialized w) x → x = Monotemporary.
  Proof.
    intros Hrel.
    inversion Hrel. auto. 
  Qed.

  Lemma std_rel_pub_rtc_Uninitialized x y w :
    x = (Uninitialized w) →
    rtc std_rel_pub x y → y = Monotemporary ∨ y = (Uninitialized w).
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto. left.
    apply std_rel_pub_Uninitialized in H0. 
    eapply std_rel_pub_rtc_Monotemporary;eauto.
  Qed.

  Lemma std_rel_pub_rtc_Monostatic x y g :
    x = (Monostatic g) →
    rtc std_rel_pub x y → y = (Monostatic g).
  Proof.
    intros Hx Hrtc.
    induction Hrtc; subst; auto.
    apply std_rel_pub_Monostatic in H0 as ->.
    auto.
  Qed.

  Lemma std_rel_pub_plus_Monostatic x g :
    std_rel_pub_plus (Monostatic g) x → x = Monotemporary.
  Proof.
    intros Hrel; inversion Hrel. auto. Qed.

  Lemma std_rel_pub_plus_Uninitialized x w :
    std_rel_pub_plus (Uninitialized w) x → x = (Uninitialized w).
  Proof.
    intros Hrel; inversion Hrel. Qed.

  Lemma std_rel_pub_plus_Monotemporary x :
    std_rel_pub_plus Monotemporary x → ∃ w, x = Uninitialized w.
  Proof.
    intros Hrel. inversion Hrel. eauto. Qed. 

  Lemma std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized x y :
    x = Monotemporary ∨ (∃ w, x = Uninitialized w) →
    rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y →
    y = Monotemporary ∨ ∃ w, y = Uninitialized w.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;[destruct Hx;eauto|].
    destruct Hx as [-> | [g ->] ].
    - destruct H0 as [Hpub | Hpubp]. 
      + apply std_rel_pub_Monotemporary in Hpub. auto. 
      + apply std_rel_pub_plus_Monotemporary in Hpubp as [g' ->].
        apply IHHrtc. eauto. 
    - destruct H0 as [Hpub | Hpubp]. 
      + apply std_rel_pub_Uninitialized in Hpub. auto. 
      + apply std_rel_pub_plus_Uninitialized in Hpubp as ->.
        apply IHHrtc. eauto. 
  Qed. 

  Lemma std_rel_pub_plus_rtc_Uninitialized x y w :
    x = Uninitialized w →
    rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y →
    y = Monotemporary ∨ (∃ w', y = Uninitialized w').
  Proof.
    intros Hx Hrtc.
    eapply std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized;eauto. 
  Qed. 

  Lemma std_rel_pub_plus_rtc_Monotemporary x y :
    x = Monotemporary →
    rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y →
    y = Monotemporary ∨ ∃ w, y = Uninitialized w.
  Proof.
    intros Hx Hrtc. subst. 
    apply (std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized Monotemporary);eauto. 
  Qed.

  (*
    this lemma does not how if there is only one revoked state, shared between
    Temporary and Monotemporary
   *)
  (* Lemma std_rel_rtc_Temporary x y : *)
  (*   x = Temporary → *)
  (*   rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0 ∨ std_rel_priv x0 y0) x y → *)
  (*   y = Temporary ∨ y = Revoked ∨ y = Permanent ∨ (∃ g, y = Static g). *)
  (* Proof. *)
  (*   intros Hx Hrtc. *)
  (*   induction Hrtc as [|x y z Hrel];auto. *)
  (*   subst. destruct Hrel as [Hrel | [Hrel | Hrel] ]. *)
  (*   - apply std_rel_pub_Temporary in Hrel. auto. *)
  (*   - apply std_rel_pub_plus_Temporary in Hrel. auto. *)
  (*   - apply std_rel_priv_Temporary in Hrel as [-> | [-> | [? ->] ] ];eauto. *)
  (*     + apply std_rel_rtc_Permanent in Hrtc;auto. *)
  (*     +  *)
  (* Qed. *)

End transitions.


