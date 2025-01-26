From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From cap_machine Require Export region_invariants.
From iris.base_logic Require Export invariants na_invariants saved_prop.
Import uPred.


Section transitions.
  Context {Σ:gFunctors}
    {ceriseg:ceriseG Σ}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    `{MP: MachineParameters}.

  Implicit Types fsd gsd hsd : STS_std_states Addr region_type.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Implicit Types W : WORLD.

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

  Lemma std_rel_priv_Frozen x g :
    std_rel_priv (Frozen g) x → x = Frozen g.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Frozen x y g :
    x = Frozen g →
    rtc std_rel_priv x y → y = Frozen g.
  Proof.
    intros Hx Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Frozen; auto.
  Qed.

  Lemma std_rel_rtc_Permanent x y :
    x = Permanent →
    rtc (λ x0 y0 : region_type, std_rel_pub x0 y0 ∨ std_rel_priv x0 y0) x y →
    y = Permanent.
  Proof.
    intros Hx Hrtc.
    induction Hrtc as [|x y z Hrel];auto.
    subst. destruct Hrel as [Hrel | Hrel].
    - apply std_rel_pub_Permanent in Hrel; auto.
    - apply std_rel_priv_Permanent in Hrel; auto.
  Qed.

  Lemma std_rel_pub_Temporary x :
    std_rel_pub Temporary x → x = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Temporary x y :
    x = Temporary →
    rtc std_rel_pub x y → y = Temporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply IHHrtc. apply std_rel_pub_Temporary; auto.
  Qed.

  Lemma std_rel_pub_Revoked x :
    std_rel_pub Revoked x → x = Permanent ∨ x = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel; auto.
  Qed.

  Lemma std_rel_pub_rtc_Revoked x y :
    x = Revoked →
    rtc std_rel_pub x y → y = Permanent ∨ y = Temporary ∨ y = Revoked.
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto.
    apply std_rel_pub_Revoked in H as [-> | ->];auto.
    - left. eapply std_rel_pub_rtc_Permanent;eauto.
    - right. left. eapply std_rel_pub_rtc_Temporary;eauto.
  Qed.

  Lemma std_rel_pub_Frozen x g :
    std_rel_pub (Frozen g) x → x = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel.
    auto.
  Qed.

  Lemma std_rel_pub_rtc_Frozen x y g :
    x = (Frozen g) →
    rtc std_rel_pub x y → (y = Temporary ∨ y = (Frozen g)).
  Proof.
    intros Hx Hrtc.
    inversion Hrtc; subst; auto.
    eapply std_rel_pub_Frozen in H; simplify_eq.
    left.
    eapply std_rel_pub_rtc_Temporary; eauto.
  Qed.

End transitions.
