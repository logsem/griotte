From cap_machine Require Export cap_lang sts.
From stdpp Require Import base.

Section region_invariants_definitions.

  (* We will first define the standard STS for the shared part of the heap *)
  Inductive region_type :=
  | Temporary
  | Permanent
  | Revoked.

  Global Instance LeibnizEquiv_region_type : @LeibnizEquiv region_type (@eq region_type).
  Proof. rewrite /LeibnizEquiv; intros ? ? ?; done. Defined.

  Inductive std_rel_pub : region_type -> region_type -> Prop :=
  | Std_pub_Revoked_Temporary : std_rel_pub Revoked Temporary
  | Std_pub_Revoked_Permanent : std_rel_pub Revoked Permanent.

  Inductive std_rel_priv : region_type -> region_type -> Prop :=
  | Std_priv_Temporary_Revoked : std_rel_priv Temporary Revoked
  | Std_priv_Temporary_Permanent : std_rel_priv Temporary Permanent.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)

  Lemma std_rel_pub_Permanent (ρ : region_type) :
    std_rel_pub Permanent ρ → ρ = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_pub_Permanent; auto.
  Qed.

  Lemma std_rel_priv_Permanent (ρ : region_type) :
    std_rel_priv Permanent ρ → ρ = Permanent.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc std_rel_priv ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Permanent; auto.
  Qed.

  Lemma std_rel_Permanent (ρ : region_type) :
    (std_rel_pub Permanent ρ ∨ std_rel_priv Permanent ρ) → ρ = Permanent.
  Proof.
    intros Hrel.
    destruct Hrel.
    + by apply std_rel_pub_Permanent.
    + by apply std_rel_priv_Permanent.
  Qed.

  Lemma std_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc (λ x y : region_type, std_rel_pub x y ∨ std_rel_priv x y) ρ1 ρ2 → ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_Permanent; auto.
  Qed.

  Lemma std_rel_priv_Revoked (ρ : region_type) :
    std_rel_priv Revoked ρ → ρ = Revoked.
  Proof.
    intros Hrel.
    inversion Hrel; done.
  Qed.

  Lemma std_rel_priv_rtc_Revoked (ρ1 ρ2 : region_type) :
    ρ1 = Revoked →
    rtc std_rel_priv ρ1 ρ2 → ρ2 = Revoked.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc;auto.
    subst. apply IHHrtc. apply std_rel_priv_Revoked; auto.
  Qed.

  Lemma std_rel_rtc_Permanent (ρ1 ρ2 : region_type) :
    ρ1 = Permanent →
    rtc (λ ρ0 ρ0' : region_type, std_rel_pub ρ0 ρ0' ∨ std_rel_priv ρ0 ρ0') ρ1 ρ2 →
    ρ2 = Permanent.
  Proof.
    intros Hρ1 Hrtc.
    induction Hrtc as [|ρ0 ρ1 ρ2 Hrel];auto.
    subst. destruct Hrel as [Hrel | Hrel].
    - apply std_rel_pub_Permanent in Hrel; auto.
    - apply std_rel_priv_Permanent in Hrel; auto.
  Qed.

  Lemma std_rel_pub_Temporary (ρ : region_type) :
    std_rel_pub Temporary ρ → ρ = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  Lemma std_rel_pub_rtc_Temporary (ρ1 ρ2 : region_type) :
    ρ1 = Temporary →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Temporary.
  Proof.
    intros Hx Hrtc.
    induction Hrtc ;auto.
    subst. apply IHHrtc. apply std_rel_pub_Temporary; auto.
  Qed.

  Lemma std_rel_pub_Revoked (ρ : region_type) :
    std_rel_pub Revoked ρ → ρ = Permanent ∨ ρ = Temporary.
  Proof.
    intros Hrel.
    inversion Hrel; auto.
  Qed.

  Lemma std_rel_pub_rtc_Revoked (ρ1 ρ2 : region_type) :
    ρ1 = Revoked →
    rtc std_rel_pub ρ1 ρ2 → ρ2 = Permanent ∨ ρ2 = Temporary ∨ ρ2 = Revoked.
  Proof.
    intros Hρ1 Hrtc.
    inversion Hrtc; subst; auto.
    apply std_rel_pub_Revoked in H as [-> | ->];auto.
    - left. eapply std_rel_pub_rtc_Permanent;eauto.
    - right. left. eapply std_rel_pub_rtc_Temporary;eauto.
  Qed.

  (* ------------------------- DEFINITION STD STS CLASS -------------------------- *)

  Global Program Instance sts_std : STS_STD region_type :=
    {|
      Rpub := std_rel_pub;
      Rpriv := std_rel_priv;
    |}.

End region_invariants_definitions.
