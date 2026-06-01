From iris.proofmode Require Import proofmode.
From cap_machine Require Export cap_lang sts.
From cap_machine Require Export stdpp_extra.

Section world_standard_sts.

  (* We will first define the standard STS for the shared part of the heap *)
  Inductive region_type :=
  | Temporary
  | Permanent
  | Revoked.

  Global Instance LeibnizEquiv_region_type : @LeibnizEquiv region_type (@eq region_type).
  Proof. rewrite /LeibnizEquiv; intros ? ? ?; done. Defined.
  Global Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Permanent, Permanent
             | Revoked, Revoked
             | Temporary, Temporary => left eq_refl
             | _, _ => ltac:(right; auto)
             end).

  Global Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Temporary => 1
                         | Permanent => 2
                         | Revoked => 3
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Temporary
                     else if decide (n = 2) then Some Permanent
                          else if decide (n = 3) then Some Revoked
                               else None)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity;
    unfold encode, decode;
    repeat (match goal with |- context [ decide ?x ] => destruct (decide x); [ try (exfalso; lia) | ] end).
  Qed.

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

End world_standard_sts.

Section world_standard_sts_mono.
  Context {Σ:gFunctors}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType Word Σ}
    `{MP: MachineParameters}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation SEAL_STD := (leibnizO (seals_std OType Word)).
  Notation WORLD := (prodO (prodO STS_STD STS) SEAL_STD).
  Notation WorldT := (((STS_std_states Addr region_type) * (STS_states * STS_rels) * (seals_std OType Word)) : Type).
  Implicit Types W : WORLD.

  Definition future_pub_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_pub_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition future_priv_mono (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (v  : Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_priv_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition mono_pub (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) :=
    (∀ (w : Word), future_pub_mono C φ w)%I.
  Definition mono_priv (C : CmptName) (φ : (WORLD * CmptName * Word) -> iProp Σ) (p : Perm) :=
    (∀ (w : Word), ⌜canStore p w = true⌝ -∗ future_priv_mono C φ w)%I.

  Lemma future_priv_mono_is_future_pub_mono (C : CmptName) (φ: (WORLD * CmptName * Word) → iProp Σ) v :
    future_priv_mono C φ v -∗ future_pub_mono C φ v.
  Proof.
    iIntros "#H". unfold future_pub_mono. iModIntro.
    iIntros (W W' Hrelated) "Hφ".
    iApply "H"; eauto.
    iPureIntro; eauto using related_sts_pub_priv_world.
  Qed.

  Lemma related_sts_priv_world_fresh_Permanent W a :
    related_sts_priv_world W (<s[a:=Permanent]s> W).
  Proof.
    apply related_sts_priv_world_fresh.
    intros ρ'; destruct ρ'.
    + eright;[right;constructor|left].
    + left.
    + eright;[left;constructor|].
      eright;[right;constructor|left].
  Qed.

End world_standard_sts_mono.

Notation STS := (leibnizO (STS_states * STS_rels)).
Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
Notation SEAL_STD := (leibnizO (seals_std OType Word)).
Notation WORLD := (prodO (prodO STS_STD STS) SEAL_STD).
Notation WorldT := (((STS_std_states Addr region_type) * (STS_states * STS_rels) * (seals_std OType Word)) : Type).
