From iris.proofmode Require Import proofmode.
From griotte Require Export griotte_lang sts region_keys logical_words.
From griotte Require Export stdpp_extra.

Section world_standard_sts.

  (* We will first define the standard STS for the shared part of the heap.
     The local world only holds local keys: Permanent regions live in the
     map of Permanent regions, outside the world. *)
  Inductive region_type :=
  | Temporary
  | Revoked.

  #[global] Instance LeibnizEquiv_region_type : @LeibnizEquiv region_type (@eq region_type).
  Proof. rewrite /LeibnizEquiv; intros ? ? ?; done. Defined.
  #[global] Instance region_type_EqDecision : EqDecision region_type :=
    (fun x y => match x, y with
             | Revoked, Revoked
             | Temporary, Temporary => left eq_refl
             | _, _ => ltac:(right; auto)
             end).

  #[global] Instance region_type_countable : Countable region_type.
  Proof.
    set encode := fun ty => match ty with
                         | Temporary => 1
                         | Revoked => 2
                         end%positive.
    set decode := (fun n =>
                     if decide (n = 1) then Some Temporary
                     else if decide (n = 2) then Some Revoked
                          else None)%positive.
    eapply (Build_Countable _ _ encode decode).
    intro ty. destruct ty; try reflexivity;
    unfold encode, decode;
    repeat (match goal with |- context [ decide ?x ] => destruct (decide x); [ try (exfalso; lia) | ] end).
  Qed.

  Inductive std_rel_pub : region_type -> region_type -> Prop :=
  | Std_pub_Revoked_Temporary : std_rel_pub Revoked Temporary.

  Inductive std_rel_priv : region_type -> region_type -> Prop :=
  | Std_priv_Temporary_Revoked : std_rel_priv Temporary Revoked.

  (* --------------------------------------------------------------------------------- *)
  (* ------------------------- LEMMAS ABOUT STD TRANSITIONS -------------------------- *)
  (* --------------------------------------------------------------------------------- *)

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

  (** The part of the world model a key lives in: the map of Permanent
      regions, or the local world. *)
  Inductive region_part :=
  | InPerm
  | InLocal.

  #[global] Instance region_part_EqDecision : EqDecision region_part.
  Proof. solve_decision. Qed.

  (* ------------------------- DEFINITION STD STS CLASS -------------------------- *)

  #[global] Program Instance sts_std : STS_STD region_type :=
    {|
      Rpub := std_rel_pub;
      Rpriv := std_rel_priv;
    |}.

End world_standard_sts.

Section world_standard_sts_mono.
  Context {Σ:gFunctors}
    {Cname : CmptNameG}
    `{MP: MachineParameters}.
  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states LAddr region_type)).
  Notation WORLD := (leibnizO (World LAddr region_type)).
  Notation WorldT := (World LAddr region_type : Type).
  Implicit Types W : WORLD.

  Definition future_pub_mono (C : CmptName) (φ : (WORLD * CmptName * LWord) -> iProp Σ) (v  : LWord) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_pub_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition mono_pub (C : CmptName) (φ : (WORLD * CmptName * LWord) -> iProp Σ) :=
    (∀ (w : LWord), future_pub_mono C φ w)%I.

End world_standard_sts_mono.

Notation STS := (leibnizO (STS_states * STS_rels)).
Notation STS_STD := (leibnizO (STS_std_states LAddr region_type)).
Notation WORLD := (leibnizO (World LAddr region_type)).
Notation WorldT := (World LAddr region_type : Type).
