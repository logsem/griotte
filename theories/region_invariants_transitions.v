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
    apply std_rel_pub_Revoked in H as [-> | ->];auto.
    - left. eapply std_rel_pub_rtc_Permanent;eauto.
    - right. left. eapply std_rel_pub_rtc_Monotemporary;eauto.
  Qed.

  Lemma std_rel_pub_Monostatic x g :
    std_rel_pub (Monostatic g) x → x = Monostatic g.
  Proof.
    intros Hrel.
    inversion Hrel.
  Qed.

  (* Lemma std_rel_pub_Uninitialized x w : *)
  (*   std_rel_pub (Uninitialized w) x → x = Monotemporary. *)
  (* Proof. *)
  (*   intros Hrel. *)
  (*   inversion Hrel. auto.  *)
  (* Qed. *)

  (* Lemma std_rel_pub_rtc_Uninitialized x y w : *)
  (*   x = (Uninitialized w) → *)
  (*   rtc std_rel_pub x y → y = Monotemporary ∨ y = (Uninitialized w). *)
  (* Proof. *)
  (*   intros Hx Hrtc. *)
  (*   inversion Hrtc; subst; auto. left. *)
  (*   apply std_rel_pub_Uninitialized in H0.  *)
  (*   eapply std_rel_pub_rtc_Monotemporary;eauto. *)
  (* Qed. *)

  Lemma std_rel_pub_rtc_Monostatic x y g :
    x = (Monostatic g) →
    rtc std_rel_pub x y → y = (Monostatic g).
  Proof.
    intros Hx Hrtc.
    induction Hrtc; subst; auto.
    apply std_rel_pub_Monostatic in H as ->.
    auto.
  Qed.

  Lemma std_rel_pub_plus_Monostatic x g :
    std_rel_pub_plus (Monostatic g) x → x = Monotemporary.
  Proof.
    intros Hrel; inversion Hrel. auto. Qed.

  (* Lemma std_rel_pub_plus_Uninitialized x w : *)
  (*   std_rel_pub_plus (Uninitialized w) x → x = (Uninitialized w). *)
  (* Proof. *)
  (*   intros Hrel; inversion Hrel. Qed. *)

  (* Lemma std_rel_pub_plus_Monotemporary x : *)
  (*   std_rel_pub_plus Monotemporary x → ∃ w, x = Uninitialized w. *)
  (* Proof. *)
  (*   intros Hrel. inversion Hrel. eauto. Qed.  *)

  (* Lemma std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized x y : *)
  (*   x = Monotemporary ∨ (∃ w, x = Uninitialized w) → *)
  (*   rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y → *)
  (*   y = Monotemporary ∨ ∃ w, y = Uninitialized w. *)
  (* Proof. *)
  (*   intros Hx Hrtc. *)
  (*   induction Hrtc ;[destruct Hx;eauto|]. *)
  (*   destruct Hx as [-> | [g ->] ]. *)
  (*   - destruct H0 as [Hpub | Hpubp].  *)
  (*     + apply std_rel_pub_Monotemporary in Hpub. auto.  *)
  (*     + apply std_rel_pub_plus_Monotemporary in Hpubp as [g' ->]. *)
  (*       apply IHHrtc. eauto.  *)
  (*   - destruct H0 as [Hpub | Hpubp].  *)
  (*     + apply std_rel_pub_Uninitialized in Hpub. auto.  *)
  (*     + apply std_rel_pub_plus_Uninitialized in Hpubp as ->. *)
  (*       apply IHHrtc. eauto.  *)
  (* Qed.  *)

  (* Lemma std_rel_pub_plus_rtc_Uninitialized x y w : *)
  (*   x = Uninitialized w → *)
  (*   rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y → *)
  (*   y = Monotemporary ∨ (∃ w', y = Uninitialized w'). *)
  (* Proof. *)
  (*   intros Hx Hrtc. *)
  (*   eapply std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized;eauto.  *)
  (* Qed.  *)

  (* Lemma std_rel_pub_plus_rtc_Monotemporary x y : *)
  (*   x = Monotemporary → *)
  (*   rtc (λ x0 y0, std_rel_pub x0 y0 ∨ std_rel_pub_plus x0 y0) x y → *)
  (*   y = Monotemporary ∨ ∃ w, y = Uninitialized w. *)
  (* Proof. *)
  (*   intros Hx Hrtc. subst.  *)
  (*   apply (std_rel_pub_plus_rtc_Monotemporary_or_Uninitialized Monotemporary);eauto.  *)
  (* Qed. *)

End transitions.
