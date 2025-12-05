From iris.proofmode Require Import proofmode.
From cap_machine Require Import region_invariants_allocation region_invariants_revocation interp_weakening monotone.

Section VAE_helper.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
  .

  Context {C : CmptName}.

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Definition awkN : namespace := nroot .@ "awkN".
  Definition awk_inv C i a :=
    (∃ x:bool, sts_state_loc (A:=Addr) C i x
            ∗ if x
              then a ↦ₐ WInt 1%Z
              else a ↦ₐ WInt 0%Z)%I.

  Definition awk_rel_pub := λ a b, a = false ∨ b = true.
  Definition awk_rel_priv := λ (a b : bool), True.

  Lemma rtc_rel_pub y x :
    y = (encode true) ->
    rtc (convert_rel awk_rel_pub) y x ->
    x = (encode true).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    rewrite Heq in H.
    inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ].
    inversion Hy; subst; auto.
    apply encode_inj in Heq1. inversion Heq1.
  Qed.
  Lemma rtc_rel_pub' x :
    rtc (convert_rel awk_rel_pub) (encode true) (encode x) ->
    x = true.
  Proof.
    intros Hrtc.
    apply encode_inj.
    apply rtc_rel_pub with (encode true); auto.
  Qed.

  Lemma rtc_rel_pub_inv y x :
    y = (encode true) ∨ y = (encode false) ->
    rtc (convert_rel awk_rel_pub) y x ->
    x = (encode true) ∨ x = (encode false).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    destruct Heq; subst.
    + inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      apply IHHrtc. destruct b; auto.
    + inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      apply IHHrtc. destruct b; auto.
  Qed.

  Lemma awk_rel_pub_inv (b : bool) (d d' : positive) :
    d = encode b ->
    rtc (convert_rel awk_rel_pub) d d' ->
    ∃ b : bool, d' = encode b.
  Proof.
    intros Hd Hrtc.
    assert (d' = encode true ∨ (d' = encode false)).
    { eapply rtc_rel_pub_inv; last done.
      destruct b ; auto.
    }
    destruct H; eexists; eauto.
  Qed.

  Lemma rtc_rel_inv y x :
    y = (encode true) ∨ y = (encode false) ->
    rtc (λ x y : positive, convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) y x ->
    x = (encode true) ∨ x = (encode false).
  Proof.
    intros Heq Hrtc.
    induction Hrtc; auto.
    destruct Heq; subst.
    + destruct H as [ | ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
    + destruct H as [ | ].
      all: inversion H as [y' [b [Heq1 [Heq2 Hy] ] ] ]; simplify_eq.
      all: apply IHHrtc; destruct b; auto.
  Qed.

  Lemma awk_rel_inv (b : bool) (d d' : positive) :
    d = encode b ->
    rtc (λ x y : positive, convert_rel awk_rel_pub x y ∨ convert_rel awk_rel_priv x y) d d' ->
    ∃ b : bool, d' = encode b.
  Proof.
    intros Hd Hrtc.
    assert (d' = encode true ∨ (d' = encode false)).
    { eapply rtc_rel_inv; last done.
      destruct b ; auto.
    }
    destruct H; eexists; eauto.
  Qed.

End VAE_helper.
