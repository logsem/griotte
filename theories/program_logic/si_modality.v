From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From griotte Require Export cerise_instance.

(** * The state-interpretation update modality

    [|~{E}~> P] updates the ghost part of the state interpretation, keeping
    the physical state, and yields [P]. It is the local counterpart of the
    [si_fupd] of Iris MR 1172; unlike there, it is eliminated only under the
    WP of a non-value, which [wp_pre] opens on the state interpretation. *)
Section si_upd.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.

  Definition si_upd_def (E : coPset) (P : iProp Σ) : iProp Σ :=
    ∀ σ, cerise_state_interp σ ={E}=∗ cerise_state_interp σ ∗ P.
  Local Definition si_upd_aux : seal (@si_upd_def). Proof. by eexists. Qed.
  Definition si_upd := si_upd_aux.(stdpp.base.unseal).
  Local Definition si_upd_unseal : @si_upd = @si_upd_def := si_upd_aux.(stdpp.base.seal_eq).
End si_upd.

Notation "|~{ E }~> P" := (si_upd E P)
  (at level 99, E at level 50, P at level 200, format "'[  ' |~{  E  }~>  '/' P ']'")
  : bi_scope.

Section si_upd_laws.
  Context `{MP: MachineParameters}.
  Context `{ceriseg: ceriseG Σ}.
  Implicit Types P Q : iProp Σ.

  Lemma si_upd_ghost E P Q :
    (∀ σ, cerise_state_interp σ -∗ P ==∗ cerise_state_interp σ ∗ Q) →
    P ⊢ |~{E}~> Q.
  Proof.
    rewrite si_upd_unseal. iIntros (Hupd) "HP %σ Hσ".
    by iMod (Hupd with "Hσ HP") as "$".
  Qed.

  Lemma si_upd_mono E P Q : (P ⊢ Q) → (|~{E}~> P) ⊢ |~{E}~> Q.
  Proof.
    rewrite si_upd_unseal. iIntros (HPQ) "HP %σ Hσ".
    iMod ("HP" with "Hσ") as "[$ HP]". iModIntro. by iApply HPQ.
  Qed.

  Lemma si_upd_intro E P : P ⊢ |~{E}~> P.
  Proof. rewrite si_upd_unseal. iIntros "HP %σ Hσ". by iFrame. Qed.

  Lemma si_upd_trans E P : (|~{E}~> |~{E}~> P) ⊢ |~{E}~> P.
  Proof.
    rewrite si_upd_unseal. iIntros "HP %σ Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]". iApply ("HP" with "Hσ").
  Qed.

  Lemma si_upd_frame_r E P Q : (|~{E}~> P) ∗ Q ⊢ |~{E}~> (P ∗ Q).
  Proof.
    rewrite si_upd_unseal. iIntros "[HP HQ] %σ Hσ".
    iMod ("HP" with "Hσ") as "[$ HP]". by iFrame.
  Qed.

  Lemma fupd_si_upd E P : (|={E}=> P) ⊢ |~{E}~> P.
  Proof. rewrite si_upd_unseal. iIntros "HP %σ Hσ". by iMod "HP" as "$". Qed.

  (** Elimination under the WP of a non-value: [wp_pre] opens the state
      interpretation before the step. *)
  Lemma wp_si_upd s E e Φ P :
    language.to_val e = None →
    (|~{E}~> P) -∗ (P -∗ WP e @ s; E {{ Φ }}) -∗ WP e @ s; E {{ Φ }}.
  Proof.
    rewrite si_upd_unseal. iIntros (He) "HP Hwp". rewrite !wp_unfold /wp_pre He /=.
    iIntros (σ ns κ κs nt) "Hσ".
    iMod ("HP" with "Hσ") as "[Hσ HP]".
    iSpecialize ("Hwp" with "HP").
    iApply ("Hwp" $! σ ns κ κs nt with "Hσ").
  Qed.

  Global Instance from_modal_si_upd E P :
    FromModal True modality_id (|~{E}~> P) (|~{E}~> P) P.
  Proof. rewrite /FromModal /=. intros _. apply si_upd_intro. Qed.

  Global Instance elim_modal_si_upd_wp p s E e P Φ :
    ElimModal (language.to_val e = None) p false (|~{E}~> P) P
      (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /=.
    iIntros (He) "[HP Hwp]". iApply (wp_si_upd with "HP Hwp"); done.
  Qed.

  Global Instance elim_modal_si_upd_si_upd p E P Q :
    ElimModal True p false (|~{E}~> P) P (|~{E}~> Q) (|~{E}~> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /= si_upd_unseal.
    iIntros (_) "[HP HQ] %σ Hσ". iMod ("HP" with "Hσ") as "[Hσ HP]".
    iApply ("HQ" with "HP Hσ").
  Qed.

  Global Instance elim_modal_bupd_si_upd p E P Q :
    ElimModal True p false (|==> P) P (|~{E}~> Q) (|~{E}~> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /= si_upd_unseal.
    iIntros (_) "[HP HQ] %σ Hσ". iMod "HP". iApply ("HQ" with "HP Hσ").
  Qed.

  Global Instance elim_modal_fupd_si_upd p E P Q :
    ElimModal True p false (|={E}=> P) P (|~{E}~> Q) (|~{E}~> Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /= si_upd_unseal.
    iIntros (_) "[HP HQ] %σ Hσ". iMod "HP". iApply ("HQ" with "HP Hσ").
  Qed.
End si_upd_laws.
