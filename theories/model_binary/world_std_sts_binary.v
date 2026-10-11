From iris.proofmode Require Import proofmode.
From griotte Require Export world_std_sts.
From griotte Require Export stdpp_extra.

(** Loading a word through a capability with permission [p'], then through a
    capability with a weaker permission [p], is the same as loading it directly
    through [p]. *)
(* TODO: move to machine_word.v *)
Lemma load_word_load_word (p p' : Perm) (w : Word) :
  PermFlowsTo p p' →
  load_word p (load_word p' w) = load_word p w.
Proof.
  intros Hfl.
  destruct (isDL p') eqn:HDL'.
  { assert (isDL p = true) as HDL by (eapply isDL_flowsto; eauto).
    destruct (isDRO p') eqn:HDRO'.
    { assert (isDRO p = true) as HDRO by (eapply isDRO_flowsto; eauto).
      rewrite /load_word HDL HDRO HDL' HDRO'.
      destruct w as [z | [ ? [] ? ? ? ? | ? ? ? ? ? ?] | ? ? ? ? ? ? | ? [ ? [] ? ? ? ? | ? ? ? ? ? ?] ]; done. }
    destruct (isDRO p) eqn:HDRO;
      rewrite /load_word HDL HDRO HDL' HDRO';
      destruct w as [z | [ ? [] ? ? ? ? | ? ? ? ? ? ?] | ? ? ? ? ? ? | ? [ ? [] ? ? ? ? | ? ? ? ? ? ?] ]; done. }
  destruct (isDRO p') eqn:HDRO'.
  { assert (isDRO p = true) as HDRO by (eapply isDRO_flowsto; eauto).
    destruct (isDL p) eqn:HDL;
      rewrite /load_word HDL HDRO HDL' HDRO';
      destruct w as [z | [ ? [] ? ? ? ? | ? ? ? ? ? ?] | ? ? ? ? ? ? | ? [ ? [] ? ? ? ? | ? ? ? ? ? ?] ]; done. }
  rewrite {2}/load_word HDL' HDRO'; done.
Qed.

(** Resolve [Countable (Word * Word)] directly with [prod_countable]. Otherwise,
    the search first tries [finite_countable], which can instantiate the type
    of an unannotated binder with [Finite (Word * Word)]. *)
#[global] Hint Extern 0 (Countable (Word * Word)) =>
  exact (@prod_countable Word _ _ Word _ _) : typeclass_instances.

(** The binary world records, for each otype, the set of pairs of words
    (one word per run) sealed with that otype. *)
Notation SEAL_STD := (leibnizO (seals_std OType (Word * Word))).
Notation WORLD := (prodO (prodO STS_STD STS) SEAL_STD).
Notation WorldT := (((STS_std_states Addr region_type) * (STS_states * STS_rels) * (seals_std OType (Word * Word))) : Type).

Section world_standard_sts_mono_binary.
  Context {Σ:gFunctors}
    {Cname : CmptNameG} {CNames : gset CmptName}
    {stsg : STSG Addr region_type OType (Word * Word) Σ}
    `{MP: MachineParameters}.
  Implicit Types W : WORLD.

  (** Monotonicity of a predicate over pairs of words (one word per run). *)
  Definition future_pub_mono (C : CmptName)
    (φ : (WORLD * CmptName * (Word * Word)) -> iProp Σ) (v : Word * Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_pub_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition future_priv_mono (C : CmptName)
    (φ : (WORLD * CmptName * (Word * Word)) -> iProp Σ) (v : Word * Word) : iProp Σ :=
    (□ ∀ (W W' : WORLD),
        ⌜ related_sts_priv_world W W'⌝
        → φ (W,C,v) -∗ φ (W',C,v))%I.

  Definition mono_pub (C : CmptName) (φ : (WORLD * CmptName * (Word * Word)) -> iProp Σ) :=
    (∀ (w : Word * Word), future_pub_mono C φ w)%I.

  (** Private monotonicity is only required for the pairs of words that can be
      stored through [p] on both sides. *)
  Definition mono_priv (C : CmptName) (φ : (WORLD * CmptName * (Word * Word)) -> iProp Σ) (p : Perm) :=
    (∀ (w : Word * Word),
        ⌜canStore p w.1 = true ∧ canStore p w.2 = true⌝ -∗
        future_priv_mono C φ w)%I.

  Lemma future_priv_mono_is_future_pub_mono (C : CmptName)
    (φ: (WORLD * CmptName * (Word * Word)) → iProp Σ) v :
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

End world_standard_sts_mono_binary.
