From griotte Require Import machine_base mmio_shadow mmio_revoker.

(* Memory-mapped addresses are never memory: the shadow region and the revoker. *)
Definition is_mmio_address `{ShadowRegion} `{RevokerRegion} (a : Addr) : bool :=
  is_shadow_address a || is_revoker_address a.

Lemma not_mmio_not_shadow `{ShadowRegion} `{RevokerRegion} a :
  is_mmio_address a = false -> is_shadow_address a = false.
Proof. rewrite /is_mmio_address. by intros [? ?]%orb_false_iff. Qed.

Lemma not_mmio_not_revoker `{ShadowRegion} `{RevokerRegion} a :
  is_mmio_address a = false -> is_revoker_address a = false.
Proof. rewrite /is_mmio_address. by intros [? ?]%orb_false_iff. Qed.

(* A range that addresses no memory-mapped device. *)
Definition disjoint_from_mmio `{ShadowRegion} `{RevokerRegion} (b e : Addr) : Prop :=
  disjoint_from_shadow b e ∧ revoker_addr ∉ finz.seq_between b e.

Lemma disjoint_from_mmio_shadow `{ShadowRegion} `{RevokerRegion} (b e : Addr) :
  disjoint_from_mmio b e → disjoint_from_shadow b e.
Proof. by intros [? _]. Qed.

Lemma disjoint_from_mmio_not_in `{ShadowRegion} `{RevokerRegion} (b e a : Addr) :
  disjoint_from_mmio b e →
  withinBounds b e a = true →
  is_mmio_address a = false.
Proof.
  intros [Hshadow Hrev] Hbounds. rewrite /is_mmio_address.
  rewrite (disjoint_from_shadow_not_in b e a Hshadow Hbounds) /=.
  apply bool_decide_eq_false. intros ->. apply Hrev.
  apply elem_of_finz_seq_between. by apply withinBounds_true_iff.
Qed.

Lemma disjoint_from_mmio_weaken `{ShadowRegion} `{RevokerRegion} (b e b' e' : Addr) :
  (b <= b')%a → (e' <= e)%a →
  disjoint_from_mmio b e → disjoint_from_mmio b' e'.
Proof.
  intros Hb He [Hshadow Hrev]. split.
  - rewrite /disjoint_from_shadow in Hshadow |- *.
    intros x Hx Hx'. apply (Hshadow x); last done.
    apply elem_of_finz_seq_between in Hx. apply elem_of_finz_seq_between. solve_addr.
  - intros Hx. apply Hrev.
    apply elem_of_finz_seq_between in Hx. apply elem_of_finz_seq_between. solve_addr.
Qed.
