From stdpp Require Import countable.
From griotte Require Export addresses.
From machine_utils Require Import finz_base.
From griotte Require Import machine_utils_extra.

(** Allocation identifiers. They are ghost only: the machine never sees them. *)
Definition AId := positive.

(** Region keys. The world indexes its regions by [LAddr]. A non-heap region
    is keyed by its address. A heap region is keyed by its address and the
    identifier of the allocation it belongs to. *)
Inductive LAddr :=
| LNonHeap (a : Addr)
| LHeap (a : Addr) (ι : AId).

#[warning="-uniform-inheritance"] Coercion LNonHeap : Addr >-> LAddr.

(** The address of a region key. *)
Definition laddr_addr (k : LAddr) : Addr :=
  match k with
  | LNonHeap a | LHeap a _ => a
  end.

#[global] Instance LNonHeap_inj : Inj eq eq LNonHeap.
Proof. by intros ?? [=]. Qed.

#[global] Instance LHeap_inj : Inj2 eq eq eq LHeap.
Proof. by intros ???? [=]. Qed.

Lemma LNonHeap_LHeap_ne a a' ι : LNonHeap a ≠ LHeap a' ι.
Proof. done. Qed.

Lemma laddr_addr_LNonHeap a : laddr_addr (LNonHeap a) = a.
Proof. done. Qed.

Lemma laddr_addr_LHeap a ι : laddr_addr (LHeap a ι) = a.
Proof. done. Qed.

Lemma LNonHeap_ne (a a' : Addr) : a ≠ a' → LNonHeap a ≠ LNonHeap a'.
Proof. by intros ? [=]. Qed.

#[export] Hint Resolve LNonHeap_LHeap_ne LNonHeap_ne : core.
#[export] Hint Rewrite laddr_addr_LNonHeap laddr_addr_LHeap : laddr.

#[global] Instance LAddr_eq_dec : EqDecision LAddr.
Proof. solve_decision. Defined.

#[global] Instance LAddr_countable : Countable LAddr.
Proof.
  refine (inj_countable'
            (λ k, match k with
                  | LNonHeap a => inl a
                  | LHeap a ι => inr (a, ι)
                  end)
            (λ x, match x with
                  | inl a => LNonHeap a
                  | inr (a, ι) => LHeap a ι
                  end) _).
  by intros [|].
Qed.

(** Region keys are compared by their address. *)
#[global] Instance laddr_le_preorder : PreOrder (λ k k', (laddr_addr k <= laddr_addr k')%a).
Proof. split; [intros ?|intros ???]; solve_addr. Qed.

#[global] Instance LAddr_ord : Ord LAddr :=
  {| le_a := λ k k', (laddr_addr k <= laddr_addr k')%a;
     le_a_decision := λ k k', finz_le_dec (laddr_addr k) (laddr_addr k');
     le_a_preorder := laddr_le_preorder |}.

(** List-level APIs over non-heap addresses map [LNonHeap] over their list. *)
Lemma elem_of_LNonHeap_fmap (a : Addr) (l : list Addr) :
  LNonHeap a ∈ LNonHeap <$> l ↔ a ∈ l.
Proof. apply list_elem_of_fmap_inj, _. Qed.

Lemma not_elem_of_LNonHeap_fmap (a : Addr) (l : list Addr) :
  LNonHeap a ∉ LNonHeap <$> l ↔ a ∉ l.
Proof. by rewrite elem_of_LNonHeap_fmap. Qed.

#[export] Hint Extern 0 (LNonHeap _ ∉ LNonHeap <$> _) =>
  apply not_elem_of_LNonHeap_fmap; assumption : core.
#[export] Hint Extern 0 (LNonHeap _ ∈ LNonHeap <$> _) =>
  apply elem_of_LNonHeap_fmap; assumption : core.
#[export] Hint Extern 1 (LNonHeap _ ∉ LNonHeap <$> _) =>
  apply not_elem_of_LNonHeap_fmap : core.
#[export] Hint Extern 1 (LNonHeap _ ∈ LNonHeap <$> _) =>
  apply elem_of_LNonHeap_fmap : core.

Lemma NoDup_LNonHeap_fmap (l : list Addr) :
  NoDup (LNonHeap <$> l) ↔ NoDup l.
Proof. split; [apply NoDup_fmap_1|apply NoDup_fmap_2, _]. Qed.
