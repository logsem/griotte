From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import agree.
From griotte Require Export machine_base.


Definition entryR : cmra :=
  (agreeR (leibnizO nat)).

Class entryGpreS Σ := EntryGpreS {
  entryPreG_rel :: inG Σ entryR;
}.

Class entryGS Σ := EntryGS {
  entryG_rel :: inG Σ entryR;
  γentry : Word -> gname
}.

Definition entryPreΣ :=
  #[ GFunctor entryR ].

Instance subG_entryPreΣ {Σ} :
  subG entryPreΣ Σ →
  entryGpreS Σ.
Proof. solve_inG. Qed.

Section ENTRY_defs.
  Context {Σ:gFunctors} {entryg : entryGS Σ}.

  Definition ENTRY_def (w : Word) (n : nat) : iProp Σ :=
    own (γentry w) (to_agree n).
  Definition ENTRY_aux : { x | x = @ENTRY_def }. by eexists. Qed.
  Definition ENTRY := proj1_sig ENTRY_aux.
  Definition ENTRY_eq : @ENTRY = @ENTRY_def := proj2_sig ENTRY_aux.
  Notation "w ↦□ₑ n" :=(ENTRY w n) (at level 20) : bi_scope.

  Lemma entry_agree w n1 n2:
    w ↦□ₑ n1 -∗ w ↦□ₑ n2 -∗ ⌜n1 = n2⌝.
  Proof.
    iIntros "H1 H2".
    rewrite ENTRY_eq /ENTRY_def.
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as "%".
    apply to_agree_op_inv in H.
    done.
  Qed.
  Global Instance persistent_entry w n : Persistent (w ↦□ₑ n)%I.
  Proof.
    rewrite ENTRY_eq /ENTRY_def.
    apply _.
  Defined.


End ENTRY_defs.
Notation "w ↦□ₑ n" :=  (ENTRY w n) (at level 20) : bi_scope.

Section entryPre.
  Context {Σ:gFunctors} {entrypreg : entryGpreS Σ}.


  Lemma entry_rel_init (m : gmap Word nat) :
    ⊢ |==> (∃ γentry, ([∗ map] w↦n ∈ m, own (γentry w) (to_agree n))).
  Proof.

    induction m using map_ind.
    - iModIntro.
      iExists ( λ w, encode w).
      by iApply big_sepM_empty.
    - iMod IHm as (γentry) "IH".
      iMod (own_alloc (A:= entryR) (to_agree x)) as (γx) "Hrel" ; first done.
      iModIntro.
      iExists (λ w, if (bool_decide (w = i)) then γx else γentry w).
      iApply (big_sepM_insert with "[IH Hrel]");auto.
      rewrite bool_decide_eq_true_2; auto; iFrame.
      iApply (big_sepM_mono with "IH").
      iIntros (k n Hk) "H".
      rewrite bool_decide_eq_false_2; [done|].
      by intros ->; rewrite H in Hk.
  Qed.

  Lemma entry_init m :
    ⊢ |==> ∃ (entryg: entryGS Σ), ([∗ map] w↦n ∈ m, w ↦□ₑ n).
  Proof.
    iMod entry_rel_init as (γ) "H".
    iExists (EntryGS _ _ _).
    by rewrite ENTRY_eq /ENTRY_def.
  Qed.

End entryPre.
