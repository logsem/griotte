From stdpp Require Import finite gmap.
From iris.proofmode Require Import proofmode.
From griotte Require Import resources.

Class CmptNameG := CmptNameS {
  CmptName : Type;
  CmptName_eq_dec :: EqDecision CmptName;
  CmptName_countable :: Finite CmptName;
}.

Definition CNames `{CmptNameG} : gset CmptName := list_to_set (enum CmptName).

(** The threads that may run in a compartment. *)
Class CmptThreads {Cname : CmptNameG} := {
  cmpt_threads : CmptName → gset Thread;
}.
#[export] Hint Mode CmptThreads ! : typeclass_instances.

(** [thread_in t C]: the thread [t] may run in the compartment [C]. *)
Section thread_in.
  Context {Σ : gFunctors} {Cname : CmptNameG} {cthreads : CmptThreads}.

  Definition thread_in_def (t : Thread) (C : CmptName) : iProp Σ := ⌜t ∈ cmpt_threads C⌝.
  #[local] Definition thread_in_aux : seal (@thread_in_def). Proof. by eexists. Qed.
  Definition thread_in := thread_in_aux.(unseal).
  #[local] Definition thread_in_unseal : @thread_in = @thread_in_def :=
    thread_in_aux.(seal_eq).

  #[global] Instance thread_in_persistent t C : Persistent (thread_in t C).
  Proof. rewrite thread_in_unseal. apply _. Qed.
  #[global] Instance thread_in_plain t C : Plain (thread_in t C).
  Proof. rewrite thread_in_unseal. apply _. Qed.
  #[global] Instance thread_in_timeless t C : Timeless (thread_in t C).
  Proof. rewrite thread_in_unseal. apply _. Qed.

  Lemma thread_in_elim t C : thread_in t C ⊢ ⌜t ∈ cmpt_threads C⌝.
  Proof. by rewrite thread_in_unseal. Qed.

  Lemma thread_in_intro t C : t ∈ cmpt_threads C → ⊢ thread_in t C.
  Proof. intros Ht. rewrite thread_in_unseal. by iPureIntro. Qed.
End thread_in.
