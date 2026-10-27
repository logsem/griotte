From stdpp Require Import namespaces strings.
From griotte Require Import resources.

(** The namespace of the invariant [switcher_inv]. *)
Definition Nswitcher : namespace := nroot .@ "switcher".

Lemma Nswitcher_Ntrap : Nswitcher ## Ntrap.
Proof. solve_ndisj. Qed.
