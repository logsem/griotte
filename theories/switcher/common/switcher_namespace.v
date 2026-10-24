From stdpp Require Import namespaces strings.
From griotte Require Import cerise_instance.

(** The namespace of the invariant [switcher_inv]. *)
Definition Nswitcher : namespace := nroot .@ "switcher".

Lemma Nswitcher_N_trap : Nswitcher ## N_trap.
Proof. solve_ndisj. Qed.
