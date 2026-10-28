From stdpp Require Import namespaces strings.
From griotte Require Import resources.

(** The namespace of the invariant [trusted_stack_inv]. *)
Definition Ntstack : namespace := nroot .@ "tstack".

Lemma Ntstack_Ntrap : Ntstack ## Ntrap.
Proof. solve_ndisj. Qed.
