From iris.proofmode Require Import proofmode ltac_tactics.
From griotte Require Export named_props.

(** Named conjuncts print as their proposition: the names matter only to
    [iNamed], so goals show [P ∗ Q] instead of ["HP" ∷ P ∗ "HQ" ∷ Q]. *)
Notation "P" := (named _ P) (at level 79, P at level 79, only printing).

(** Opens the hypothesis [H] with the lemma [lem] (whose conclusion is under a
    modality that [iMod] eliminates, such as [◇]), then names its conjuncts with
    [iNamed]. *)
Tactic Notation "iModNamed" open_constr(lem) constr(H) :=
  iMod (lem with H) as H; iNamed H.

(** [iIntrosNamed (x1 … xn)] introduces the universally quantified variables
    [x1 … xn] and the premise under a fresh anonymous name, then destructs the
    premise with [iNamed]; use it when all the conjuncts of the premise are
    named, so that nothing remains under the fresh name.
    [iIntrosNamed (x1 … xn) H] instead introduces the premise as [H], for a
    premise whose remaining unnamed part must stay available as [H]. *)
Tactic Notation "iIntrosNamed" :=
  let H := iFresh in iIntros H; iNamed H.
Tactic Notation "iIntrosNamed" "(" ne_simple_intropattern_list(xs) ")" :=
  let H := iFresh in _iIntros xs H; iNamed H.
Tactic Notation "iIntrosNamed" constr(H) :=
  iIntros H; iNamed H.
Tactic Notation "iIntrosNamed" "(" ne_simple_intropattern_list(xs) ")" constr(H) :=
  _iIntros xs H; iNamed H.
