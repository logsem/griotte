From iris.proofmode Require Import proofmode.
(* [custom_syntax] adds the intro pattern [@], which destructs a hypothesis with
   [iNamed]: [iIntros "@"], [iDestruct "H" as "[@ H']"], [iMod "H" as ">@"]. *)
From griotte Require Export named_props custom_syntax.

(** Named conjuncts print as their proposition: the names matter only to
    [iNamed], so goals show [P ∗ Q] instead of ["HP" ∷ P ∗ "HQ" ∷ Q]. *)
Notation "P" := (named _ P) (at level 79, P at level 79, only printing).

(** Opens the hypothesis [H] with the lemma [lem] (whose conclusion is under a
    modality that [iMod] eliminates, such as [◇]), then names its conjuncts with
    [iNamed]. *)
Tactic Notation "iModNamed" open_constr(lem) constr(H) :=
  iMod (lem with H) as H; iNamed H.
