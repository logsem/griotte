From stdpp Require Import finite gmap.

Class CmptNameG := CmptNameS {
  CmptName : Type;
  CmptName_eq_dec :: EqDecision CmptName;
  CmptName_countable :: Finite CmptName;
}.

Definition CNames `{CmptNameG} : gset CmptName := list_to_set (enum CmptName).
