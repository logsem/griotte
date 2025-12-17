From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import is_word_type lea_to_base.

Section Checkra.
  Context
      {MP: MachineParameters}
  .


  Definition checkra_instrs (r r1 r2 : RegName) : list Word.
  (* TODO: it's actually quite annoying to check...
     In CHERIoT, I would do something like:
     ```
     GetP r1 r;
     LAnd r1 (R, Ow, DL, DRO);
     ```

     Maybe I should have another instruction in the machine
     for checking this easily?
   *)
  Admitted.


End Checkra.

Section Checkra_spec.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {MP: MachineParameters}
  .

End Checkra_spec.
