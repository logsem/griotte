From iris.proofmode Require Import proofmode.
From cap_machine Require Import rules proofmode.
From cap_machine Require Import checkra checkints check_no_overlap_spec.

Section Check_Valid_SO.
  Context
      {MP: MachineParameters}
  .

  Definition check_valid_stack_object_instrs (r r1 r2 : RegName) : list Word :=
    checkra_instrs r r1 r2
      ++ check_no_overlap_instrs r csp r1 r2
      ++ checkints_instrs r r1 r2.

End Check_Valid_SO.
