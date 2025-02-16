From iris.algebra Require Import frac.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening addr_reg_sample rules proofmode.
(* From cap_machine Require Import multiple_updates region_invariants_frozen region_invariants_allocation. *)
From cap_machine Require Import switcher.

Section Switcher.
  Context
    {Σ : gFunctors}
      {ceriseg: ceriseG Σ}
      {sealsg: sealStoreG Σ}
      {nainv: logrel_na_invs Σ}
      {MP: MachineParameters}
  .



End Switcher.
