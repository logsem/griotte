From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel.
From cap_machine Require Import cmdc_spec.
(* From cap_machine Require Import compartment_layout. *)
From stdpp Require Import base.
From cap_machine Require Import switcher assert.
From cap_machine Require Import mkregion_helpers.

Record cmpt : Type :=
  mkCmpt {
      cmpt_b_pcc : Addr;
      cmpt_a_code : Addr;
      cmpt_e_pcc : Addr;

      cmpt_b_cgp : Addr;
      cmpt_e_cgp : Addr;

      cmpt_imports : list Word;
      cmpt_code : list Word;
      cmpt_data : list Word;

      cmpt_import_size : (cmpt_b_pcc + length cmpt_imports)%a = Some cmpt_a_code;
      cmpt_code_size : (cmpt_a_code + length cmpt_code)%a = Some cmpt_e_pcc;
      cmpt_data_size : (cmpt_b_cgp + length cmpt_data)%a = Some cmpt_e_cgp;

      code_data_disjoint :
            (finz.seq_between cmpt_b_pcc cmpt_e_pcc)
              ## (finz.seq_between cmpt_b_cgp cmpt_e_cgp)
    }.

Definition cmpt_pcc_region (C : cmpt) : list Addr :=
  (finz.seq_between (cmpt_b_pcc C) (cmpt_e_pcc C)).

Definition cmpt_cgp_region (C : cmpt) : list Addr :=
  (finz.seq_between (cmpt_b_pcc C) (cmpt_e_pcc C)).

Definition disjoint_cmpt (C1 C2 : cmpt) : Prop :=
  let pcc1 := cmpt_pcc_region C1 in
  let pcc2 := cmpt_pcc_region C2 in
  let cgp1 := cmpt_cgp_region C1 in
  let cgp2 := cmpt_cgp_region C2 in
  pcc1 ## pcc2 ∧
  pcc1 ## cgp2 ∧
  cgp1 ## pcc2 ∧
  cgp1 ## cgp2.

Global Instance Cmpt_Disjoint : Disjoint cmpt := disjoint_cmpt.

Definition cmpt_pcc_mregion (C: cmpt) : gmap Addr Word :=
  mkregion (cmpt_b_pcc C) (cmpt_a_code C) (cmpt_imports C)
  ∪ mkregion (cmpt_a_code C) (cmpt_e_pcc C) (cmpt_code C).

Definition cmpt_cgp_mregion (C: cmpt) : gmap Addr Word :=
  mkregion (cmpt_b_cgp C) (cmpt_e_cgp C) (cmpt_data C).

(* Record cmptExportTbl : Type := *)
(*   mkCmptExportTbl { *)
(*       etlb_start : Addr ; *)
(*       etlb_end : Addr ; *)
(*     }. *)

Record cmptSwitcher `{MachineParameters} : Type :=
  mkCmptSwitcher {
      b_switcher : Addr ;
      e_switcher : Addr ;
      a_switcher_cc : Addr ;
      ot_switcher : OType ;

      switcher_size :
      (b_switcher + length switcher_instrs)%a = Some e_switcher ;

      switcher_cc_entry_point :
      (b_switcher + 1)%a = Some a_switcher_cc ;
    }.

Definition cmpt_switcher_region `{MachineParameters} (Cswitcher : cmptSwitcher) :=
  (finz.seq_between (b_switcher Cswitcher) (e_switcher Cswitcher)).

Definition cmpt_switcher_mregion `{MachineParameters} (Cswitcher : cmptSwitcher) : gmap Addr Word :=
  let ot := (ot_switcher Cswitcher) in
  let switcher_sealing := (WSealRange (true,true) Global ot (ot^+1)%ot ot) in
  mkregion (b_switcher Cswitcher) (a_switcher_cc Cswitcher) [switcher_sealing]
  ∪ mkregion (a_switcher_cc Cswitcher) (e_switcher Cswitcher) switcher_instrs.

Definition switcher_disjoint
  `{MachineParameters} (C : cmpt) (Cswitcher : cmptSwitcher) : Prop :=
  let switcher := cmpt_switcher_code Cswitcher in
  let pcc := cmpt_pcc_region C in
  let cgp := cmpt_cgp_region C in
  switcher ## pcc ∧ switcher ## cgp.

Record cmptAssert `{MachineParameters} : Type :=
  mkCmptAssert {
      b_assert : Addr ;
      e_assert : Addr ;
      cap_assert : Addr ;
      flag_assert : Addr ;

      assert_code_size :
      (b_assert + length (assert_subroutine_instrs cnull cnull cnull))%a = Some cap_assert ;
      assert_cap_size :
      (cap_assert + 1)%a = Some e_assert;

      assert_flag_size :
      (flag_assert + 1)%a = Some (flag_assert ^+ 1)%a;
    }.

Definition cmpt_assert_code `{MachineParameters} (Cassert : cmptAssert) :=
  (finz.seq_between (b_assert Cassert) (e_assert Cassert)).

Definition cmpt_assert_flag `{MachineParameters} (Cassert : cmptAssert) :=
  (finz.seq_between (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a).

Definition assert_disjoint
  `{MachineParameters} (C : cmpt) (Cassert : cmptAssert) : Prop :=
  let assert_code := cmpt_assert_code Cassert in
  let assert_flag := cmpt_assert_flag Cassert in
  let pcc := cmpt_pcc_region C in
  let cgp := cmpt_cgp_region C in
  assert_code ## pcc ∧
  assert_code ## cgp ∧
  assert_flag ## pcc ∧
  assert_flag ## cgp.

Class memory_layout `{MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adv compartments B and C *)
    B_cmpt : cmpt ;
    C_cmpt : cmpt ;

    (* disjointness *)
    cmpts_disjoint :
    main_cmpt ## B_cmpt
    ∧ main_cmpt ## C_cmpt
    ∧ B_cmpt ## C_cmpt ;

    switcher_cmpt_disjoint :
    switcher_disjoint main_cmpt switcher_cmpt
    ∧ switcher_disjoint B_cmpt switcher_cmpt
    ∧ switcher_disjoint C_cmpt switcher_cmpt ;

    assert_cmpt_disjoint :
    assert_disjoint main_cmpt assert_cmpt
    ∧ assert_disjoint B_cmpt assert_cmpt
    ∧ assert_disjoint C_cmpt assert_cmpt ;
}.
