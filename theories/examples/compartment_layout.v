From cap_machine Require Import proofmode machine_parameters.
From cap_machine Require Import switcher assert.
From cap_machine Require Import disjoint_regions_tactics mkregion_helpers.

Section CmptLayout.
  Context `{MP: MachineParameters}.

  Record cmpt : Type :=
    mkCmpt {
        cmpt_b_pcc : Addr;
        cmpt_a_code : Addr;
        cmpt_e_pcc : Addr;

        cmpt_b_cgp : Addr;
        cmpt_e_cgp : Addr;

        cmpt_exp_tbl_pcc : Addr;
        cmpt_exp_tbl_cgp : Addr;
        cmpt_exp_tbl_entries_start : Addr;
        cmpt_exp_tbl_entries_end : Addr;

        cmpt_imports : list Word;
        cmpt_code : list Word;
        cmpt_data : list Word;
        cmpt_exp_tbl_entries : list Word;

        cmpt_import_size : (cmpt_b_pcc + length cmpt_imports)%a = Some cmpt_a_code;
        cmpt_code_size : (cmpt_a_code + length cmpt_code)%a = Some cmpt_e_pcc;
        cmpt_data_size : (cmpt_b_cgp + length cmpt_data)%a = Some cmpt_e_cgp;
        cmpt_exp_tbl_pcc_size : (cmpt_exp_tbl_pcc + 1)%a = Some cmpt_exp_tbl_cgp;
        cmpt_exp_tbl_cgp_size : (cmpt_exp_tbl_cgp + 1)%a = Some cmpt_exp_tbl_entries_start;
        cmpt_exp_tbl_entries_size : (cmpt_exp_tbl_entries_end + length cmpt_exp_tbl_entries)%a = Some cmpt_exp_tbl_entries_end;

        cmpt_disjointness :
        ## [
            (finz.seq_between cmpt_b_pcc cmpt_e_pcc) ;
            (finz.seq_between cmpt_b_cgp cmpt_e_cgp) ;
            (finz.seq_between cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end)
          ]
      }.

  Definition cmpt_pcc_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_b_pcc C) (cmpt_e_pcc C)).

  Definition cmpt_cgp_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_b_pcc C) (cmpt_e_pcc C)).

  Definition cmpt_exp_tbl_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_entries_end C)).

  Definition cmpt_region (C : cmpt) : list Addr :=
   (cmpt_pcc_region C) ∪ (cmpt_cgp_region C) ∪ (cmpt_exp_tbl_region C).

  Definition disjoint_cmpt (C1 C2 : cmpt) : Prop :=
    cmpt_region C1 ## cmpt_region C2.

  Global Instance Cmpt_Disjoint : Disjoint cmpt := disjoint_cmpt.

  Definition cmpt_pcc_mregion (C: cmpt) : gmap Addr Word :=
    mkregion (cmpt_b_pcc C) (cmpt_a_code C) (cmpt_imports C) ∪
      mkregion (cmpt_a_code C) (cmpt_e_pcc C) (cmpt_code C).
  Definition cmpt_cgp_mregion (C: cmpt) : gmap Addr Word :=
    mkregion (cmpt_b_cgp C) (cmpt_e_cgp C) (cmpt_data C).
  Definition cmpt_exp_tbl_mregion (C: cmpt) : gmap Addr Word :=
    let pcc_word := WCap RX Global (cmpt_b_pcc C) (cmpt_e_pcc C) (cmpt_a_code C) in
    let cgp_word := WCap RW Global (cmpt_b_cgp C) (cmpt_e_cgp C) (cmpt_b_cgp C) in
    mkregion (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_cgp C) [pcc_word] ∪
      mkregion (cmpt_exp_tbl_cgp C) (cmpt_exp_tbl_entries_start C) [cgp_word] ∪
      mkregion (cmpt_exp_tbl_entries_start C) (cmpt_exp_tbl_entries_end C) (cmpt_exp_tbl_entries C)
  .

  Definition mk_initial_cmpt (C : cmpt) : gmap Addr Word :=
    cmpt_pcc_mregion C ∪
    cmpt_cgp_mregion C ∪
    cmpt_exp_tbl_mregion C.

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

        b_trusted_stack : Addr;
        e_trusted_stack : Addr;
        trusted_stack_content : list Word;

        trusted_stack_size :
        (b_trusted_stack + length trusted_stack_content)%a = Some e_trusted_stack ;

        (* compartment's stack *)
        b_stack : Addr;
        e_stack : Addr;
        stack_content : list Word;

        stack_size :
        (b_stack + length stack_content)%a = Some e_stack ;

        switcher_disjointness :
        (finz.seq_between b_switcher e_switcher) ## (finz.seq_between b_trusted_stack e_trusted_stack)
        ∧ (finz.seq_between b_switcher e_switcher) ## (finz.seq_between b_stack e_stack)
        ∧ (finz.seq_between b_trusted_stack e_trusted_stack) ## (finz.seq_between b_stack e_stack)
      }.

  Definition cmpt_switcher_code_region `{MachineParameters} (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_switcher Cswitcher) (e_switcher Cswitcher)).

  Definition cmpt_switcher_trusted_stack_region `{MachineParameters} (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_trusted_stack Cswitcher) (e_trusted_stack Cswitcher)).

  Definition cmpt_switcher_stack_region `{MachineParameters} (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_stack Cswitcher) (e_stack Cswitcher)).

  Definition cmpt_switcher_region `{MachineParameters} (Cswitcher : cmptSwitcher) : list Addr :=
    (cmpt_switcher_code_region Cswitcher)
      ∪ (cmpt_switcher_trusted_stack_region Cswitcher)
      ∪ (cmpt_switcher_stack_region Cswitcher).

  Definition cmpt_switcher_code_mregion
    `{MachineParameters} (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    let ot := (ot_switcher Cswitcher) in
    let switcher_sealing := (WSealRange (true,true) Global ot (ot^+1)%ot ot) in
    mkregion (b_switcher Cswitcher) (a_switcher_cc Cswitcher) [switcher_sealing]
      ∪ mkregion (a_switcher_cc Cswitcher) (e_switcher Cswitcher) switcher_instrs .
  Definition cmpt_switcher_trusted_stack_mregion
    `{MachineParameters} (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    mkregion (b_trusted_stack Cswitcher) (e_trusted_stack Cswitcher) (trusted_stack_content Cswitcher).
  Definition cmpt_switcher_stack_mregion
    `{MachineParameters} (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    mkregion (b_stack Cswitcher) (e_stack Cswitcher) (stack_content Cswitcher).

  Definition mk_initial_switcher `{MachineParameters} (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    cmpt_switcher_code_mregion Cswitcher ∪
    cmpt_switcher_trusted_stack_mregion Cswitcher ∪
    cmpt_switcher_stack_mregion Cswitcher.

  Definition switcher_cmpt_disjoint
    `{MachineParameters} (C : cmpt) (Cswitcher : cmptSwitcher) : Prop :=
    (cmpt_switcher_region Cswitcher) ## (cmpt_region C).

  Record cmptAssert `{MachineParameters} : Type :=
    mkCmptAssert {
        b_assert : Addr ;
        e_assert : Addr ;
        cap_assert : Addr ;
        flag_assert : Addr ;

        assert_code_size :
        (b_assert + length assert_subroutine_instrs)%a = Some cap_assert ;
        assert_cap_size :
        (cap_assert + 1)%a = Some e_assert;

        assert_flag_size :
        (flag_assert + 1)%a = Some (flag_assert ^+ 1)%a;
      }.

  Definition cmpt_assert_code_region `{MachineParameters} (Cassert : cmptAssert) :=
    (finz.seq_between (b_assert Cassert) (cap_assert Cassert)).
  Definition cmpt_assert_cap_region `{MachineParameters} (Cassert : cmptAssert) :=
    (finz.seq_between (cap_assert Cassert) (e_assert Cassert)).
  Definition cmpt_assert_flag_region `{MachineParameters} (Cassert : cmptAssert) :=
    (finz.seq_between (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a).
  Definition cmpt_assert_region `{MachineParameters} (Cassert : cmptAssert) : list Addr :=
    (cmpt_assert_code_region Cassert) ∪
    (cmpt_assert_cap_region Cassert) ∪
    (cmpt_assert_flag_region Cassert).

  Definition cmpt_assert_code_mregion `{MachineParameters} (Cassert : cmptAssert) :=
    mkregion (b_assert Cassert) (cap_assert Cassert) assert_subroutine_instrs.
  Definition cmpt_assert_cap_mregion `{MachineParameters} (Cassert : cmptAssert) :=
    mkregion (cap_assert Cassert) (e_assert Cassert)
      [WCap RW Global (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a (flag_assert Cassert)].
  Definition cmpt_assert_flag_mregion `{MachineParameters} (Cassert : cmptAssert) :=
    mkregion (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a [WInt 0].

  Definition mk_initial_assert `{MachineParameters} (Cassert : cmptAssert) : gmap Addr Word :=
    cmpt_assert_code_mregion Cassert ∪
    cmpt_assert_cap_mregion Cassert ∪
    cmpt_assert_flag_mregion Cassert.

  Definition assert_cmpt_disjoint
    `{MachineParameters} (C : cmpt) (Cassert : cmptAssert) : Prop :=
    (cmpt_assert_region Cassert) ## (cmpt_region C).

  Definition assert_switcher_disjoint
    `{MachineParameters} (Cassert : cmptAssert) (Cswitcher : cmptSwitcher) : Prop :=
    (cmpt_assert_region Cassert) ## (cmpt_switcher_region Cswitcher).

Lemma disjoint_cmpts_mkinitial (A_cmpt B_cmpt : cmpt) :
  A_cmpt ## B_cmpt -> (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_cmpt B_cmpt).
Proof.
  intros Hdis.
  rewrite /mk_initial_cmpt.
  rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdis.
Admitted.

Lemma disjoint_switcher_cmpts_mkinitial (A_cmpt : cmpt) (switcher_cmpt : cmptSwitcher) :
  switcher_cmpt_disjoint A_cmpt switcher_cmpt ->
  (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_switcher switcher_cmpt).
Proof.
Admitted.

Lemma disjoint_assert_cmpts_mkinitial (A_cmpt : cmpt) (assert_cmpt : cmptAssert) :
  assert_cmpt_disjoint A_cmpt assert_cmpt ->
  (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_assert assert_cmpt).
Proof.
Admitted.

Lemma disjoint_assert_switcher_mkinitial (assert_cmpt : cmptAssert) (switcher_cmpt : cmptSwitcher) :
  assert_switcher_disjoint assert_cmpt (switcher_cmpt : cmptSwitcher) ->
  (mk_initial_assert assert_cmpt) ##ₘ (mk_initial_switcher switcher_cmpt).
Proof.
Admitted.



End CmptLayout.
