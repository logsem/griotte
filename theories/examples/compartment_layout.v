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
        cmpt_exp_tbl_entries_size : (cmpt_exp_tbl_entries_start + length cmpt_exp_tbl_entries)%a = Some cmpt_exp_tbl_entries_end;

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
    (finz.seq_between (cmpt_b_cgp C) (cmpt_e_cgp C)).

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
        (a_switcher_cc + length switcher_instrs)%a = Some e_switcher ;

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

  Lemma dom_cmpt_pcc_mregion (A_cmpt : cmpt) :
    dom (cmpt_pcc_mregion A_cmpt) = list_to_set (cmpt_pcc_region A_cmpt).
  Proof.
    pose proof (cmpt_import_size A_cmpt).
    pose proof (cmpt_code_size A_cmpt).

    rewrite /cmpt_pcc_mregion /cmpt_pcc_region.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try solve_addr.
    rewrite (finz_seq_between_split
               (cmpt_b_pcc A_cmpt)
               (cmpt_a_code A_cmpt)
               (cmpt_e_pcc A_cmpt)); last solve_addr.
    set_solver.
  Qed.
  Lemma dom_cmpt_cgp_mregion (A_cmpt : cmpt) :
    dom (cmpt_cgp_mregion A_cmpt) = list_to_set (cmpt_cgp_region A_cmpt).
  Proof.
    pose proof (cmpt_data_size A_cmpt).
    rewrite /cmpt_cgp_mregion /cmpt_cgp_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.
  Lemma dom_cmpt_exp_tbl_mregion (A_cmpt : cmpt) :
    dom (cmpt_exp_tbl_mregion A_cmpt) = list_to_set (cmpt_exp_tbl_region A_cmpt).
  Proof.
    pose proof (cmpt_exp_tbl_pcc_size A_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size A_cmpt).
    pose proof (cmpt_exp_tbl_entries_size A_cmpt).
    rewrite /cmpt_exp_tbl_mregion /cmpt_exp_tbl_region.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try solve_addr.
    rewrite (finz_seq_between_split
               (cmpt_exp_tbl_pcc A_cmpt)
               (cmpt_exp_tbl_cgp A_cmpt)
               (cmpt_exp_tbl_entries_end A_cmpt)); last solve_addr.
    rewrite (finz_seq_between_split
               (cmpt_exp_tbl_cgp A_cmpt)
               (cmpt_exp_tbl_entries_start A_cmpt)
               (cmpt_exp_tbl_entries_end A_cmpt)); last solve_addr.
    set_solver.
  Qed.

  Lemma disjoint_cmpts_mkinitial (A_cmpt B_cmpt : cmpt) :
    A_cmpt ## B_cmpt -> (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_cmpt B_cmpt).
  Proof.
    intros Hdis.
    apply map_disjoint_dom_2.
    rewrite /mk_initial_cmpt.
    rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdis.
    apply list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.
    do 4 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_exp_tbl_mregion.
    done.
  Qed.

  Lemma dom_switcher_code_mregion (switcher_cmpt : cmptSwitcher) :
    dom (cmpt_switcher_code_mregion switcher_cmpt) =
    list_to_set (cmpt_switcher_code_region switcher_cmpt).
  Proof.
    pose proof (switcher_size switcher_cmpt).
    pose proof (switcher_cc_entry_point switcher_cmpt).
    rewrite /cmpt_switcher_code_mregion /cmpt_switcher_code_region.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try solve_addr.
    rewrite (finz_seq_between_split
               (b_switcher switcher_cmpt)
               (a_switcher_cc switcher_cmpt)
               (e_switcher switcher_cmpt)); last solve_addr.
    set_solver.
  Qed.
  Lemma dom_switcher_trusted_stack_mregion (switcher_cmpt : cmptSwitcher) :
    dom (cmpt_switcher_trusted_stack_mregion switcher_cmpt) =
    list_to_set (cmpt_switcher_trusted_stack_region switcher_cmpt).
  Proof.
    pose proof (trusted_stack_size switcher_cmpt).
    rewrite /cmpt_switcher_trusted_stack_mregion /cmpt_switcher_trusted_stack_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.
  Lemma dom_switcher_stack_mregion (switcher_cmpt : cmptSwitcher) :
    dom (cmpt_switcher_stack_mregion switcher_cmpt) =
    list_to_set (cmpt_switcher_stack_region switcher_cmpt).
  Proof.
    pose proof (stack_size switcher_cmpt).
    rewrite /cmpt_switcher_stack_mregion /cmpt_switcher_stack_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.

  Lemma dom_assert_code_mregion (assert_cmpt : cmptAssert) :
    dom (cmpt_assert_code_mregion assert_cmpt) = list_to_set (cmpt_assert_code_region assert_cmpt).
  Proof.
    pose proof (assert_code_size assert_cmpt).
    rewrite /cmpt_assert_code_mregion /cmpt_assert_code_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.
  Lemma dom_assert_cap_mregion (assert_cmpt : cmptAssert) :
    dom (cmpt_assert_cap_mregion assert_cmpt) = list_to_set (cmpt_assert_cap_region assert_cmpt).
  Proof.
    pose proof (assert_cap_size assert_cmpt).
    rewrite /cmpt_assert_cap_mregion /cmpt_assert_cap_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.
  Lemma dom_assert_flag_mregion (assert_cmpt : cmptAssert) :
    dom (cmpt_assert_flag_mregion assert_cmpt) = list_to_set (cmpt_assert_flag_region assert_cmpt).
  Proof.
    pose proof (assert_flag_size assert_cmpt).
    rewrite /cmpt_assert_flag_mregion /cmpt_assert_flag_region.
    repeat rewrite dom_mkregion_eq; try solve_addr.
  Qed.

  Lemma disjoint_switcher_cmpts_mkinitial (A_cmpt : cmpt) (switcher_cmpt : cmptSwitcher) :
    switcher_cmpt_disjoint A_cmpt switcher_cmpt ->
    (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_switcher switcher_cmpt).
  Proof.
    intros Hdis.
    apply map_disjoint_dom_2.
    rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_region in Hdis.
    apply list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.

    rewrite /mk_initial_cmpt /mk_initial_switcher.
    do 4 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_exp_tbl_mregion.
    rewrite !dom_switcher_code_mregion.
    rewrite !dom_switcher_trusted_stack_mregion.
    rewrite !dom_switcher_stack_mregion.
    set_solver.
  Qed.

  Lemma disjoint_assert_cmpts_mkinitial (A_cmpt : cmpt) (assert_cmpt : cmptAssert) :
    assert_cmpt_disjoint A_cmpt assert_cmpt ->
    (mk_initial_cmpt A_cmpt) ##ₘ (mk_initial_assert assert_cmpt).
  Proof.
    intros Hdis.
    apply map_disjoint_dom_2.
    rewrite /assert_cmpt_disjoint /cmpt_assert_region /cmpt_region in Hdis.
    apply list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.

    rewrite /mk_initial_cmpt /mk_initial_assert.
    do 4 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_exp_tbl_mregion.
    rewrite !dom_assert_code_mregion.
    rewrite !dom_assert_cap_mregion.
    rewrite !dom_assert_flag_mregion.
    set_solver.
  Qed.

  Lemma disjoint_assert_switcher_mkinitial (assert_cmpt : cmptAssert) (switcher_cmpt : cmptSwitcher) :
    assert_switcher_disjoint assert_cmpt (switcher_cmpt : cmptSwitcher) ->
    (mk_initial_assert assert_cmpt) ##ₘ (mk_initial_switcher switcher_cmpt).
  Proof.
    intros Hdis.
    apply map_disjoint_dom_2.
    rewrite /assert_switcher_disjoint /cmpt_assert_region /cmpt_switcher_region in Hdis.
    apply list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.

    rewrite /mk_initial_switcher /mk_initial_assert.
    do 4 rewrite dom_union_L.
    rewrite !dom_assert_code_mregion.
    rewrite !dom_assert_cap_mregion.
    rewrite !dom_assert_flag_mregion.
    rewrite !dom_switcher_code_mregion.
    rewrite !dom_switcher_trusted_stack_mregion.
    rewrite !dom_switcher_stack_mregion.
    set_solver.
  Qed.

  Lemma cmpt_assert_flag_mregion_disjoint (assert_cmpt : cmptAssert) :
    cmpt_assert_code_mregion assert_cmpt ∪ cmpt_assert_cap_mregion assert_cmpt
      ##ₘ cmpt_assert_flag_mregion assert_cmpt.
  Proof.
  Admitted.

  Lemma cmpt_assert_cap_mregion_disjoint (assert_cmpt : cmptAssert) :
    cmpt_assert_code_mregion assert_cmpt ##ₘ cmpt_assert_cap_mregion assert_cmpt.
  Proof.
  Admitted.

  Lemma cmpt_switcher_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    cmpt_switcher_code_mregion switcher_cmpt ∪ cmpt_switcher_trusted_stack_mregion switcher_cmpt
      ##ₘ cmpt_switcher_stack_mregion switcher_cmpt.
  Proof.
  Admitted.
  Lemma cmpt_switcher_trusted_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    cmpt_switcher_code_mregion switcher_cmpt
      ##ₘ cmpt_switcher_trusted_stack_mregion switcher_cmpt.
  Proof.
  Admitted.

  Lemma cmpt_switcher_code_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    mkregion (b_switcher switcher_cmpt) (a_switcher_cc switcher_cmpt)
      [WSealRange (true, true) Global (ot_switcher switcher_cmpt)
         (ot_switcher switcher_cmpt ^+ 1)%f (ot_switcher switcher_cmpt)]
      ##ₘ mkregion (a_switcher_cc switcher_cmpt) (e_switcher switcher_cmpt) switcher_instrs.
  Proof.
  Admitted.

  Lemma cmpt_exp_tbl_disjoint (B_cmpt : cmpt) :
    cmpt_pcc_mregion B_cmpt ∪ cmpt_cgp_mregion B_cmpt ##ₘ cmpt_exp_tbl_mregion B_cmpt.
  Proof.
  Admitted.
  Lemma cmpt_cgp_disjoint (B_cmpt : cmpt) :
    cmpt_pcc_mregion B_cmpt ##ₘ cmpt_cgp_mregion B_cmpt .
  Proof.
  Admitted.
  Lemma cmpt_code_disjoint (B_cmpt : cmpt) :
    mkregion (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt) (cmpt_imports B_cmpt)
      ##ₘ mkregion (cmpt_a_code B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_code B_cmpt).
  Proof.
  Admitted.

End CmptLayout.
