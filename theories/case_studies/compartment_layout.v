From griotte Require Import proofmode machine_parameters allocator_resources.
From griotte Require Import switcher assert.
From griotte Require Import disjoint_regions_tactics mkregion_helpers.

Section CmptLayout.
  Context `{MP: MachineParameters}.

  Record cmpt : Type :=
    mkCmpt {
        cmpt_b_pcc : Addr;
        cmpt_a_code : Addr;
        cmpt_e_pcc : Addr;

        cmpt_b_cgp : Addr;
        cmpt_e_cgp : Addr;

        cmpt_b_static_sealed : Addr;
        cmpt_e_static_sealed : Addr;

        cmpt_exp_tbl_pcc : Addr;
        cmpt_exp_tbl_cgp : Addr;
        cmpt_exp_tbl_entries_start : Addr;
        cmpt_exp_tbl_entries_end : Addr;

        cmpt_imports : list Word;
        cmpt_code : list Word;
        cmpt_data : list Word;
        cmpt_static_sealed : list Word;
        cmpt_exp_tbl_entries : list Word;

        cmpt_import_size : (cmpt_b_pcc + length cmpt_imports)%a = Some cmpt_a_code;
        cmpt_code_size : (cmpt_a_code + length cmpt_code)%a = Some cmpt_e_pcc;
        cmpt_data_size : (cmpt_b_cgp + length cmpt_data)%a = Some cmpt_e_cgp;
        cmpt_static_sealed_size : (cmpt_b_static_sealed + length cmpt_static_sealed)%a = Some cmpt_e_static_sealed;
        cmpt_exp_tbl_pcc_size : (cmpt_exp_tbl_pcc + 1)%a = Some cmpt_exp_tbl_cgp;
        cmpt_exp_tbl_cgp_size : (cmpt_exp_tbl_cgp + 1)%a = Some cmpt_exp_tbl_entries_start;
        cmpt_exp_tbl_entries_size : (cmpt_exp_tbl_entries_start + length cmpt_exp_tbl_entries)%a = Some cmpt_exp_tbl_entries_end;

        cmpt_disjointness :
        ## [
            (finz.seq_between cmpt_b_pcc cmpt_e_pcc) ;
            (finz.seq_between cmpt_b_cgp cmpt_e_cgp) ;
            (finz.seq_between cmpt_b_static_sealed cmpt_e_static_sealed) ;
            (finz.seq_between cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end)
          ];

        cmpt_pcc_disjoint_from_mmio : disjoint_from_mmio cmpt_b_pcc cmpt_e_pcc;
        cmpt_pcc_not_heap_range : not_heap_range cmpt_b_pcc cmpt_e_pcc;
        cmpt_cgp_disjoint_from_mmio : disjoint_from_mmio cmpt_b_cgp cmpt_e_cgp;
        cmpt_cgp_not_heap_range : not_heap_range cmpt_b_cgp cmpt_e_cgp;
        cmpt_exp_tbl_disjoint_from_mmio :
        disjoint_from_mmio cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end;
        cmpt_static_sealed_disjoint_from_mmio :
        disjoint_from_mmio cmpt_b_static_sealed cmpt_e_static_sealed;
        cmpt_exp_tbl_not_heap_range :
        not_heap_range cmpt_exp_tbl_pcc cmpt_exp_tbl_entries_end;
        cmpt_static_sealed_not_heap_range :
        not_heap_range cmpt_b_static_sealed cmpt_e_static_sealed
      }.

  Definition cmpt_pcc_disjoint_from_shadow (C : cmpt) :
    disjoint_from_shadow (cmpt_b_pcc C) (cmpt_e_pcc C) :=
    disjoint_from_mmio_shadow _ _ (cmpt_pcc_disjoint_from_mmio C).
  Definition cmpt_cgp_disjoint_from_shadow (C : cmpt) :
    disjoint_from_shadow (cmpt_b_cgp C) (cmpt_e_cgp C) :=
    disjoint_from_mmio_shadow _ _ (cmpt_cgp_disjoint_from_mmio C).
  Definition cmpt_exp_tbl_disjoint_from_shadow (C : cmpt) :
    disjoint_from_shadow (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_entries_end C) :=
    disjoint_from_mmio_shadow _ _ (cmpt_exp_tbl_disjoint_from_mmio C).
  Definition cmpt_static_sealed_disjoint_from_shadow (C : cmpt) :
    disjoint_from_shadow (cmpt_b_static_sealed C) (cmpt_e_static_sealed C) :=
    disjoint_from_mmio_shadow _ _ (cmpt_static_sealed_disjoint_from_mmio C).
  Definition cmpt_pcc_disjoint_from_heap (C : cmpt) :
    disjoint_from_heap (cmpt_b_pcc C) (cmpt_e_pcc C) :=
    proj2 (cmpt_pcc_not_heap_range C).
  Definition cmpt_cgp_disjoint_from_heap (C : cmpt) :
    disjoint_from_heap (cmpt_b_cgp C) (cmpt_e_cgp C) :=
    proj2 (cmpt_cgp_not_heap_range C).
  Definition cmpt_exp_tbl_disjoint_from_heap (C : cmpt) :
    disjoint_from_heap (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_entries_end C) :=
    proj2 (cmpt_exp_tbl_not_heap_range C).
  Definition cmpt_static_sealed_disjoint_from_heap (C : cmpt) :
    disjoint_from_heap (cmpt_b_static_sealed C) (cmpt_e_static_sealed C) :=
    proj2 (cmpt_static_sealed_not_heap_range C).
  Definition cmpt_pcc_base_not_heap (C : cmpt) :
    is_heap_address (cmpt_b_pcc C) = false :=
    proj1 (cmpt_pcc_not_heap_range C).
  Definition cmpt_cgp_base_not_heap (C : cmpt) :
    is_heap_address (cmpt_b_cgp C) = false :=
    proj1 (cmpt_cgp_not_heap_range C).
  Definition cmpt_exp_tbl_base_not_heap (C : cmpt) :
    is_heap_address (cmpt_exp_tbl_pcc C) = false :=
    proj1 (cmpt_exp_tbl_not_heap_range C).
  Definition cmpt_static_sealed_base_not_heap (C : cmpt) :
    is_heap_address (cmpt_b_static_sealed C) = false :=
    proj1 (cmpt_static_sealed_not_heap_range C).

  Definition cmpt_pcc_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_b_pcc C) (cmpt_e_pcc C)).

  Definition cmpt_cgp_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_b_cgp C) (cmpt_e_cgp C)).

  Definition cmpt_static_sealed_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_b_static_sealed C) (cmpt_e_static_sealed C)).

  Definition cmpt_exp_tbl_region (C : cmpt) : list Addr :=
    (finz.seq_between (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_entries_end C)).

  Definition cmpt_region (C : cmpt) : list Addr :=
   (cmpt_pcc_region C) ∪ (cmpt_cgp_region C) ∪ (cmpt_static_sealed_region C) ∪ (cmpt_exp_tbl_region C).

  Definition disjoint_cmpt (C1 C2 : cmpt) : Prop :=
    cmpt_region C1 ## cmpt_region C2.

  Global Instance Cmpt_Disjoint : Disjoint cmpt := disjoint_cmpt.

  Definition cmpt_pcc_mregion (C: cmpt) : gmap Addr Word :=
    mkregion (cmpt_b_pcc C) (cmpt_a_code C) (cmpt_imports C) ∪
      mkregion (cmpt_a_code C) (cmpt_e_pcc C) (cmpt_code C).
  Definition cmpt_cgp_mregion (C: cmpt) : gmap Addr Word :=
    mkregion (cmpt_b_cgp C) (cmpt_e_cgp C) (cmpt_data C).
  Definition cmpt_static_sealed_mregion (C: cmpt) : gmap Addr Word :=
    mkregion (cmpt_b_static_sealed C) (cmpt_e_static_sealed C) (cmpt_static_sealed C).
  Definition cmpt_exp_tbl_mregion (C: cmpt) : gmap Addr Word :=
    let pcc_word := WCap true RX Global (cmpt_b_pcc C) (cmpt_e_pcc C) (cmpt_b_pcc C) in
    let cgp_word := WCap true RW Global (cmpt_b_cgp C) (cmpt_e_cgp C) (cmpt_b_cgp C) in
    mkregion (cmpt_exp_tbl_pcc C) (cmpt_exp_tbl_cgp C) [pcc_word] ∪
      mkregion (cmpt_exp_tbl_cgp C) (cmpt_exp_tbl_entries_start C) [cgp_word] ∪
      mkregion (cmpt_exp_tbl_entries_start C) (cmpt_exp_tbl_entries_end C) (cmpt_exp_tbl_entries C)
  .

  Definition mk_initial_cmpt (C : cmpt) : gmap Addr Word :=
    cmpt_pcc_mregion C ∪
    cmpt_cgp_mregion C ∪
    cmpt_static_sealed_mregion C ∪
    cmpt_exp_tbl_mregion C.

  Record cmptSwitcher : Type :=
    mkCmptSwitcher {
        b_switcher : Addr ;
        e_switcher : Addr ;
        a_switcher_call : Addr ;
        a_switcher_return : Addr ;

        ot_switcher : OType ;

        b_trusted_stack : Addr;
        e_trusted_stack : Addr;

        switcher_size :
        (a_switcher_call + length switcher_instrs)%a = Some e_switcher ;

        switcher_call_entry_point :
        (b_switcher + 1)%a = Some a_switcher_call ;

        switcher_return_entry_point :
        (b_switcher + (1 + length switcher_call_instrs) )%a = Some a_switcher_return ;

        ot_switcher_size :
        (ot_switcher < ot_switcher ^+ 1)%ot;

        trusted_stack_content : list Word;

        trusted_stack_size :
        (b_trusted_stack + length trusted_stack_content)%a = Some e_trusted_stack ;

        trusted_stack_content_base_zeroed :
        head trusted_stack_content = Some (WInt 0);
        trusted_stack_content_ints :
        Forall is_z trusted_stack_content;

        (* compartment's stack *)
        b_stack : Addr;
        e_stack : Addr;
        stack_content : list Word;

        stack_size :
        (b_stack + length stack_content)%a = Some e_stack ;

        switcher_disjointness :
        (finz.seq_between b_switcher e_switcher) ## (finz.seq_between b_trusted_stack e_trusted_stack)
        ∧ (finz.seq_between b_switcher e_switcher) ## (finz.seq_between b_stack e_stack)
        ∧ (finz.seq_between b_trusted_stack e_trusted_stack) ## (finz.seq_between b_stack e_stack);

        trusted_stack_disjoint_from_mmio :
        disjoint_from_mmio b_trusted_stack e_trusted_stack;

        switcher_base_not_shadow : is_shadow_address b_switcher = false;
        switcher_not_heap_range : not_heap_range b_switcher e_switcher;

        stack_disjoint_from_mmio : disjoint_from_mmio b_stack e_stack;
        stack_disjoint_from_heap : disjoint_from_heap b_stack e_stack;

        switcher_disjoint_from_mmio : disjoint_from_mmio b_switcher e_switcher;
      }.

  Definition trusted_stack_disjoint_from_shadow (C : cmptSwitcher) :
    disjoint_from_shadow (b_trusted_stack C) (e_trusted_stack C) :=
    disjoint_from_mmio_shadow _ _ (trusted_stack_disjoint_from_mmio C).
  Definition stack_disjoint_from_shadow (C : cmptSwitcher) :
    disjoint_from_shadow (b_stack C) (e_stack C) :=
    disjoint_from_mmio_shadow _ _ (stack_disjoint_from_mmio C).

  Definition switcher_base_not_heap (C : cmptSwitcher) :
    is_heap_address (b_switcher C) = false :=
    proj1 (switcher_not_heap_range C).
  Definition switcher_disjoint_from_heap (C : cmptSwitcher) :
    disjoint_from_heap (b_switcher C) (e_switcher C) :=
    proj2 (switcher_not_heap_range C).


  Global Instance cmptSwitcher_switcherLayout (switcher_cmpt : cmptSwitcher) : switcherLayout.
  Proof.
    refine (@mkSwitcherLayout
              (b_switcher switcher_cmpt)
              (e_switcher switcher_cmpt)
              (a_switcher_call switcher_cmpt)
              (a_switcher_return switcher_cmpt)
              (ot_switcher switcher_cmpt)
              (b_trusted_stack switcher_cmpt)
              (e_trusted_stack switcher_cmpt)
           ).
  Defined.

  Definition cmpt_switcher_code_region (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_switcher Cswitcher) (e_switcher Cswitcher)).

  Definition cmpt_switcher_trusted_stack_region (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_trusted_stack Cswitcher) (e_trusted_stack Cswitcher)).

  Definition cmpt_switcher_stack_region (Cswitcher : cmptSwitcher) :=
    (finz.seq_between (b_stack Cswitcher) (e_stack Cswitcher)).

  Definition cmpt_switcher_region (Cswitcher : cmptSwitcher) : list Addr :=
    (cmpt_switcher_code_region Cswitcher)
      ∪ (cmpt_switcher_trusted_stack_region Cswitcher)
      ∪ (cmpt_switcher_stack_region Cswitcher).

  Definition cmpt_switcher_code_mregion
    (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    let ot := (ot_switcher Cswitcher) in
    let switcher_sealing := (WSealRange true (true,true) Global ot (ot^+1)%ot ot) in
    mkregion (b_switcher Cswitcher) (a_switcher_call Cswitcher) [switcher_sealing]
      ∪ mkregion (a_switcher_call Cswitcher) (e_switcher Cswitcher) switcher_instrs .
  Definition cmpt_switcher_trusted_stack_mregion
     (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    mkregion (b_trusted_stack Cswitcher) (e_trusted_stack Cswitcher) (trusted_stack_content Cswitcher).
  Definition cmpt_switcher_stack_mregion
     (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    mkregion (b_stack Cswitcher) (e_stack Cswitcher) (stack_content Cswitcher).

  Definition mk_initial_switcher (Cswitcher : cmptSwitcher) : gmap Addr Word :=
    cmpt_switcher_code_mregion Cswitcher ∪
    cmpt_switcher_trusted_stack_mregion Cswitcher ∪
    cmpt_switcher_stack_mregion Cswitcher.

  Definition switcher_cmpt_disjoint
    (C : cmpt) (Cswitcher : cmptSwitcher) : Prop :=
    (cmpt_switcher_region Cswitcher) ## (cmpt_region C).

  Record cmptAssert : Type :=
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

        assert_code_nonheap : is_heap_address b_assert = false;

        assert_flag_disjoint :
        (finz.seq_between b_assert e_assert) ##
        (finz.seq_between flag_assert (flag_assert ^+ 1)%a);

        assert_disjoint_from_mmio : disjoint_from_mmio b_assert e_assert;
        assert_flag_disjoint_from_mmio :
        disjoint_from_mmio flag_assert (flag_assert ^+ 1)%a
      }.

  Global Instance cmptAssert_assertLayout (assert_cmpt : cmptAssert) : assertLayout.
  Proof.
    refine (@mkAssertLayout
              (b_assert assert_cmpt)
              (e_assert assert_cmpt)
              (flag_assert assert_cmpt)
           ).
  Defined.

  Definition cmpt_assert_code_region (Cassert : cmptAssert) :=
    (finz.seq_between (b_assert Cassert) (cap_assert Cassert)).
  Definition cmpt_assert_cap_region (Cassert : cmptAssert) :=
    (finz.seq_between (cap_assert Cassert) (e_assert Cassert)).
  Definition cmpt_assert_flag_region (Cassert : cmptAssert) :=
    (finz.seq_between (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a).
  Definition cmpt_assert_region (Cassert : cmptAssert) : list Addr :=
    (cmpt_assert_code_region Cassert) ∪
    (cmpt_assert_cap_region Cassert) ∪
    (cmpt_assert_flag_region Cassert).

  Definition cmpt_assert_code_mregion (Cassert : cmptAssert) :=
    mkregion (b_assert Cassert) (cap_assert Cassert) assert_subroutine_instrs.
  Definition cmpt_assert_cap_mregion (Cassert : cmptAssert) :=
    mkregion (cap_assert Cassert) (e_assert Cassert)
      [WCap true RW Global (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a (flag_assert Cassert)].
  Definition cmpt_assert_flag_mregion (Cassert : cmptAssert) :=
    mkregion (flag_assert Cassert) ((flag_assert Cassert) ^+1)%a [WInt 0].

  Definition mk_initial_assert (Cassert : cmptAssert) : gmap Addr Word :=
    cmpt_assert_code_mregion Cassert ∪
    cmpt_assert_cap_mregion Cassert ∪
    cmpt_assert_flag_mregion Cassert.

  Definition assert_cmpt_disjoint
    (C : cmpt) (Cassert : cmptAssert) : Prop :=
    (cmpt_assert_region Cassert) ## (cmpt_region C).

  Definition assert_switcher_disjoint
    (Cassert : cmptAssert) (Cswitcher : cmptSwitcher) : Prop :=
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
  Lemma dom_cmpt_static_sealed_mregion (A_cmpt : cmpt) :
    dom (cmpt_static_sealed_mregion A_cmpt) = list_to_set (cmpt_static_sealed_region A_cmpt).
  Proof.
    pose proof (cmpt_static_sealed_size A_cmpt).
    rewrite /cmpt_static_sealed_mregion /cmpt_static_sealed_region.
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
    apply stdpp_extra.list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.
    do 6 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_static_sealed_mregion.
    rewrite !dom_cmpt_exp_tbl_mregion.
    done.
  Qed.

  Lemma dom_switcher_code_mregion (switcher_cmpt : cmptSwitcher) :
    dom (cmpt_switcher_code_mregion switcher_cmpt) =
    list_to_set (cmpt_switcher_code_region switcher_cmpt).
  Proof.
    pose proof (switcher_size switcher_cmpt).
    pose proof (switcher_call_entry_point switcher_cmpt).
    rewrite /cmpt_switcher_code_mregion /cmpt_switcher_code_region.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try solve_addr.
    rewrite (finz_seq_between_split
               (b_switcher switcher_cmpt)
               (a_switcher_call switcher_cmpt)
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
    apply stdpp_extra.list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.
    rewrite /mk_initial_cmpt /mk_initial_switcher.
    do 5 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_static_sealed_mregion.
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
    apply stdpp_extra.list_to_set_disj in Hdis.
    repeat rewrite list_to_set_app_L in Hdis.

    rewrite /mk_initial_cmpt /mk_initial_assert.
    do 5 rewrite dom_union_L.
    rewrite !dom_cmpt_pcc_mregion.
    rewrite !dom_cmpt_cgp_mregion.
    rewrite !dom_cmpt_static_sealed_mregion.
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
    apply stdpp_extra.list_to_set_disj in Hdis.
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
    apply map_disjoint_dom_2.
    rewrite dom_union_L.
    pose proof (assert_flag_disjoint assert_cmpt).
    pose proof (assert_code_size assert_cmpt).
    pose proof (assert_cap_size assert_cmpt).
    pose proof (assert_flag_size assert_cmpt).
    rewrite /cmpt_assert_code_mregion /cmpt_assert_cap_mregion.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    rewrite (finz_seq_between_split
               (b_assert assert_cmpt)
               (cap_assert assert_cmpt)
               (e_assert assert_cmpt)) in H ; last solve_addr.
    set_solver.
  Qed.

  Lemma cmpt_assert_cap_mregion_disjoint (assert_cmpt : cmptAssert) :
    cmpt_assert_code_mregion assert_cmpt ##ₘ cmpt_assert_cap_mregion assert_cmpt.
  Proof.
    apply map_disjoint_dom_2.
    pose proof (assert_code_size assert_cmpt).
    pose proof (assert_cap_size assert_cmpt).
    rewrite /cmpt_assert_code_mregion /cmpt_assert_cap_mregion.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    rewrite !elem_of_finz_seq_between in Ha,Ha'.
    solve_addr.
  Qed.

  Lemma cmpt_switcher_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    cmpt_switcher_code_mregion switcher_cmpt ∪ cmpt_switcher_trusted_stack_mregion switcher_cmpt
      ##ₘ cmpt_switcher_stack_mregion switcher_cmpt.
  Proof.
    apply map_disjoint_dom_2.
    pose proof (switcher_disjointness switcher_cmpt) as (_ & ? & ?).
    pose proof (switcher_call_entry_point switcher_cmpt).
    pose proof (switcher_size switcher_cmpt).
    pose proof (trusted_stack_size switcher_cmpt).
    pose proof (stack_size switcher_cmpt).
    rewrite /cmpt_switcher_code_mregion /cmpt_switcher_trusted_stack_mregion /cmpt_switcher_stack_mregion.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_union in Ha.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    destruct Ha as [ [Ha | Ha] | Ha].
    - rewrite elem_of_disjoint in H; eapply H; eauto.
      rewrite !elem_of_finz_seq_between in Ha,Ha' |- *.
      solve_addr.
    - rewrite elem_of_disjoint in H; eapply H; eauto.
      rewrite !elem_of_finz_seq_between in Ha,Ha' |- *.
      solve_addr.
    - rewrite elem_of_disjoint in H0; eapply H0; eauto.
  Qed.

  Lemma cmpt_switcher_trusted_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    cmpt_switcher_code_mregion switcher_cmpt
      ##ₘ cmpt_switcher_trusted_stack_mregion switcher_cmpt.
  Proof.
    apply map_disjoint_dom_2.
    pose proof (switcher_disjointness switcher_cmpt) as (? & _ & _).
    pose proof (switcher_call_entry_point switcher_cmpt).
    pose proof (switcher_size switcher_cmpt).
    pose proof (trusted_stack_size switcher_cmpt).
    rewrite /cmpt_switcher_code_mregion /cmpt_switcher_trusted_stack_mregion.
    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_union in Ha.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    destruct Ha as [ Ha | Ha].
    - rewrite elem_of_disjoint in H; eapply H; eauto.
      rewrite !elem_of_finz_seq_between in Ha,Ha' |- *.
      solve_addr.
    - rewrite elem_of_disjoint in H; eapply H; eauto.
      rewrite !elem_of_finz_seq_between in Ha,Ha' |- *.
      solve_addr.
  Qed.

  Lemma cmpt_switcher_code_stack_mregion_disjoint (switcher_cmpt : cmptSwitcher) :
    let ot := ot_switcher switcher_cmpt in
    mkregion (b_switcher switcher_cmpt) (a_switcher_call switcher_cmpt)
      [WSealRange true (true, true) Global ot (ot ^+ 1)%f ot]
      ##ₘ mkregion (a_switcher_call switcher_cmpt) (e_switcher switcher_cmpt) switcher_instrs.
  Proof.
    intro ot ; subst ot.
    apply map_disjoint_dom_2.
    pose proof (switcher_call_entry_point switcher_cmpt).
    pose proof (switcher_size switcher_cmpt).
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    rewrite !elem_of_finz_seq_between in Ha,Ha'.
    solve_addr.
  Qed.

  Lemma cmpt_exp_tbl_disjoint (B_cmpt : cmpt) :
    cmpt_pcc_mregion B_cmpt ∪ cmpt_cgp_mregion B_cmpt ∪ cmpt_static_sealed_mregion B_cmpt ##ₘ cmpt_exp_tbl_mregion B_cmpt.
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_disjointness B_cmpt) as Hdis.
    rewrite !disjoint_list_cons in Hdis.
    destruct Hdis as (?&?&?&_&_).
    rewrite !union_list_cons in H,H0,H1.
    rewrite union_list_nil in H,H0,H1.
    rewrite /union /Union_list in H,H0,H1.
    rewrite /empty /Empty_list in H,H0,H1.
    rewrite app_nil_r in H,H0,H1.
    rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion /cmpt_static_sealed_mregion /cmpt_exp_tbl_mregion.

    pose proof (cmpt_import_size B_cmpt).
    pose proof (cmpt_code_size B_cmpt).
    pose proof (cmpt_data_size B_cmpt).
    pose proof (cmpt_static_sealed_size B_cmpt).
    pose proof (cmpt_exp_tbl_pcc_size B_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size B_cmpt).
    pose proof (cmpt_exp_tbl_entries_size B_cmpt).

    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    rewrite -(list_to_set_app_L
                (finz.seq_between (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_cgp B_cmpt)) _).
    rewrite -(list_to_set_app_L _
                (finz.seq_between (cmpt_exp_tbl_entries_start B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt))
             ).
    rewrite -(list_to_set_app_L (finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt)) _).
    rewrite -!finz_seq_between_split; try solve_addr.
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_union in Ha.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    destruct Ha as [ Ha | Ha].
    - destruct Ha as [ Ha | Ha].
      + rewrite elem_of_disjoint in H; eapply H; eauto.
        rewrite !elem_of_app. by right;right.
      + rewrite elem_of_disjoint in H0; eapply H0; eauto.
        apply elem_of_app. by right.
    - rewrite elem_of_disjoint in H1; eapply H1; eauto.
  Qed.
  Lemma cmpt_static_sealed_disjoint (B_cmpt : cmpt) :
    cmpt_pcc_mregion B_cmpt ∪ cmpt_cgp_mregion B_cmpt ##ₘ cmpt_static_sealed_mregion B_cmpt .
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_disjointness B_cmpt) as Hdis.
    rewrite !disjoint_list_cons in Hdis.
    destruct Hdis as (?&?&?&_&_).
    rewrite !union_list_cons in H,H0,H1.
    rewrite union_list_nil in H,H0,H1.
    rewrite /union /Union_list in H,H0,H1.
    rewrite /empty /Empty_list in H,H0,H1.
    rewrite app_nil_r in H,H0,H1.
    rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion /cmpt_static_sealed_mregion.

    pose proof (cmpt_import_size B_cmpt).
    pose proof (cmpt_code_size B_cmpt).
    pose proof (cmpt_data_size B_cmpt).
    pose proof (cmpt_static_sealed_size B_cmpt).

    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    rewrite -(list_to_set_app_L (finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt)) _).
    rewrite -!finz_seq_between_split; try solve_addr.
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    rewrite !elem_of_union in Ha.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    destruct Ha as [ Ha | Ha].
    - rewrite elem_of_disjoint in H; eapply H; eauto.
      rewrite !elem_of_app. by right;left.
    - rewrite elem_of_disjoint in H0; eapply H0; eauto.
      rewrite !elem_of_app. by left.
  Qed.
  Lemma cmpt_cgp_disjoint (B_cmpt : cmpt) :
    cmpt_pcc_mregion B_cmpt ##ₘ cmpt_cgp_mregion B_cmpt .
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_disjointness B_cmpt) as Hdis.
    rewrite !disjoint_list_cons in Hdis.
    destruct Hdis as (?&?&_&_).
    rewrite !union_list_cons in H,H0.
    rewrite union_list_nil in H,H0.
    rewrite /union /Union_list in H,H0.
    rewrite /empty /Empty_list in H,H0.
    rewrite app_nil_r in H,H0.
    rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion.

    pose proof (cmpt_import_size B_cmpt).
    pose proof (cmpt_code_size B_cmpt).
    pose proof (cmpt_data_size B_cmpt).

    rewrite !dom_union_L.
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    rewrite -(list_to_set_app_L (finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt)) _).
    rewrite -!finz_seq_between_split; try solve_addr.
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    rewrite elem_of_disjoint in H; eapply H; eauto.
    rewrite !elem_of_app. by left.
  Qed.
  Lemma cmpt_code_disjoint (B_cmpt : cmpt) :
    mkregion (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt) (cmpt_imports B_cmpt)
      ##ₘ mkregion (cmpt_a_code B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_code B_cmpt).
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_import_size B_cmpt).
    pose proof (cmpt_code_size B_cmpt).
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set in Ha,Ha'.
    rewrite !elem_of_finz_seq_between in Ha,Ha'.
    solve_addr.
  Qed.
  Lemma cmpt_exp_tbl_entries_disjoint (B_cmpt : cmpt) :
    mkregion (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_cgp B_cmpt)
      [WCap true RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)]
      ∪ mkregion (cmpt_exp_tbl_cgp B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt)
      [WCap true RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)]
      ##ₘ mkregion (cmpt_exp_tbl_entries_start B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt) (cmpt_exp_tbl_entries B_cmpt).
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_disjointness B_cmpt) as Hdis.
    rewrite !disjoint_list_cons in Hdis.
    destruct Hdis as (?&?&_&?).
    rewrite !union_list_cons in H,H0.
    rewrite union_list_nil in H,H0.
    rewrite /union /Union_list in H,H0.
    rewrite /empty /Empty_list in H,H0.
    rewrite app_nil_r in H,H0.
    pose proof (cmpt_import_size B_cmpt).
    pose proof (cmpt_exp_tbl_pcc_size B_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size B_cmpt).
    pose proof (cmpt_exp_tbl_entries_size B_cmpt).
    repeat rewrite dom_mkregion_eq; try (solve_addr).
    rewrite /mkregion.
    rewrite finz_seq_between_cons /=; [rewrite zip_nil_r /=|solve_addr].
    rewrite finz_seq_between_cons /=; [rewrite zip_nil_r /=|solve_addr].
    rewrite dom_union_L !dom_insert_L !dom_empty_L !union_empty_r_L.
    rewrite disjoint_union_l
    ; split
    ; rewrite disjoint_singleton_l not_elem_of_list_to_set not_elem_of_finz_seq_between
    ; solve_addr.
  Qed.

  Lemma cmpt_exp_tbl_pcc_cgp_disjoint (B_cmpt : cmpt) :
    mkregion (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_cgp B_cmpt)
      [WCap true RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)]
      ##ₘ mkregion (cmpt_exp_tbl_cgp B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt)
      [WCap true RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)].
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_exp_tbl_pcc_size B_cmpt).
    pose proof (cmpt_exp_tbl_cgp_size B_cmpt).
    pose proof (cmpt_exp_tbl_entries_size B_cmpt).

    rewrite /mkregion.
    rewrite finz_seq_between_cons /=; [rewrite zip_nil_r /=|solve_addr].
    rewrite finz_seq_between_cons /=; [rewrite zip_nil_r /=|solve_addr].
    rewrite !dom_insert_L !dom_empty_L !union_empty_r_L.
    rewrite disjoint_singleton_l elem_of_singleton.
    solve_addr.
  Qed.

  Definition in_region (w : Word) (b e : Addr) :=
    match w with
    | WSealable (SCap _ p Global b' e' a) =>
        PermFlowsTo p RW (* at most RW capability: excludes WL, excludes XSR *)
        ∧ (b <= b')%a /\ (e' <= e)%a (* in between the bounds *)
    | _ => False
    end.

  Definition is_initial_data_word (B_cmpt : cmpt) :=
    (fun w => is_z w ∨ in_region w (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt)).

  Lemma exported_entry_point_disjoint
    (C1_cmpt C2_cmpt : cmpt) (t1 t2 : bool) (p1 p2 : Perm) (g1 g2 : Locality) (a1 a2 : Addr):
    C1_cmpt ## C2_cmpt ->
    (WCap t1 p1 g1 (cmpt_exp_tbl_pcc C1_cmpt) (cmpt_exp_tbl_entries_end C1_cmpt) a1)
      ≠
      (WCap t2 p2 g2 (cmpt_exp_tbl_pcc C2_cmpt) (cmpt_exp_tbl_entries_end C2_cmpt) a2).
  Proof.
    intros Hdisjoint H ; simplify_eq.
    rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
    assert (
        cmpt_exp_tbl_region C1_cmpt  ## cmpt_exp_tbl_region C2_cmpt
      ) as Hdis by set_solver+Hdisjoint.
    rewrite /cmpt_exp_tbl_region in Hdis.
    apply stdpp_extra.list_to_set_disj in Hdis.
    rewrite H2 H3 in Hdis.
    assert (
        list_to_set
          (finz.seq_between (cmpt_exp_tbl_pcc C2_cmpt) (cmpt_exp_tbl_entries_end C2_cmpt))
          ≠ (∅ : gset Addr)
      ) as Hemp; last set_solver.
    pose proof (cmpt_exp_tbl_pcc_size C2_cmpt) as Hc.
    pose proof (cmpt_exp_tbl_cgp_size C2_cmpt) as Hc'.
    pose proof (cmpt_exp_tbl_entries_size C2_cmpt) as Hc''.
    rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
    set_solver+.
  Qed.

  (** Initial memory never covers a memory-mapped address. *)
  Lemma mem_avoids_mmio_region (m : Mem) (b e : Addr) :
    disjoint_from_mmio b e →
    dom m ⊆ list_to_set (finz.seq_between b e) →
    mem_avoids_mmio m.
  Proof.
    intros Hmmio Hdom a Ha.
    apply (disjoint_from_mmio_not_in b e); first done.
    apply withinBounds_true_iff, elem_of_finz_seq_between.
    apply Hdom in Ha. by apply elem_of_list_to_set in Ha.
  Qed.

  Lemma mem_avoids_mmio_initial_heap : mem_avoids_mmio initial_heap_memory.
  Proof.
    intros a Ha.
    rewrite /initial_heap_memory /heap_addresses dom_gset_to_gmap
      elem_of_list_to_set in Ha.
    rewrite /is_mmio_address. apply orb_false_iff. split.
    - apply not_true_is_false. intros Hshadow.
      apply (heap_shadow_disjoint a); first done.
      apply elem_of_finz_seq_between, withinBounds_true_iff. exact Hshadow.
    - apply bool_decide_eq_false. intros ->.
      apply elem_of_finz_seq_between, withinBounds_true_iff in Ha.
      by rewrite revoker_not_heap in Ha.
  Qed.

  Lemma mem_avoids_mmio_initial_cmpt (C : cmpt) :
    mem_avoids_mmio (mk_initial_cmpt C).
  Proof.
    rewrite /mk_initial_cmpt.
    apply mem_avoids_mmio_union; [apply mem_avoids_mmio_union;
      [apply mem_avoids_mmio_union|]|].
    - eapply mem_avoids_mmio_region; first exact (cmpt_pcc_disjoint_from_mmio C).
      by rewrite dom_cmpt_pcc_mregion.
    - eapply mem_avoids_mmio_region; first exact (cmpt_cgp_disjoint_from_mmio C).
      by rewrite dom_cmpt_cgp_mregion.
    - eapply mem_avoids_mmio_region; first exact (cmpt_static_sealed_disjoint_from_mmio C).
      by rewrite dom_cmpt_static_sealed_mregion.
    - eapply mem_avoids_mmio_region; first exact (cmpt_exp_tbl_disjoint_from_mmio C).
      by rewrite dom_cmpt_exp_tbl_mregion.
  Qed.

  Lemma mem_avoids_mmio_initial_switcher (C : cmptSwitcher) :
    mem_avoids_mmio (mk_initial_switcher C).
  Proof.
    rewrite /mk_initial_switcher.
    apply mem_avoids_mmio_union; [apply mem_avoids_mmio_union|].
    - eapply mem_avoids_mmio_region; first exact (switcher_disjoint_from_mmio C).
      by rewrite dom_switcher_code_mregion.
    - eapply mem_avoids_mmio_region; first exact (trusted_stack_disjoint_from_mmio C).
      by rewrite dom_switcher_trusted_stack_mregion.
    - eapply mem_avoids_mmio_region; first exact (stack_disjoint_from_mmio C).
      by rewrite dom_switcher_stack_mregion.
  Qed.

  Lemma mem_avoids_mmio_initial_assert (C : cmptAssert) :
    mem_avoids_mmio (mk_initial_assert C).
  Proof.
    pose proof (assert_code_size C).
    pose proof (assert_cap_size C).
    rewrite /mk_initial_assert.
    apply mem_avoids_mmio_union; [apply mem_avoids_mmio_union|].
    - eapply mem_avoids_mmio_region; first exact (assert_disjoint_from_mmio C).
      rewrite dom_assert_code_mregion /cmpt_assert_code_region.
      intros a. rewrite !elem_of_list_to_set !elem_of_finz_seq_between. solve_addr.
    - eapply mem_avoids_mmio_region; first exact (assert_disjoint_from_mmio C).
      rewrite dom_assert_cap_mregion /cmpt_assert_cap_region.
      intros a. rewrite !elem_of_list_to_set !elem_of_finz_seq_between. solve_addr.
    - eapply mem_avoids_mmio_region; first exact (assert_flag_disjoint_from_mmio C).
      by rewrite dom_assert_flag_mregion.
  Qed.

  (** ** Heap roots of the initial memory

      The words of an initial memory with heap authority are based on the
      heap roots [H] of [cerise_ghost_init] ([gi_mem]). *)
  Definition word_rooted (H : gset Addr) (w : Word) : Prop :=
    ∀ b, get_tag w = true → heap_authority_base w = Some b → b ∈ H.

  Definition mem_rooted (H : gset Addr) (m : Mem) : Prop :=
    ∀ a w, m !! a = Some w → word_rooted H w.

  Lemma word_rooted_nonheap H w : heap_cap_base w = None → word_rooted H w.
  Proof.
    intros Hw b _ Hb. apply heap_authority_base_heap_cap_base in Hb. congruence.
  Qed.

  Lemma word_rooted_not_heap_cap H w : is_heap_cap w = false → word_rooted H w.
  Proof.
    intros Hw. apply word_rooted_nonheap. rewrite /is_heap_cap in Hw.
    by destruct (heap_cap_base w).
  Qed.

  Lemma word_rooted_not_heap_caps H (ws : list Word) :
    Forall (λ w, is_heap_cap w = false) ws → Forall (word_rooted H) ws.
  Proof. intros Hws. eapply Forall_impl; first exact Hws. apply word_rooted_not_heap_cap. Qed.

  Lemma word_rooted_int H z : word_rooted H (WInt z).
  Proof. by apply word_rooted_nonheap. Qed.

  Lemma word_rooted_cap_nonheap H t p g b e a :
    is_heap_address b = false → word_rooted H (WCap t p g b e a).
  Proof. intros Hb. apply word_rooted_nonheap. by rewrite /heap_cap_base /= Hb. Qed.

  Lemma word_rooted_cap_disjoint H t p g b e a :
    disjoint_from_heap b e → word_rooted H (WCap t p g b e a).
  Proof.
    intros Hbe b' _ Hb'. rewrite /heap_authority_base in Hb'.
    case_decide; last done.
    rewrite /heap_cap_base /= (disjoint_from_heap_not_in b e b Hbe) in Hb'; first done.
    apply withinBounds_true_iff. solve_addr.
  Qed.

  Lemma word_rooted_ints H (ws : list Word) :
    Forall is_z ws → Forall (word_rooted H) ws.
  Proof.
    intros Hws. eapply Forall_impl; first exact Hws.
    intros [] Hz; try done; apply word_rooted_int.
  Qed.

  (** An initial data word is an integer or a capability inside the data
      region, which is outside the heap. *)
  Lemma word_rooted_initial_data H (C : cmpt) w :
    is_initial_data_word C w → word_rooted H w.
  Proof.
    intros [Hz|Hin].
    - destruct w; try done; apply word_rooted_int.
    - intros b Ht Hb.
      destruct w as [z|[t p g b' e' a|t p g b' e' a]|t p g b' e' a|o sb];
        cbn in Hin; try done.
      destruct g; try done. destruct Hin as (_ & Hlo & Hhi).
      rewrite /heap_authority_base in Hb. case_decide as Hlt; last done.
      rewrite /heap_cap_base /= in Hb.
      destruct (is_heap_address b') eqn:Hheap; last done. exfalso.
      pose proof (cmpt_cgp_disjoint_from_heap C) as Hdisj.
      rewrite /disjoint_from_heap elem_of_disjoint in Hdisj.
      apply (Hdisj b'); apply elem_of_finz_seq_between;
        [solve_addr|by apply withinBounds_true_iff].
  Qed.

  Lemma word_rooted_instrs H (l : list instr) :
    Forall (word_rooted H) (encodeInstrsW l).
  Proof. apply Forall_fmap, Forall_true. intros i. apply word_rooted_int. Qed.

  Lemma word_rooted_code H (l : list (list instr)) :
    Forall (word_rooted H) (concat (encodeInstrsW <$> l)).
  Proof. apply Forall_concat, Forall_fmap, Forall_true. intros. apply word_rooted_instrs. Qed.

  Lemma mem_rooted_union H m1 m2 :
    mem_rooted H m1 → mem_rooted H m2 → mem_rooted H (m1 ∪ m2).
  Proof. intros H1 H2 a w [Ha|[_ Ha] ]%lookup_union_Some_raw; eauto. Qed.

  Lemma mem_rooted_mkregion H b e ws :
    Forall (word_rooted H) ws → mem_rooted H (mkregion b e ws).
  Proof.
    intros Hws a w Ha. apply elem_of_list_to_map_2, elem_of_zip_r in Ha.
    by eapply Forall_forall.
  Qed.

  Lemma mem_rooted_initial_heap H : mem_rooted H initial_heap_memory.
  Proof.
    intros a w Ha. rewrite /initial_heap_memory lookup_gset_to_gmap_Some in Ha.
    destruct Ha as [_ <-]. apply word_rooted_int.
  Qed.

  Lemma mem_rooted_initial_cmpt H (C : cmpt) :
    Forall (word_rooted H) (cmpt_imports C) →
    Forall (word_rooted H) (cmpt_code C) →
    Forall (word_rooted H) (cmpt_data C) →
    Forall (word_rooted H) (cmpt_static_sealed C) →
    Forall (word_rooted H) (cmpt_exp_tbl_entries C) →
    mem_rooted H (mk_initial_cmpt C).
  Proof.
    intros Himports Hcode Hdata Hstatic Hentries.
    rewrite /mk_initial_cmpt /cmpt_pcc_mregion /cmpt_cgp_mregion
      /cmpt_static_sealed_mregion /cmpt_exp_tbl_mregion.
    repeat apply mem_rooted_union; apply mem_rooted_mkregion; try done.
    - repeat constructor. apply word_rooted_cap_nonheap, cmpt_pcc_base_not_heap.
    - repeat constructor. apply word_rooted_cap_nonheap, cmpt_cgp_not_heap_range.
  Qed.

  Lemma mem_rooted_initial_switcher H (C : cmptSwitcher) :
    Forall (word_rooted H) (stack_content C) →
    mem_rooted H (mk_initial_switcher C).
  Proof.
    intros Hstack.
    pose proof (word_rooted_ints H _ (trusted_stack_content_ints C)) as Htrusted.
    rewrite /mk_initial_switcher /cmpt_switcher_code_mregion
      /cmpt_switcher_trusted_stack_mregion /cmpt_switcher_stack_mregion.
    repeat apply mem_rooted_union; apply mem_rooted_mkregion; try done.
    - repeat constructor. by apply word_rooted_nonheap.
    - rewrite /switcher_instrs. apply Forall_concat, Forall_fmap, Forall_true.
      intros l. apply word_rooted_instrs.
  Qed.

  Lemma mem_rooted_initial_assert H (C : cmptAssert) :
    is_heap_address (flag_assert C) = false →
    mem_rooted H (mk_initial_assert C).
  Proof.
    intros Hflag.
    rewrite /mk_initial_assert /cmpt_assert_code_mregion
      /cmpt_assert_cap_mregion /cmpt_assert_flag_mregion.
    repeat apply mem_rooted_union; apply mem_rooted_mkregion.
    - apply word_rooted_instrs.
    - repeat constructor. by apply word_rooted_cap_nonheap.
    - repeat constructor. apply word_rooted_int.
  Qed.

End CmptLayout.

(* Discharges [disjoint_from_mmio] for concrete address ranges. *)
(* The revoker address and the bounds are computed first, so that [cbn] never
   unfolds the machine-parameter instance. *)
Ltac solve_disjoint_from_mmio :=
  lazymatch goal with
  | |- disjoint_from_mmio ?b ?e =>
      let r := eval vm_compute in (revoker_addr : Addr) in
      let b' := eval vm_compute in b in
      let e' := eval vm_compute in e in
      change revoker_addr with r; change b with b'; change e with e';
      split;
      [ unfold disjoint_from_shadow, disjoint, set_disjoint_instance;
        intros x Hx Hx'; rewrite !elem_of_finz_seq_between in Hx, Hx';
        unfold finz.le_lt in Hx, Hx'; cbn in Hx, Hx'; lia
      | rewrite elem_of_finz_seq_between; unfold finz.le_lt; cbn; lia ]
  end.

(* Discharges [mem_avoids_mmio] for an initial memory built from the layout's
   regions. Matching is syntactic, so no region map is ever unfolded. *)
Ltac solve_mem_avoids_mmio_initial :=
  repeat lazymatch goal with
  | |- mem_avoids_mmio (_ ∪ _) => apply mem_avoids_mmio_union
  | |- mem_avoids_mmio initial_heap_memory => apply mem_avoids_mmio_initial_heap
  | |- mem_avoids_mmio (mk_initial_cmpt _) => apply mem_avoids_mmio_initial_cmpt
  | |- mem_avoids_mmio (mk_initial_switcher _) => apply mem_avoids_mmio_initial_switcher
  | |- mem_avoids_mmio (mk_initial_assert _) => apply mem_avoids_mmio_initial_assert
  end.
