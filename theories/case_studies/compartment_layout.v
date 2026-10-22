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
        cmpt_exp_tbl_handler : Word;
        cmpt_exp_tbl_handler_stackless : Word;
        cmpt_exp_tbl_entries : list Word;

        cmpt_import_size : (cmpt_b_pcc + length cmpt_imports)%a = Some cmpt_a_code;
        cmpt_code_size : (cmpt_a_code + length cmpt_code)%a = Some cmpt_e_pcc;
        cmpt_data_size : (cmpt_b_cgp + length cmpt_data)%a = Some cmpt_e_cgp;
        cmpt_static_sealed_size : (cmpt_b_static_sealed + length cmpt_static_sealed)%a = Some cmpt_e_static_sealed;
        cmpt_exp_tbl_pcc_size :
          (cmpt_exp_tbl_pcc + ExportTable_offset_cgp)%a = Some cmpt_exp_tbl_cgp;
        (* The header: the PCC, the CGP and the offsets of the error handlers *)
        cmpt_exp_tbl_header_size :
          (cmpt_exp_tbl_pcc + ExportTable_offset_entries)%a = Some cmpt_exp_tbl_entries_start;
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
        not_heap_range cmpt_b_static_sealed cmpt_e_static_sealed;
        (* The PCC is executable: its closed bounds avoid the heap. *)
        cmpt_pcc_end_not_heap : is_heap_address cmpt_e_pcc = false
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

  #[global] Instance Cmpt_Disjoint : Disjoint cmpt := disjoint_cmpt.

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
      mkregion (cmpt_exp_tbl_cgp C) (cmpt_exp_tbl_entries_start C)
        [cgp_word; cmpt_exp_tbl_handler C; cmpt_exp_tbl_handler_stackless C] ∪
      mkregion (cmpt_exp_tbl_entries_start C) (cmpt_exp_tbl_entries_end C) (cmpt_exp_tbl_entries C)
  .

  Definition mk_initial_cmpt (C : cmpt) : gmap Addr Word :=
    cmpt_pcc_mregion C ∪
    cmpt_cgp_mregion C ∪
    cmpt_static_sealed_mregion C ∪
    cmpt_exp_tbl_mregion C.

  (** A word of an initial trusted stack: it has no authority over the heap
      and is not executable. *)
  Definition trusted_stack_word (w : Word) : Prop :=
    heap_authority_base w = None ∧ executable_word w = false.

  Lemma trusted_stack_word_int z : trusted_stack_word (WInt z).
  Proof. by split. Qed.

  (** The initial contents of a trusted stack with room for the entry frame
      and [n] frames: a zeroed register save area, [frameoffset] pointing
      after the entry frame, a zeroed [threadID], the entry frame, and
      zeroed frames. The entry frame holds the stack pointer [w_csp] of the
      thread, the export table [w_export_table] of the compartment it starts
      in, and no error handler invocation. *)
  Definition initial_trusted_stack_content (w_csp w_export_table : Word) (n : nat) : list Word :=
    replicate (Z.to_nat TSTACK_REGFRAME_SZ) (WInt 0) ++
    [WInt (tstack_frameoffset 0); WInt 0] ++
    [w_csp; w_export_table; WInt 0] ++
    replicate (Z.to_nat (TrustedStackFrame_size * Z.of_nat n)) (WInt 0).

  Lemma initial_trusted_stack_content_words (w_csp w_export_table : Word) (n : nat) :
    trusted_stack_word w_csp →
    trusted_stack_word w_export_table →
    Forall trusted_stack_word (initial_trusted_stack_content w_csp w_export_table n).
  Proof.
    intros Hcsp Hexport_table. rewrite /initial_trusted_stack_content.
    pose proof (trusted_stack_word_int 0) as Hzero.
    repeat apply Forall_app_2; try by apply Forall_replicate.
    - by apply Forall_cons_2; [apply trusted_stack_word_int | apply Forall_singleton].
    - by apply Forall_cons_2; [| apply Forall_cons_2; [| apply Forall_singleton] ].
  Qed.

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

        (* [frameoffset] points after the entry frame of the thread. *)
        trusted_stack_content_frameoffset :
        trusted_stack_content !! Z.to_nat TrustedStack_offset_frameoffset
        = Some (WInt (tstack_frameoffset 0));
        (* The trusted stack holds its header, the entry frame and a whole
           number of frames. *)
        trusted_stack_frames_fit :
        ∃ n : nat,
          (b_trusted_stack + tstack_frame_offset (S n))%a = Some e_trusted_stack;
        (* The entry frame holds a capability to the export table of the
           compartment the thread starts in, and no error handler
           invocation. *)
        trusted_stack_content_export_table :
        ∃ (b_tbl : Addr) (w : Word),
          trusted_stack_content
            !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_calleeExportTable)
          = Some w ∧
          exp_tbl_cap b_tbl w;
        trusted_stack_content_error_count :
          trusted_stack_content
            !! Z.to_nat (tstack_frame_offset 0 + TrustedStackFrame_offset_errorHandlerCount)
          = Some (WInt 0);
        (* The trusted stack has no authority over the heap and no
           executable word. *)
        trusted_stack_content_words :
        Forall trusted_stack_word trusted_stack_content;

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
        (* The switcher's sentries are executable: their closed bounds avoid
           the heap. *)
        switcher_end_not_heap : is_heap_address e_switcher = false;
        (* The register save area of the trusted stack is not in the heap. *)
        trusted_stack_not_heap :
        not_heap_range b_trusted_stack (b_trusted_stack ^+ TSTACK_REGFRAME_SZ)%a;
      }.

  Definition trusted_stack_disjoint_from_shadow (C : cmptSwitcher) :
    disjoint_from_shadow (b_trusted_stack C) (e_trusted_stack C) :=
    disjoint_from_mmio_shadow _ _ (trusted_stack_disjoint_from_mmio C).

  Definition switcher_base_not_heap (C : cmptSwitcher) :
    is_heap_address (b_switcher C) = false :=
    proj1 (switcher_not_heap_range C).
  Definition switcher_disjoint_from_heap (C : cmptSwitcher) :
    disjoint_from_heap (b_switcher C) (e_switcher C) :=
    proj2 (switcher_not_heap_range C).


  #[global] Instance cmptSwitcher_switcherLayout (switcher_cmpt : cmptSwitcher) : switcherLayout.
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

  (** The PCC of a compartment disjoint from the switcher, with code, does
      not have the base of the switcher's PCC. *)
  Lemma switcher_cmpt_disjoint_pcc_b (C : cmpt) (Cswitcher : cmptSwitcher) :
    switcher_cmpt_disjoint C Cswitcher →
    (cmpt_b_pcc C < cmpt_e_pcc C)%a →
    cmpt_b_pcc C ≠ b_switcher Cswitcher.
  Proof.
    intros Hdisj Hpcc Heq.
    pose proof (switcher_size Cswitcher) as Hsize.
    pose proof (switcher_call_entry_point Cswitcher) as Hcall.
    assert (cmpt_b_pcc C ∈ cmpt_switcher_code_region Cswitcher) as Hin_sw.
    { rewrite /cmpt_switcher_code_region elem_of_finz_seq_between Heq. solve_addr. }
    assert (cmpt_b_pcc C ∈ cmpt_pcc_region C) as Hin_C.
    { rewrite /cmpt_pcc_region elem_of_finz_seq_between. solve_addr. }
    rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_region in Hdisj.
    set_solver.
  Qed.

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
        disjoint_from_mmio flag_assert (flag_assert ^+ 1)%a;
        (* The assert sentry is executable: its closed bounds avoid the heap. *)
        assert_end_not_heap : is_heap_address e_assert = false
      }.

  #[global] Instance cmptAssert_assertLayout (assert_cmpt : cmptAssert) : assertLayout.
  Proof.
    refine (@mkAssertLayout
              (b_assert assert_cmpt)
              (e_assert assert_cmpt)
              (flag_assert assert_cmpt)
           ).
  Defined.

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
    pose proof (cmpt_exp_tbl_header_size B_cmpt).
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
      [WCap true RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt);
       cmpt_exp_tbl_handler B_cmpt; cmpt_exp_tbl_handler_stackless B_cmpt]
      ##ₘ mkregion (cmpt_exp_tbl_entries_start B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt) (cmpt_exp_tbl_entries B_cmpt).
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_exp_tbl_pcc_size B_cmpt).
    pose proof (cmpt_exp_tbl_header_size B_cmpt).
    pose proof (cmpt_exp_tbl_entries_size B_cmpt).
    rewrite dom_union_L.
    repeat rewrite dom_mkregion_eq; try (cbn; solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite elem_of_union !elem_of_list_to_set !elem_of_finz_seq_between in Ha.
    rewrite !elem_of_list_to_set !elem_of_finz_seq_between in Ha'.
    solve_addr.
  Qed.

  Lemma cmpt_exp_tbl_pcc_cgp_disjoint (B_cmpt : cmpt) :
    mkregion (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_cgp B_cmpt)
      [WCap true RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)]
      ##ₘ mkregion (cmpt_exp_tbl_cgp B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt)
      [WCap true RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt);
       cmpt_exp_tbl_handler B_cmpt; cmpt_exp_tbl_handler_stackless B_cmpt].
  Proof.
    apply map_disjoint_dom_2.
    pose proof (cmpt_exp_tbl_pcc_size B_cmpt).
    pose proof (cmpt_exp_tbl_header_size B_cmpt).
    repeat rewrite dom_mkregion_eq; try (cbn; solve_addr).
    apply elem_of_disjoint.
    intros a Ha Ha'.
    rewrite !elem_of_list_to_set !elem_of_finz_seq_between in Ha Ha'.
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

  Lemma word_rooted_trusted_stack_word H w : trusted_stack_word w → word_rooted H w.
  Proof. intros [Hw _] b _ Hb. congruence. Qed.

  Lemma word_rooted_ints H (ws : list Word) :
    Forall is_z ws → Forall (word_rooted H) ws.
  Proof.
    intros Hws. eapply Forall_impl; first exact Hws.
    intros [] Hz; try done; apply word_rooted_int.
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

  (** ** Executable words of the initial memory

      Every tagged executable word of an initial memory has closed bounds
      that avoid the heap ([gi_mem_exec] of [cerise_ghost_init]). *)
  Definition word_exec_ok (w : Word) : Prop := lword_exec (lword_of_word w).

  Definition mem_exec_ok (m : Mem) : Prop :=
    ∀ a w, m !! a = Some w → word_exec_ok w.

  Lemma word_exec_ok_not_executable w : executable_word w = false → word_exec_ok w.
  Proof. intros Hx. by apply (lword_exec_not_executable (lword_of_word w)). Qed.

  Lemma word_exec_ok_int z : word_exec_ok (WInt z).
  Proof. by apply word_exec_ok_not_executable. Qed.

  Lemma word_exec_ok_trusted_stack_word w : trusted_stack_word w → word_exec_ok w.
  Proof. intros [_ Hw]. by apply word_exec_ok_not_executable. Qed.

  Lemma word_exec_ok_ints (ws : list Word) :
    Forall is_z ws → Forall word_exec_ok ws.
  Proof.
    intros Hws. eapply Forall_impl; first exact Hws.
    intros [] Hz; try done; apply word_exec_ok_int.
  Qed.

  (** A word whose closed bounds avoid the heap. *)
  Lemma word_exec_ok_closed w b e :
    memory_cap_bounds w = Some (b, e) →
    not_heap_range b e →
    is_heap_address e = false →
    word_exec_ok w.
  Proof.
    intros Hbe [Hb Hdisj] He _ _. split; first done.
    intros b' e' Hbe'. cbn in Hbe'. rewrite Hbe in Hbe'. simplify_eq.
    split; first done.
    intros y [Hy1 Hy2]. destruct (decide (y = e')) as [->|Hne]; first done.
    apply (disjoint_from_heap_not_in b' e'); first done.
    apply withinBounds_true_iff. solve_addr.
  Qed.

  Lemma word_exec_ok_instrs (l : list instr) :
    Forall word_exec_ok (encodeInstrsW l).
  Proof. apply Forall_fmap, Forall_true. intros i. apply word_exec_ok_int. Qed.

  Lemma mem_exec_ok_union m1 m2 :
    mem_exec_ok m1 → mem_exec_ok m2 → mem_exec_ok (m1 ∪ m2).
  Proof. intros H1 H2 a w [Ha|[_ Ha] ]%lookup_union_Some_raw; eauto. Qed.

  Lemma mem_exec_ok_mkregion b e ws :
    Forall word_exec_ok ws → mem_exec_ok (mkregion b e ws).
  Proof.
    intros Hws a w Ha. apply elem_of_list_to_map_2, elem_of_zip_r in Ha.
    by eapply Forall_forall.
  Qed.

  Lemma mem_exec_ok_initial_heap : mem_exec_ok initial_heap_memory.
  Proof.
    intros a w Ha. rewrite /initial_heap_memory lookup_gset_to_gmap_Some in Ha.
    destruct Ha as [_ <-]. apply word_exec_ok_int.
  Qed.

End CmptLayout.
