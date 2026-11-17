From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy_obligations firmware_obligations
  firmware_thread_obligations tsy_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import tsy_flag tsy_spec_states tsy_spec_run1 tsy_spec_run2.
From griotte Require Import assert_spec.
From griotte Require Import world_interp_allocation.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.

Section tsy_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {B Sched : CmptName}.
  Context `{MP : MachineParameters}.

  (** The threads of the compartments: the context-switch thread in the
      scheduler's [Sched], the user thread 0 in [B], exclusively. The user
      thread 1 runs only the trusted [K]: it is in no logical compartment. *)
  Definition tsy_cthreads : CmptThreads := {|
    cmpt_threads := λ X,
      if decide (X = Sched) then {[CtxSwitch]} else {[UserThread 0]};
    cmpt_shared := λ _, false;
    cmpt_threads_sep := ltac:(intros X t; cbv beta; repeat case_decide; set_solver) |}.

  (** The thread 1 starts at the export [run2] of [K]. *)
  Lemma tsy_entry_pc_1 img σ :
    firmware_ok tsy_firmware img σ →
    let m := cmpt_of img "K" in
    fw_entry_pc tsy_firmware img 1 =
      Cap RX Global (image.cmpt_b_pcc m) (image.cmpt_e_pcc m)
        (image.cmpt_a_code m ^+ tsy_label_offset ".Lsync_run2")%a.
  Proof.
    intros Hok m.
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as HK_l.
    cbn [fc_name] in HK_l.
    (* The imports end at the start of the code, which holds 35 words *)
    pose proof (icl_import_size _ HK_l) as Himp.
    pose proof (icl_code_size _ HK_l) as Hcode.
    pose proof (cmpt_ok_imports _ _ _ (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl)) as Himports.
    cbn [fc_name] in Himports.
    rewrite Himports length_fmap in Himp. cbn [fc_imports length] in Himp.
    clear Himports.
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_K.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts tsy_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb]
      in Hok_K.
    destruct Hok_K as (_ & _ & K_code & _).
    rewrite K_code in Hcode.
    assert (length tsy_K_code = 35) as Hlen by reflexivity.
    assert (tsy_label_offset ".Lsync_run2" = 16%Z) as -> by reflexivity.
    rewrite Hlen in Hcode.
    (* The entry of [run2] is at the offset 19 of the PCC *)
    rewrite /fw_entry_pc. change (fw_entry_offset tsy_firmware 1) with 19.
    change (fw_entry_cmpt tsy_firmware img 1) with m.
    assert (∃ tb, fc_body (fw_entry_fc tsy_firmware 1) = TrustedBody tb) as [tb ->]
      by (eexists; reflexivity).
    rewrite addr_off_eq. subst m. f_equal.
    assert (image.cmpt_b_pcc (cmpt_of img "K") ^+ 19%nat =
              image.cmpt_a_code (cmpt_of img "K") ^+ 16)%a as -> by solve_addr.
    reflexivity.
  Qed.

  (** The obligations of the trusted code of the thread-synchronisation
      firmware: the thread 0 runs safely from the export [run1] of [K], the
      untrusted compartment ["B"] being owned by the logical compartment
      [B], which only it runs; the thread 1 runs safely from the export
      [run2] of [K]; the world of [B] passes from the thread 0 to the
      thread 1 through the invariant of the global [flag] of [K]; the
      scheduler runs in [Sched]. *)
  Lemma tsy_fw_obligations :
    B ≠ Sched →
    fw_obligations Σ tsy_firmware.
  Proof.
    intros HBS.
    exists tsy_cthreads, Sched.
    split; first by (cbn; rewrite decide_True; [set_solver | done]).
    split; first reflexivity.
    set (cthreads := tsy_cthreads).
    assert (@cmpt_threads _ cthreads B = {[UserThread 0]}) as HB_threads.
    { rewrite /cthreads /tsy_cthreads /=. by rewrite decide_False. }
    assert (UserThread 0 ∈ @cmpt_threads _ cthreads B) as Hin_B.
    { rewrite HB_threads. set_solver. }
    assert (@cmpt_threads _ cthreads B ⊆ {[UserThread 0]}) as Hpin_B.
    { by rewrite HB_threads. }
    assert (@cmpt_shared _ cthreads B = false) as HB_excl by reflexivity.
    assert (fw_threads tsy_firmware = [fw_thread_of tsy_firmware 0; fw_thread_of tsy_firmware 1])
      as Hthreads by reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_K.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts tsy_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb]
      in Hok_K.
    destruct Hok_K as (K_imports & _ & K_code & K_data & _).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as HK_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as HB_l.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (fw_cmpts_disjoint_at _ _ _ 0 1 _ _ HK_l HB_l Hok ltac:(done) eq_refl eq_refl)
      as HKB.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 0 _ HK_l eq_refl) as Hsw_K.
    cbn [fc_name] in HK_l, HB_l, HKB, Hsw_K.
    set (K_cmpt := layout_cmpt_of (cmpt_of img "K") HK_l) in *.
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l) in *.
    set (swc := fw_switcher_cmpt _ _ _ Hok) in *.
    set (swl := fw_switcher_layout img) in *.
    set (asl := fw_assert_layout img).

    (* 2 - The export entry of B, imported by K *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry tsy_B_entry_f)).
    assert (cmpt_export_sb (cmpt_of img "B") tsy_B_entry_f = B_f) as HsbB.
    { by rewrite /cmpt_export_sb /B_f /=. }
    assert (image.cmpt_imports (cmpt_of img "K") = @tsy_K_imports swl asl B_f)
      as K_imports'.
    { rewrite K_imports /tsy_K_imports. done. }

    (* 3 - The outer update: the memory of K, its data split between [b]
       and [flag], and the invariant of [flag] *)
    iIntros "Hshared". iNamed "Hshared". iClear "Hswitcher_tstacks".
    iEval (rewrite Hthreads big_sepL_cons big_sepL_singleton) in "Hswitcher_static".
    iDestruct "Hswitcher_static" as "[#Hswitcher_static #Hstatic1]".
    iEval (cbv [tsy_firmware fw_cmpts]; rewrite !big_sepL_cons big_sepL_nil;
           cbv [fw_cmpt_res_user fc_body]) in "Hcmpts".
    iDestruct "Hcmpts" as "((HK & _ & _) & (HB & _ & #HB_pers) & _)".
    iMod (fw_cmpt_mem_persist with "HK") as "(#HK_imports & #HK_code & HK_data)";
      first exact HK_l.
    rewrite K_imports' K_code K_data.
    cbn [fc_name].
    fw_fold_cmpt K_cmpt.
    pose proof (main_spec_size_obligations _ _ _ _ K_imports' K_code K_data)
      as (HK_bounds & HK_data_size & HK_imports_size).
    (* [b] and [flag] are neither MMIO nor heap addresses *)
    assert (is_mmio_address (cmpt_b_cgp K_cmpt) = false) as HK_cgp_mmio.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio K_cmpt).
      apply withinBounds_true_iff.
      pose proof HK_data_size as Hsize.
      rewrite /tsy_K_data /= in Hsize. split; solve_addr. }
    assert (is_mmio_address (cmpt_b_cgp K_cmpt ^+ 1) = false) as HK_flag_mmio.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio K_cmpt).
      apply withinBounds_true_iff.
      pose proof HK_data_size as Hsize.
      rewrite /tsy_K_data /= in Hsize. split; solve_addr. }
    assert (is_heap_address (cmpt_b_cgp K_cmpt ^+ 1) = false) as HK_flag_heap.
    { eapply disjoint_from_heap_not_in;
        first exact (cmpt_cgp_disjoint_from_heap K_cmpt).
      apply withinBounds_true_iff.
      pose proof HK_data_size as Hsize.
      rewrite /tsy_K_data /= in Hsize. split; solve_addr. }
    iEval (cbn [fmap list_fmap tsy_K_data]) in "HK_data".
    iRegionSplit "HK_data" as "[Hb Hflag]".
    iMod (tsy_flag_alloc ⊤ B (cmpt_b_cgp K_cmpt ^+ 1) (cmpt_b_cgp K_cmpt) with "Hflag")
      as (γ) "[#Hflag_inv Htok]".
    iModIntro.
    rewrite Hthreads big_sepL_cons big_sepL_singleton.
    iSplitR "Hstatic1 Hassert Htok".
    2: {
      (* The thread 1, at [K.run2]: the code of K, the assert library and the
         invariant of [flag], moved to the thread 1 *)
      iIntros "Hthread _". iNamed "Hthread".
      iEval (rewrite (tsy_entry_pc_1 img σ Hok)) in "HPC".
      iEval (rewrite fw_thread_cra_eq) in "Hcra".
      iEval (rewrite /fw_entry_cgp; cbv zeta) in "Hcgp".
      iEval (rewrite (assert_static_thread_indep (UserThread 0) (UserThread 1))) in "Hassert".
      iEval (rewrite (codefrag_pers_thread_indep (UserThread 0) (UserThread 1))) in "HK_code".
      change (fw_entry_cmpt tsy_firmware img 1) with (cmpt_of img "K") in *.
      fw_fold_cmpt K_cmpt.
      change (fw_entry_posture tsy_firmware img 1) with InterruptEnabled.
      (* The thread 1 uses neither its stack, its high-water-mark resources nor its
         local maps *)
      iClear "Hstack Hhwm Hlocals".
      iModIntro.
      iApply (tsy_run2_spec (th := UserThread 1) (swlayout := swl) (assertlayout := asl) (B := B)
                (cmpt_b_pcc K_cmpt) (cmpt_e_pcc K_cmpt) (cmpt_a_code K_cmpt)
                (cmpt_b_cgp K_cmpt) (cmpt_e_cgp K_cmpt)
                fw_cleared_regs (fw_thread_csp img 1) B_f
                (entry_cstack (fw_entry_frame tsy_firmware img 1)) γ
                ltac:(done)
                (cmpt_pcc_disjoint_from_shadow K_cmpt)
                (cmpt_pcc_base_not_heap K_cmpt)
                HK_cgp_mmio (cmpt_cgp_base_not_heap K_cmpt)
                HK_flag_mmio HK_flag_heap
                fw_cleared_regs_dom HK_bounds HK_data_size HK_imports_size
                eq_refl
               with "[$Hassert $Hswitcher $Hstatic1 $Hna $HPC $Hcgp $Hcsp $Hcra $Hregs
                      $HK_imports $HK_code $Hcstk $Hflag_inv $Htok $HMIE $Hheld]").
    }
    (* The thread 0, at [K.run1]: cmdc's first call, B pinned to it *)
    iClear "Hstatic1".
    iIntros "Hthread _". iNamed "Hthread".
    iEval (rewrite (fw_entry_pc_code tsy_firmware img σ ltac:(reflexivity) Hok)) in "HPC".
    iEval (rewrite fw_thread_cra_eq) in "Hcra".
    iEval (rewrite /fw_thread_csp; cbv zeta) in "Hcsp".
    iEval (rewrite /fw_entry_cgp; cbv zeta) in "Hcgp".
    iEval (rewrite /fw_entry_frame /fw_thread_csp /fw_entry_tbl; cbv zeta) in "Hcstk Hhwm".
    change (fw_entry_posture tsy_firmware img 0) with InterruptEnabled.
    (* The world of B at the thread 0: its map of Permanent regions and the
       thread's local map *)
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hperm_B _]".
    { apply elem_of_difference. split; last set_solver+HBS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ B with "Hlocals") as "[Hlocal_B _]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iAssert (world_interp (th := UserThread 0) fw_world0 B)
      with "[Hperm_B Hlocal_B]" as "Hworld_B".
    { rewrite world_interp_eq. iFrame. }
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) B Hin_B) as "#Hthread_B".
    iDestruct (switcher_threads_pinned (UserThread 0) B Hpin_B with "Hswitcher Hswitcher_static")
      as "#Hswitcher_threads_B".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack tsy_firmware 0) with 4 in Hentry_min_stack.
    change (fw_entry_cmpt tsy_firmware img 0) with (cmpt_of img "K") in *.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ tsy_B_entry_f 1
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|cbv; lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".

    (* 4 - Close the world of B: its compartment becomes Permanent regions,
       and the stack is revoked, because K keeps it; its export is safe to
       share. *)
    iMod (fw_close_adv_world_revoked (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts tsy_firmware) default_fw_cmpt)
            _ HB_l fw_world0 B Hok eq_refl eq_refl
            ltac:(apply Forall_singleton; cbn; lia) ltac:(done)
           with "Hswitcher_threads_B Hswitcher_static HB HB_pers [] Hthread_B Hworld_B")
      as "(Hworld_B & Hrevoked_stack_B & [#Hinterp_B _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher_threads_B"). }
    cbn [fc_name fw_nth fw_cmpts tsy_firmware]. rewrite HsbB.
    fw_fold_cmpt K_cmpt. fw_fold_cmpt B_cmpt.
    set (Wk := std_update_multiple fw_world0
                 (finz.seq_between (image.b_stack (thread_of img 0))
                    (image.e_stack (thread_of img 0)))
                 Revoked).

    (* 5 - We can apply the specification! *)
    iModIntro.
    iApply (tsy_run1_spec (th := UserThread 0) (swlayout := swl) (assertlayout := asl) (B := B)
              _ _ _ _ _ _ _ _ _ Wk [] [] _ _ γ
              ltac:(done)
              (cmpt_pcc_disjoint_from_shadow K_cmpt)
              (cmpt_pcc_base_not_heap K_cmpt)
              HK_cgp_mmio (cmpt_cgp_base_not_heap K_cmpt)
              HK_flag_mmio HK_flag_heap
              (stack_disjoint_from_mmio swc)
              (stack_disjoint_from_heap swc)
             with "[ $Hthread_B $Hswitcher $Hswitcher_static $Hna
                    $HPC $Hcgp $Hcsp $Hcra $Hregs
                    $HK_imports $HK_code $Hb $Hstack
                    $Hworld_B $Hcstk $Hhwm $Hinterp_B $Hentry_Bf $Hrevoked_stack_B
                    $Hflag_inv $HMIE $Hheld ]").
    - exact fw_cleared_regs_dom.
    - intros r Hr. by rewrite fw_cleared_regs_lookup.
    - exact HK_bounds.
    - exact HK_data_size.
    - exact HK_imports_size.
    - exact Hentry_min_stack.
    - apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
    - rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    - exact HB_excl.
  Qed.
End tsy_obligations.
