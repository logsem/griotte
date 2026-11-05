From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy_obligations firmware_obligations
  firmware_thread_obligations cmdc_isolated_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import cmdc cmdc_spec.
From griotte Require Import assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.
From griotte Require Import allocator_resources heap_region.

Section cmdc_isolated_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {B C D Sched : CmptName}.
  Context `{MP : MachineParameters}.

  (** The threads of the compartments: the context-switch thread in the
      scheduler's [Sched], the user thread 1 in [D], the user thread 0 in
      the others; every compartment in exclusive mode. *)
  Definition cmdc_isolated_cthreads : CmptThreads := {|
    cmpt_threads := λ X,
      if decide (X = Sched) then {[CtxSwitch]}
      else if decide (X = D) then {[UserThread 1]}
      else {[UserThread 0]};
    cmpt_shared := λ _, false;
    cmpt_threads_sep := ltac:(intros X t; cbv beta; repeat case_decide; set_solver) |}.

  (** The obligations of the trusted code of the CMDC firmware with an
      isolated thread: the thread 0 runs safely from the export of [main],
      the untrusted compartments ["B"] and ["C"] being owned by the logical
      compartments [B] and [C]; the thread 1 runs safely from the export
      [adv] of the untrusted compartment ["D"], owned by the logical
      compartment [D], which only it runs; the scheduler runs in [Sched]. *)
  Lemma cmdc_isolated_fw_obligations :
    B ≠ C →
    B ≠ D →
    C ≠ D →
    B ≠ Sched →
    C ≠ Sched →
    D ≠ Sched →
    fw_obligations Σ cmdc_isolated_firmware.
  Proof.
    intros HBC HBD HCD HBS HCS HDS.
    exists cmdc_isolated_cthreads, Sched.
    split; first by (cbn; rewrite decide_True; [set_solver | done]).
    split; first reflexivity.
    set (cthreads := cmdc_isolated_cthreads).
    assert (@cmpt_threads _ cthreads B = {[UserThread 0]}) as HB_threads.
    { rewrite /cthreads /cmdc_isolated_cthreads /=. by rewrite decide_False // decide_False. }
    assert (@cmpt_threads _ cthreads C = {[UserThread 0]}) as HC_threads.
    { rewrite /cthreads /cmdc_isolated_cthreads /=. by rewrite decide_False // decide_False. }
    assert (@cmpt_threads _ cthreads D = {[UserThread 1]}) as HD_threads.
    { rewrite /cthreads /cmdc_isolated_cthreads /=. by rewrite decide_False // decide_True. }
    assert (UserThread 0 ∈ @cmpt_threads _ cthreads B) as Hin_B.
    { rewrite HB_threads. set_solver. }
    assert (@cmpt_threads _ cthreads B ⊆ {[UserThread 0]}) as Hpin_B.
    { by rewrite HB_threads. }
    assert (UserThread 0 ∈ @cmpt_threads _ cthreads C) as Hin_C.
    { rewrite HC_threads. set_solver. }
    assert (@cmpt_threads _ cthreads C ⊆ {[UserThread 0]}) as Hpin_C.
    { by rewrite HC_threads. }
    assert (∀ X, cmpt_shared X = false) as Hexcl by done.
    assert (fw_threads cmdc_isolated_firmware =
              [fw_thread_of cmdc_isolated_firmware 0; fw_thread_of cmdc_isolated_firmware 1])
      as Hthreads by reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts cmdc_isolated_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb] in Hok_main.
    destruct Hok_main as (main_imports & _ & main_code & main_data & _).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as Hmain_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as HB_l.
    pose proof (fw_cmpt_layout_at _ _ _ 2 _ Hok eq_refl) as HC_l.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (fw_cmpts_disjoint_at _ _ _ 0 1 _ _ Hmain_l HB_l Hok ltac:(done) eq_refl eq_refl)
      as HmainB.
    pose proof (fw_cmpts_disjoint_at _ _ _ 0 2 _ _ Hmain_l HC_l Hok ltac:(done) eq_refl eq_refl)
      as HmainC.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 0 _ Hmain_l eq_refl) as Hsw_main.
    cbn [fc_name] in Hmain_l, HB_l, HC_l, HmainB, HmainC, Hsw_main.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l) in *.
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l) in *.
    set (C_cmpt := layout_cmpt_of (cmpt_of img "C") HC_l) in *.
    set (swc := fw_switcher_cmpt _ _ _ Hok) in *.
    set (swl := fw_switcher_layout img) in *.
    set (asl := fw_assert_layout img).

    (* 2 - The export entries of B and C, imported by main *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry cmdc_B_entry_f)).
    set (C_g := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry cmdc_C_entry_g)).
    assert (cmpt_export_sb (cmpt_of img "B") cmdc_B_entry_f = B_f ∧
            cmpt_export_sb (cmpt_of img "C") cmdc_C_entry_g = C_g) as (HsbB & HsbC).
    { by rewrite /cmpt_export_sb /B_f /C_g /=. }
    assert (image.cmpt_imports (cmpt_of img "main") = @cmdc_main_imports swl asl B_f C_g)
      as main_imports'.
    { rewrite main_imports /cmdc_main_imports. done. }

    (* 3 - The resources of the image: the thread 1 takes the resources of
       D, the thread 0 the others *)
    iIntros "Hshared". iNamed "Hshared".
    iEval (rewrite Hthreads big_sepL_cons big_sepL_singleton) in "Hswitcher_static".
    iDestruct "Hswitcher_static" as "[#Hswitcher_static #Hstatic1]".
    iEval (cbv [cmdc_isolated_firmware fw_cmpts]; rewrite !big_sepL_cons big_sepL_nil;
           cbv [fw_cmpt_res_user fc_body]) in "Hcmpts".
    iDestruct "Hcmpts" as "((Hmain & _ & _) & (HB & _ & #HB_pers) & (HC & _ & #HC_pers) & HD & _)".
    iDestruct (big_sepS_delete _ _ D with "Hworlds") as "[Hperm_D Hworlds]".
    { apply elem_of_difference. split; last set_solver+HDS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iModIntro.
    rewrite Hthreads big_sepL_cons big_sepL_singleton.
    iSplitR "Hstatic1 HD Hperm_D".
    2: {
      (* The thread 1, alone in D, by the FTLR *)
      iApply (fw_isolated_thread_obligation (cthreads := cthreads)
                cmdc_isolated_firmware img σ 1 (fw_thread_of cmdc_isolated_firmware 1) _ D
                Hok with "Hstatic1 HD Hperm_D").
      - reflexivity.
      - reflexivity.
      - cbn. apply Forall_singleton. lia.
      - cbn. by apply Forall_singleton.
      - exact HD_threads.
      - reflexivity.
    }
    (* The thread 0, as in the CMDC case study *)
    iClear "Hstatic1".
    iIntros "Hthread _". iNamed "Hthread".
    iEval (rewrite (fw_entry_pc_code cmdc_isolated_firmware img σ ltac:(reflexivity) Hok)) in "HPC".
    iEval (rewrite fw_thread_cra_eq) in "Hcra".
    iEval (rewrite fw_thread_of_0) in "Hstack".
    iEval (rewrite /fw_thread_csp; cbv zeta) in "Hcsp".
    iEval (rewrite /fw_entry_cgp; cbv zeta) in "Hcgp".
    iEval (rewrite /fw_entry_frame /fw_thread_csp /fw_entry_tbl; cbv zeta) in "Hcstk".
    (* The worlds of B and C at the thread 0: their maps of Permanent regions
       and the thread's local maps *)
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hperm_B Hworlds]".
    { apply elem_of_difference. split; last set_solver+HBD.
      apply elem_of_difference. split; last set_solver+HBS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ C with "Hworlds") as "[Hperm_C _]".
    { apply elem_of_difference. split; last set_solver+HBC.
      apply elem_of_difference. split; last set_solver+HCD.
      apply elem_of_difference. split; last set_solver+HCS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ B with "Hlocals") as "[Hlocal_B Hlocals]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ C with "Hlocals") as "[Hlocal_C _]".
    { apply elem_of_difference. split; last set_solver+HBC.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iAssert (world_interp (ceriseg := ceriseG_of (UserThread 0)) (th := UserThread 0) fw_world0 B)
      with "[Hperm_B Hlocal_B]" as "Hworld_B".
    { rewrite world_interp_eq. iFrame. }
    iAssert (world_interp (ceriseg := ceriseG_of (UserThread 0)) (th := UserThread 0) fw_world0 C)
      with "[Hperm_C Hlocal_C]" as "Hworld_C".
    { rewrite world_interp_eq. iFrame. }
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) B Hin_B) as "#Hthread_B".
    iDestruct (switcher_threads_pinned (UserThread 0) B Hpin_B with "Hswitcher Hswitcher_static")
      as "#Hswitcher_threads_B".
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) C Hin_C) as "#Hthread_C".
    iDestruct (switcher_threads_pinned (UserThread 0) C Hpin_C with "Hswitcher Hswitcher_static")
      as "#Hswitcher_threads_C".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack cmdc_isolated_firmware 0) with 4 in Hentry_min_stack.
    cbn [fc_name].
    change (fw_entry_cmpt cmdc_isolated_firmware img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    rewrite main_imports' main_code main_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ cmdc_B_entry_f cmdc_B_f_args
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|cbv; lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ cmdc_C_entry_g cmdc_C_g_args
                 (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) with "HC_pers")
      as "#Hentry_Cg"; [done|cbv; lia|].
    iEval (rewrite HsbC) in "Hentry_Cg".

    (* 4 - Close the worlds of B and C: their compartments become Permanent regions,
       and the stack is revoked, because main keeps it; their exports are
       safe to share. *)
    iMod (fw_close_adv_world_revoked (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts cmdc_isolated_firmware) default_fw_cmpt)
            _ HB_l fw_world0 B Hok eq_refl eq_refl
            ltac:(apply Forall_singleton; cbn; rewrite /cmdc_B_f_args; lia) ltac:(done)
           with "Hswitcher_threads_B Hswitcher_static HB HB_pers [] Hthread_B Hworld_B")
      as "(Hworld_B & Hrevoked_stack_B & [#Hinterp_B _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher_threads_B"). }
    iMod (fw_close_adv_world_revoked (th := UserThread 0)
            _ _ _ 2 (fw_nth 2 (fw_cmpts cmdc_isolated_firmware) default_fw_cmpt)
            _ HC_l fw_world0 C Hok eq_refl eq_refl
            ltac:(apply Forall_singleton; cbn; rewrite /cmdc_C_g_args; lia) ltac:(done)
           with "Hswitcher_threads_C Hswitcher_static HC HC_pers [] Hthread_C Hworld_C")
      as "(Hworld_C & Hrevoked_stack_C & [#Hinterp_C _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher_threads_C"). }
    cbn [fc_name fw_nth fw_cmpts cmdc_isolated_firmware]. rewrite HsbB HsbC.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt B_cmpt. fw_fold_cmpt C_cmpt.

    (* 5 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    assert (is_mmio_address (cmpt_b_cgp main_cmpt) = false) as Hmain_shadow.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio main_cmpt).
      apply withinBounds_true_iff.
      pose proof Hmain_data_size as Hsize.
      rewrite /cmdc_main_data /= in Hsize. split; solve_addr. }
    assert (is_mmio_address (cmpt_b_cgp main_cmpt ^+ 1) = false) as Hmain1_shadow.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio main_cmpt).
      apply withinBounds_true_iff.
      pose proof Hmain_data_size as Hsize.
      rewrite /cmdc_main_data /= in Hsize. split; solve_addr. }
    assert (is_heap_address (cmpt_b_cgp main_cmpt ^+ 1) = false) as Hmain1_heap.
    { eapply disjoint_from_heap_not_in;
        first exact (cmpt_cgp_disjoint_from_heap main_cmpt).
      apply withinBounds_true_iff.
      pose proof Hmain_data_size as Hsize.
      rewrite /cmdc_main_data /= in Hsize. split; solve_addr. }
    iApply (cmdc_spec (th := UserThread 0) (swlayout := swl) (assertlayout := asl)
              (B := B) (C := C)
              _ _ _ _ _ _ _
              _ _ _ _ _
              [] [] _ _ _
              (cmpt_pcc_disjoint_from_shadow main_cmpt)
              (cmpt_pcc_base_not_heap main_cmpt)
              Hmain_shadow (cmpt_cgp_base_not_heap main_cmpt)
              Hmain1_shadow Hmain1_heap
              (stack_disjoint_from_mmio swc)
              (stack_disjoint_from_heap swc)
             with "[ $Hassert $Hthread_B $Hthread_C $Hswitcher $Hswitcher_static $Hna
                    $Hworld_B $Hworld_C
                    $HPC $Hcgp $Hcsp $Hcra $Hregs
                    $Hmain_imports $Hmain_code $Hmain_data $Hstack
                    $Hinterp_B $Hinterp_C $Hcstk $Hrevoked_stack_B $Hrevoked_stack_C
                    $Hentry_Bf $Hentry_Cg
                    $HMIE $Hheld
                    ]"); eauto using fw_cleared_regs_dom.
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply (main_cgp_not_in_adv_world Revoked fw_world0 swc main_cmpt); [done | |].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply (main_cgp_not_in_adv_world Revoked fw_world0 swc main_cmpt); [done | |].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    { by rewrite /route_pre. }
  Qed.
End cmdc_isolated_obligations.
