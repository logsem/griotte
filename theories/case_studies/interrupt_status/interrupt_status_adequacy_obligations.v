From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy_obligations
  firmware_obligations firmware_thread_obligations ist_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import interrupt_status_spec.
From griotte Require Import assert_spec.
From griotte Require Import world_interp_allocation.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import
  compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.

Section ist_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {B Sched : CmptName}.
  Context `{MP : MachineParameters}.

  (** The threads of the compartments: the context-switch thread in the
      scheduler's [Sched]; both user threads in [B], in shared mode. *)
  Definition ist_cthreads : CmptThreads := {|
    cmpt_threads := λ X,
      if decide (X = Sched) then {[CtxSwitch]} else {[UserThread 0; UserThread 1]};
    cmpt_shared := λ X, if decide (X = Sched) then false else true;
    cmpt_threads_sep := ltac:(intros X t; cbv beta; repeat case_decide; set_solver) |}.

  (** The obligations of the trusted code of the interrupt-status firmware:
      the thread 0 runs safely from the export [run] of [K], entered with
      interrupts disabled, the thread 1 from the export [adv] of the
      untrusted compartment ["B"], owned by the logical compartment [B],
      which both threads share; the scheduler runs in [Sched]. *)
  Lemma ist_fw_obligations :
    B ≠ Sched →
    fw_obligations Σ ist_firmware.
  Proof.
    intros HBS.
    exists ist_cthreads, Sched.
    split; first by (cbn; rewrite decide_True; [set_solver | done]).
    split; first by (cbn; rewrite decide_True).
    set (cthreads := ist_cthreads).
    assert (@cmpt_threads _ cthreads B = {[UserThread 0; UserThread 1]}) as HB_threads.
    { rewrite /cthreads /ist_cthreads /=. by rewrite decide_False. }
    assert (@cmpt_shared _ cthreads B = true) as HB_shared.
    { rewrite /cthreads /ist_cthreads /=. by rewrite decide_False. }
    assert (UserThread 0 ∈ @cmpt_threads _ cthreads B) as Hin0_B.
    { rewrite HB_threads. set_solver. }
    assert (UserThread 1 ∈ @cmpt_threads _ cthreads B) as Hin1_B.
    { rewrite HB_threads. set_solver. }
    assert (fw_threads ist_firmware = [fw_thread_of ist_firmware 0; fw_thread_of ist_firmware 1])
      as Hthreads by reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.
    (* The entry of [K.run] disables interrupts *)
    assert (fw_entry_posture ist_firmware img 0 = InterruptDisabled) as Hposture0
      by reflexivity.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_K.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts ist_firmware
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
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry ist_B_entry_f)).
    assert (cmpt_export_sb (cmpt_of img "B") ist_B_entry_f = B_f) as HsbB.
    { by rewrite /cmpt_export_sb /B_f /=. }
    assert (image.cmpt_imports (cmpt_of img "K") = @ist_K_imports swl asl B_f)
      as K_imports'.
    { rewrite K_imports /ist_K_imports. done. }

    (* 3 - The outer update: B opened on its map of Permanent regions, which
       goes into its invariant *)
    iIntros "Hshared". iNamed "Hshared".
    iDestruct "Hswitcher_static" as "#Hswitcher_static".
    iDestruct (fw_switcher_threads (cthreads := cthreads) ist_firmware img B
                with "Hswitcher_static Hswitcher_tstacks")
      as "#Hswitcher_threads_B".
    { intros t Ht. rewrite HB_threads in Ht.
      apply elem_of_union in Ht as [Ht | Ht]; apply elem_of_singleton in Ht as ->;
        [exists 0 | exists 1]; split; done || (cbn; lia). }
    iClear "Hswitcher_tstacks".
    iEval (rewrite Hthreads big_sepL_cons big_sepL_singleton) in "Hswitcher_static".
    iDestruct "Hswitcher_static" as "[#Hswitcher_static #Hstatic1]".
    iEval (cbv [ist_firmware fw_cmpts]; rewrite !big_sepL_cons big_sepL_nil;
           cbv [fw_cmpt_res_user fc_body]) in "Hcmpts".
    iDestruct "Hcmpts" as "((HK & _ & _) & (HB_mem & _ & #HB_pers) & _)".
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hperm_B _]".
    { apply elem_of_difference. split; last set_solver+HBS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) B Hin0_B) as "#Hthread_B".
    iMod (fw_open_adv_cmpt_perm (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts ist_firmware) default_fw_cmpt) _ HB_l fw_world0 B
            Hok eq_refl eq_refl ltac:(cbn; repeat constructor; lia)
           with "Hswitcher_threads_B Hswitcher_static HB_mem HB_pers [] Hthread_B Hperm_B")
      as "(Hperm_B & #Hpcc_B & #Hcgp_B & #Hinterp_B_exports)".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher_threads_B"). }
    iEval (cbn [ub_exports]; rewrite big_sepL_cons) in "Hinterp_B_exports".
    iDestruct "Hinterp_B_exports" as "[#Hinterp_B_f _]".
    iMod (world_resources_init_all ⊤ {[B]} with "[Hperm_B]") as "[Hinv_B _]".
    { rewrite big_sepS_singleton. iFrame. }
    assert (shared_of {[B]} = {[B]}) as Hshared_B.
    { apply filter_singleton_True_L; [apply _ | exact HB_shared]. }
    iEval (rewrite Hshared_B big_sepS_singleton) in "Hinv_B".
    iDestruct "Hinv_B" as "#Hinv_B".
    iModIntro.
    rewrite Hthreads big_sepL_cons big_sepL_singleton.
    (* every spatial hypothesis to the thread 0 *)
    iSplitL.
    2: {
      (* The thread 1, in the shared B, by the FTLR *)
      iApply (fw_shared_thread_obligation (cthreads := cthreads)
                ist_firmware img σ 1 (fw_thread_of ist_firmware 1) _ B fw_world0 HB_l
                Hok with "Hstatic1 HB_pers Hpcc_B Hcgp_B Hinv_B").
      - reflexivity.
      - reflexivity.
      - exact Hin1_B.
      - exact HB_shared.
    }
    (* The thread 0, in K: its world of B is its local map with its stack
       revoked, joined with the invariant of B; its posture is the one of
       its entry *)
    iClear "Hstatic1".
    iIntros "Hthread _". iNamed "Hthread".
    iEval (rewrite Hposture0) in "HMIE Hheld".
    iEval (rewrite (fw_entry_pc_code ist_firmware img σ ltac:(reflexivity) Hok)) in "HPC".
    iEval (rewrite fw_thread_cra_eq) in "Hcra".
    iEval (rewrite /fw_thread_csp; cbv zeta) in "Hcsp".
    iEval (rewrite /fw_entry_cgp; cbv zeta) in "Hcgp".
    iEval (rewrite /fw_entry_frame /fw_thread_csp /fw_entry_tbl; cbv zeta) in "Hcstk Hhwm".
    iDestruct (big_sepS_elem_of _ _ B with "Hlocals") as "Hlocal_B".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iMod (fw_shared_caller_world img 0 B HB_shared with "Hinv_B Hlocal_B")
      as "[Hworld_B Hrevoked_stack_B]".
    set (Wk := std_update_multiple fw_world0
                 (finz.seq_between (image.b_stack (thread_of img 0))
                    (image.e_stack (thread_of img 0)))
                 Revoked).
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack ist_firmware 0) with 4 in Hentry_min_stack.
    cbn [fc_name].
    change (fw_entry_cmpt ist_firmware img 0) with (cmpt_of img "K").
    iMod (fw_cmpt_mem_persist with "HK") as "(#HK_imports & #HK_code & HK_data)";
      first exact HK_l.
    rewrite K_imports' K_code K_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ ist_B_entry_f 1
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".
    (* The export of B, from the empty world to the world of the call *)
    iEval (cbn [fc_name fw_nth fw_cmpts ist_firmware]; rewrite HsbB) in "Hinterp_B_f".
    iDestruct (interp_sealed_global_kind_world_free fw_world0 Wk B _ _ _ None
                with "[] Hinterp_B_f") as "#Hinterp_B".
    { iApply (switcher_static_seal_pred with "Hswitcher_static"). }
    iClear "Hinterp_B_f Hpcc_B Hcgp_B HB_pers".
    fw_fold_cmpt K_cmpt.

    (* 4 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ K_imports' K_code K_data)
      as (HK_bounds & HK_data_size & HK_imports_size).
    assert (is_mmio_address (cmpt_b_cgp K_cmpt) = false) as HK_cgp_mmio.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio K_cmpt).
      apply withinBounds_true_iff.
      pose proof HK_data_size as Hsize.
      rewrite /ist_K_data /= in Hsize. split; solve_addr. }
    iApply (ist_spec (th := UserThread 0) (cthreads := cthreads)
              (swlayout := swl) (assertlayout := asl) (B := B)
              _ _ _ _ _ _ _
              _ _ Wk [] [] _ _
              (cmpt_pcc_disjoint_from_shadow K_cmpt)
              (cmpt_pcc_base_not_heap K_cmpt)
              HK_cgp_mmio
              (cmpt_cgp_base_not_heap K_cmpt)
              (stack_disjoint_from_mmio swc)
              (stack_disjoint_from_heap swc)
             with "[ $Hassert $Hthread_B $Hswitcher $Hswitcher_static $Hna
                    $Hworld_B
                    $HPC $Hcgp $Hcsp $Hcra $Hregs
                    $HK_imports $HK_code $HK_data $Hstack
                    $Hinterp_B $Hcstk $Hhwm $Hrevoked_stack_B
                    $Hentry_Bf
                    $HMIE $Hheld
                    ]"); eauto using fw_cleared_regs_dom.
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
  Qed.
End ist_obligations.
