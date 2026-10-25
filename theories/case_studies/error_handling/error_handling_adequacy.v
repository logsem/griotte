From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  error_handling_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  error_handling error_handling_spec_handler error_handling_spec_read
  error_handling_spec_read_safe error_handling_main_spec.
From griotte Require Import assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.

Section error_handling_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {C : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the error-handling firmware:
      the thread runs safely from the export [entry] of [main], the
      untrusted compartment ["adv"] being owned by the logical compartment
      [C]. *)
  Lemma error_handling_fw_obligations :
    fw_obligations Σ error_handling_firmware.
  Proof.
    apply fw_obligations_of; first reflexivity.
    intros img σ ceriseg seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    pose proof (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) as Hok_stats.
    pose proof (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) as Hok_adv.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts error_handling_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb]
      in Hok_main, Hok_stats, Hok_adv.
    destruct Hok_main as (main_imports & _ & main_code & main_data & _ & main_exp_tbl).
    destruct Hok_stats as (stats_imports & _ & stats_code_eq & stats_data_eq & _ & stats_exp_tbl).
    destruct Hok_adv as (adv_imports & _).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as Hmain_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as Hstats_l.
    pose proof (fw_cmpt_layout_at _ _ _ 2 _ Hok eq_refl) as Hadv_l.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 1 _ Hstats_l eq_refl) as Hsw_stats.
    cbn [fc_name] in Hmain_l, Hstats_l, Hadv_l, Hsw_stats.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l).
    set (stats_cmpt := layout_cmpt_of (cmpt_of img "stats") Hstats_l).
    set (adv_cmpt := layout_cmpt_of (cmpt_of img "adv") Hadv_l).
    fw_fold_cmpt main_cmpt. fw_fold_cmpt stats_cmpt. fw_fold_cmpt adv_cmpt.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    set (swl := fw_switcher_layout img) in *.
    set (asl := fw_assert_layout img).

    (* 2 - The layout of [stats] *)
    pose (statsl := mkStatsLayout
            (cmpt_b_pcc stats_cmpt) (cmpt_a_code stats_cmpt) (cmpt_e_pcc stats_cmpt)
            (cmpt_b_cgp stats_cmpt) (cmpt_e_cgp stats_cmpt)
            (cmpt_exp_tbl_pcc stats_cmpt) (cmpt_exp_tbl_entries_end stats_cmpt)).
    assert statsLayoutWf as statslWf.
    { refine (mkStatsLayoutWf _ _ _ _ _ _ _ _ _ _ _); cbn.
      - pose proof (cmpt_import_size stats_cmpt) as Hsize.
        by rewrite stats_imports in Hsize.
      - pose proof (cmpt_code_size stats_cmpt) as Hsize.
        by rewrite stats_code_eq in Hsize.
      - pose proof (cmpt_data_size stats_cmpt) as Hsize.
        by rewrite stats_data_eq in Hsize.
      - pose proof (cmpt_exp_tbl_pcc_size stats_cmpt) as Hsize_pcc.
        pose proof (cmpt_exp_tbl_header_size stats_cmpt) as Hsize_header.
        pose proof (cmpt_exp_tbl_entries_size stats_cmpt) as Hsize_entries.
        rewrite stats_exp_tbl in Hsize_entries.
        rewrite /length_stats_exports_tbl /stats_nb_exports.
        cbn in *. solve_addr+Hsize_pcc Hsize_header Hsize_entries.
      - exact (cmpt_cgp_disjoint_from_shadow stats_cmpt).
      - exact (cmpt_pcc_disjoint_from_shadow stats_cmpt).
      - exact (cmpt_exp_tbl_disjoint_from_shadow stats_cmpt).
      - exact (cmpt_pcc_base_not_heap stats_cmpt).
      - exact (cmpt_cgp_base_not_heap stats_cmpt).
      - exact (cmpt_exp_tbl_base_not_heap stats_cmpt). }
    (* The code of [stats] is outside the switcher's: its faults are not
       resumed by the exception path *)
    assert (cmpt_b_pcc stats_cmpt ≠ switcher.b_switcher) as Hstats_switcher.
    { apply (switcher_cmpt_disjoint_pcc_b stats_cmpt _ Hsw_stats).
      pose proof (cmpt_import_size stats_cmpt) as Himports_size.
      pose proof (cmpt_code_size stats_cmpt) as Hcode_size.
      rewrite stats_imports in Himports_size; cbn [length] in Himports_size.
      rewrite stats_code_eq in Hcode_size.
      assert (length stats_code = 16%nat) as Hcode_length by reflexivity.
      rewrite Hcode_length in Hcode_size.
      solve_addr+Himports_size Hcode_size. }
    (* [stats] has no import: its code starts at the base of its PCC *)
    assert (cmpt_a_code stats_cmpt = cmpt_b_pcc stats_cmpt) as Hstats_code_start.
    { pose proof (cmpt_import_size stats_cmpt) as Hsize.
      rewrite stats_imports in Hsize; cbn [length] in Hsize. solve_addr+Hsize. }

    (* 3 - The export of [adv], imported by [main] *)
    set (adv_f := SCap true RO Global (cmpt_exp_tbl_pcc adv_cmpt)
                    (cmpt_exp_tbl_entries_end adv_cmpt)
                    (cmpt_exp_tbl_pcc adv_cmpt
                       ^+ ExportTable_offset_entry error_handling_adv_entry)%a).
    assert (cmpt_export_sb (cmpt_of img "adv") error_handling_adv_entry = adv_f) as Hsb_adv.
    { by rewrite /cmpt_export_sb /adv_f /=. }
    assert (cmpt_imports main_cmpt = error_handling_main_imports adv_f) as main_imports'.
    { rewrite main_imports /error_handling_main_imports /STATS_read. done. }

    (* 4 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    iEval (cbv [error_handling_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts"
      as "((Hmain & _ & #Hmain_pers) & (Hstats & _ & #Hstats_pers) & (Hadv & _ & #Hadv_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt error_handling_firmware img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    iMod (fw_cmpt_mem_persist with "Hstats") as "(_ & #Hstats_code & Hstats_data)";
      first exact Hstats_l.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ error_handling_adv_entry 0
                 (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) with "Hadv_pers")
      as "#Hentry_adv"; [done | lia |].
    iEval (rewrite Hsb_adv) in "Hentry_adv".
    iPoseProof "Hstats_pers"
      as "(Hstats_etbl_pcc & Hstats_etbl_cgp & Hstats_etbl_eh & Hstats_etbl_entries)".
    (* The export table of [stats]: a stackful handler, no stackless one *)
    iEval (cbn [fw_handler_res fc_body tb_error_handler tb_error_handler_stackless])
      in "Hstats_etbl_eh".
    iEval (cbn [fc_name]) in "Hstats_etbl_pcc Hstats_etbl_cgp Hstats_etbl_entries".
    iDestruct (big_sepS_elem_of_acc _ _ C with "Hworlds") as "[Hworld_C _]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    fw_fold_cmpt main_cmpt. fw_fold_cmpt stats_cmpt. fw_fold_cmpt adv_cmpt.
    iEval (rewrite stats_exp_tbl big_sepL_cons) in "Hstats_etbl_entries".
    iDestruct "Hstats_etbl_entries" as "[Hstats_etbl_read _]".
    iDestruct "Hstats_etbl_eh" as "[Hstats_etbl_eh Hstats_etbl_ehs]".
    iEval (cbn [fc_name]) in "Hstats_etbl_eh Hstats_etbl_ehs". fw_fold_cmpt stats_cmpt.

    (* 4.1 The static resources of [stats] *)
    iAssert stats_static as "#Hstats_static".
    { rewrite /stats_static /stats_wpcc /stats_pcc /stats_wcgp.
      cbn [STATS_pcc_b STATS_pcc_e STATS_cgp_b STATS_cgp_e b_stats_exp_tbl e_stats_exp_tbl
           statsl].
      rewrite -cmpt_exp_tbl_cgp_eq -Hstats_code_start -stats_code_eq.
      iFrame "Hstats_code Hstats_etbl_pcc Hstats_etbl_cgp Hstats_etbl_eh Hstats_etbl_ehs
        Hstats_etbl_read". }

    (* 4.2 The lock of [stats], released, in [stats_inv] *)
    iEval (rewrite stats_data_eq) in "Hstats_data".
    iDestruct (region_pointsto_single with "Hstats_data") as (vlock) "[Hlock %Hvlock]".
    { pose proof (cmpt_data_size stats_cmpt) as Hsize. rewrite stats_data_eq in Hsize.
      exact Hsize. }
    rewrite /stats_data /= in Hvlock. injection Hvlock as <-.
    iMod (na_inv_alloc cerise_nais _ Nstats stats_inv with "[Hlock]") as "#Hinv_stats".
    { iNext. iExact "Hlock". }

    (* 5 - Seal the export [stats_read] with [ot_switcher] in the world of
       [adv] *)
    set (stats_read_sb :=
           SCap true RO Global b_stats_exp_tbl e_stats_exp_tbl stats_read_exp_tbl_addr).
    set (W0' := <o[ switcher.ot_switcher :=
                    {[ lword_of_word (WSealable stats_read_sb);
                       lword_of_word (borrow (WSealable stats_read_sb)) ]} ]o> fw_world0).
    iAssert (ot_switcher_prop W0' C (WSealable stats_read_sb)) as "#Hot_switcher_read".
    { iApply (stats_read_entry_point_spec Global W0' C).
      - exact Hstats_switcher.
      - iFrame "Hswitcher Hswitcher_static Hstats_static Hinv_stats". }
    iMod (seal_main_export fw_world0 C stats_read_sb
           with "Hseal_switcher Hot_switcher_read Hworld_C")
      as "(Hworld_C & #Hinterp_read)"; [done | | done |].
    { intros p g b e a Heq; inversion Heq; subst.
      exact (cmpt_exp_tbl_disjoint_from_heap stats_cmpt). }

    (* 6 - The stack holds the minimum stack of the entry of [main]: the
       spill of its calls, the space reserved at the top of the callee's
       stack, and the minimum stack of [stats_read] *)
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hstk_size.
    change (fw_entry_min_stack error_handling_firmware 0) with 22%nat in Hstk_size.
    assert (∀ b e : Z, b + Z.of_nat 22 + StackEntry_reserved_space <= e →
              b + SpillSlot_size + 2 * StackEntry_reserved_space + stats_read_min_stack <= e)%Z
      as Hmin_bridge
      by (rewrite /SpillSlot_size /StackEntry_reserved_space /stats_read_min_stack; lia).
    apply Hmin_bridge in Hstk_size; clear Hmin_bridge.

    (* 7 - Close the world of [adv]: its compartment becomes permanent, and
       the stack temporary; [stats_read] is safe to import; the export of
       [adv] is safe to share. *)
    iMod (fw_close_adv_world _ _ _ 2 (fw_nth 2 (fw_cmpts error_handling_firmware) default_fw_cmpt)
            _ Hadv_l W0' C Hok eq_refl eq_refl ltac:(apply Forall_singleton; cbn; lia)
            ltac:(done)
           with "Hswitcher Hswitcher_static Hseal_switcher Hadv Hadv_pers Hstack [] Hworld_C")
      as "(Hworld_C & #Hinterp_stack_C & [#Hinterp_adv _])".
    { iIntros "_". cbn [fc_name fc_imports fw_nth fw_cmpts error_handling_firmware].
      iSplit; first by iApply (fw_switcher_call_safe with "Hswitcher Hswitcher_static").
      iSplit; last done.
      rewrite /fw_import_safe /fw_word_of /note.
      cbv [fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts
           error_handling_firmware fc_name fc_body tb_exports fe_name String.eqb Ascii.eqb
           Bool.eqb andb addr_off].
      fw_fold_cmpt stats_cmpt.
      fold stats_read_sb.
      iSplit.
      - iApply interp_to_in_mem.
        iApply (interp_monotone_sd_same_heap W0' with "[]").
        { by rewrite std_update_compartment_heap. }
        { iPureIntro.
          apply related_sts_pub_priv_world.
          eapply std_update_compartment_pub; eauto; (apply Forall_true; intros; done). }
        done.
      - iIntros (W2 W3) "!> %Hrelated Hinterp".
        iEval (cbn) in "Hinterp".
        iApply (interp_in_mem_monotone_nl W2 W3 C RWL with "Hinterp"); first exact Hrelated.
        done. }
    iEval (rewrite /fw_thread_csp) in "Hinterp_stack_C".
    cbn [fc_name fw_nth fw_cmpts error_handling_firmware]. rewrite Hsb_adv.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt adv_cmpt.

    (* 8 - We can apply the specification! *)
    iEval (rewrite main_imports') in "Hmain_imports".
    iEval (rewrite main_code) in "Hmain_code".
    iEval (rewrite main_data) in "Hmain_data".
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    iPoseProof (error_handling_main_spec (swlayout := swl) (assertlayout := asl)
                  (statslayout := statsl) (C := C)
                  _ _ _ _ _ _ _ _ adv_f _ [] [] _
                 with "[$Hassert $Hswitcher $Hswitcher_static $Hstats_static $Hinv_stats
                        $Hna $HPC $Hcgp $Hcsp $Hregs $Hmain_imports $Hmain_code $Hmain_data
                        $Hworld_C $Hcstk $Hinterp_adv $Hentry_adv $Hinterp_stack_C]")
      as "Hspec".
    all: [> exact Hstats_switcher
      | split_and!; [exact Hmain_bounds | exact Hmain_imports_size
                    | exact (cmpt_pcc_disjoint_from_shadow main_cmpt)
                    | exact (cmpt_pcc_base_not_heap main_cmpt)]
      | exact Hmain_data_size
      | exact (cmpt_cgp_base_not_heap main_cmpt)
      | eapply disjoint_from_shadow_not_in;
        first exact (cmpt_cgp_disjoint_from_shadow main_cmpt);
        apply withinBounds_true_iff; cbn in Hmain_data_size |- *; solve_addr+Hmain_data_size
      | exact fw_cleared_regs_dom
      | intros r Hr; by rewrite fw_cleared_regs_lookup
      | exact Hstk_size
      | apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap
      | done
      | ].
    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End error_handling_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_error_handling := | Adv.
#[local] Instance CmptNames_error_handling_eq_dec : EqDecision CmptNames_error_handling.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_error_handling_finite : finite.Finite CmptNames_error_handling.
Proof.
  refine {| finite.enum := [Adv] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_error_handling_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_error_handling; |}.

(** The logical compartment of the adversary. *)
Definition error_handling_adv_name : @CmptName CmptNames_error_handling_CmptNameG := Adv.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem error_handling_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  error_handling_initial_state_ok flag σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (error_handling_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & stats & adv & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_error_handling_CmptNameG) #[]
            error_handling_firmware (error_handling_img sw asrt t0 main stats adv));
    [| exact Hfw | exact Hstep].
  apply (error_handling_fw_obligations (C := error_handling_adv_name)).
Qed.
