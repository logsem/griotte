From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  lse_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import lse lse_spec_states lse_spec_closure lse_spec.
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

Section lse_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {C : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the LSE downward firmware:
      the thread runs safely from the export [entry] of [main], the
      untrusted compartment ["C"] being owned by the logical compartment
      [C]. *)
  Lemma lse_fw_obligations :
    fw_obligations Σ lse_firmware.
  Proof.
    apply fw_obligations_of; first reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts lse_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb] in Hok_main.
    destruct Hok_main as (main_imports & _ & main_code & main_data & _ & main_exp_tbl).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as Hmain_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as HC_l.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (fw_cmpts_disjoint_at _ _ _ 0 1 _ _ Hmain_l HC_l Hok ltac:(done) eq_refl eq_refl)
      as HmainC.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 0 _ Hmain_l eq_refl) as Hsw_main.
    cbn [fc_name] in Hmain_l, HC_l, HmainC, Hsw_main.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l) in *.
    set (C_cmpt := layout_cmpt_of (cmpt_of img "C") HC_l) in *.
    set (swc := fw_switcher_cmpt _ _ _ Hok) in *.
    set (swl := fw_switcher_layout img) in *.
    set (asl := fw_assert_layout img).

    (* 2 - The export entries of C and main, imported by each other *)
    set (C_f := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry lse_C_entry_adv)%a).
    assert (cmpt_export_sb (cmpt_of img "C") lse_C_entry_adv = C_f) as HsbC.
    { by rewrite /cmpt_export_sb /C_f /=. }
    assert (image.cmpt_imports (cmpt_of img "main") = @lse_main_imports swl asl C_f)
      as main_imports'.
    { rewrite main_imports /lse_main_imports. done. }
    assert (WInt (encode_entry_point InterruptEnabled 0%nat 1%nat 12%nat) = @lse_exp_tbl_entry_f _ swl asl)
      as Hentry_f_word.
    { reflexivity. }

    (* 3 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack lse_firmware 0) with 4 in Hentry_min_stack.
    iEval (cbv [lse_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "((Hmain & _ & #Hmain_pers) & (HC & _ & #HC_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt lse_firmware img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    rewrite main_imports' main_code main_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ lse_C_entry_adv 0
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HC_pers")
      as "#Hentry_Cf"; [done|lia|].
    iEval (rewrite HsbC) in "Hentry_Cf".
    (* The export table of main, which exports [f] (its first entry) to C *)
    iPoseProof "Hmain_pers" as "(Hmain_etbl_pcc & Hmain_etbl_cgp & Hmain_etbl_nh & Hmain_etbl_entries)".
    iEval (cbn [fw_handler_res fc_body tb_error_handler tb_error_handler_stackless]) in "Hmain_etbl_nh".
    iEval (cbn [fc_name]) in "Hmain_etbl_pcc Hmain_etbl_cgp Hmain_etbl_entries".
    iEval (rewrite main_exp_tbl) in "Hmain_etbl_entries".
    iDestruct (big_sepS_elem_of_acc _ _ C with "Hworlds") as "[Hworld_C _]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    fw_fold_cmpt main_cmpt. fw_fold_cmpt C_cmpt.
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hmain_exp_tbl_size.
    rewrite main_exp_tbl in Hmain_exp_tbl_size.
    assert (cmpt_exp_tbl_pcc main_cmpt <= cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry lse_entry_f
            < cmpt_exp_tbl_entries_end main_cmpt)%a as Hmain_exp_tbl_bounds.
    { pose proof (cmpt_exp_tbl_header_size main_cmpt) as Hheader.
      clear -Hmain_exp_tbl_size Hheader. rewrite /lse_entry_f. cbn in *. solve_addr. }
    iEval (rewrite big_sepL_cons) in "Hmain_etbl_entries".
    iDestruct "Hmain_etbl_entries" as "[Hmain_etbl_f _]".
    rewrite (cmpt_exp_tbl_cgp_eq main_cmpt).
    rewrite Hentry_f_word.

    (* 4 - The global [a] of main, in an invariant *)
    iDestruct (region_pointsto_single with "Hmain_data") as "[%v [Hcgp_b %Hv] ]".
    { solve_addr+Hmain_data_size. }
    rewrite /lse_main_data /= in Hv; simplify_eq.
    iMod (na_inv_alloc (tpool (UserThread 0)) _ Nlse _ with "Hcgp_b") as "#Hlse_data".

    (* 5 - Seal the exported entry [f] of main with [ot_switcher] in the
       world of C *)
    set (C_f := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry lse_C_entry_adv)%a) in *.
    set (main_f := SCap true RO Global (cmpt_exp_tbl_pcc main_cmpt)
                     (cmpt_exp_tbl_entries_end main_cmpt)
                       (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry lse_entry_f)%a) in *.
    set (W0' := <o[ switcher.ot_switcher :=
                    {[ lword_of_word (WSealable main_f);
                       lword_of_word (borrow (WSealable main_f)) ]} ]o> fw_world0).
    iAssert (ot_switcher_prop (th := UserThread 0) W0' C (WSealable main_f))
      as "#Hot_switcher_main_f".
    { assert (is_Some (cmpt_b_pcc main_cmpt +
                         (length_lse_main_imports + length LSE_main_code_run))%a)
        as Hentry_some.
      { pose proof (cmpt_code_size main_cmpt) as Hcode_size.
        rewrite main_code /lse_main_code /LSE_main_code_run /LSE_main_code_f /= in Hcode_size.
        rewrite /lse_main_imports /= in Hmain_imports_size.
        rewrite /length_lse_main_imports /lse_main_imports /LSE_main_code_run /=.
        solve_addr+Hmain_imports_size Hcode_size. }
      iApply (lse_f_spec (swlayout := swl) (assertlayout := asl)
                _ _ _ _ _ _ _ _ _ W0');
        last iFrame "#"; auto.
      { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
      { eapply disjoint_from_shadow_not_in;
          first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
        apply withinBounds_true_iff; cbn in Hmain_data_size |- *; solve_addr+Hmain_data_size. }
      { exact (cmpt_cgp_base_not_heap main_cmpt). }
      { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
      exact (cmpt_pcc_base_not_heap main_cmpt). }
    iMod (seal_main_export fw_world0 C main_f
           with "Hseal_switcher Hot_switcher_main_f Hworld_C")
      as "(Hworld_C & #Hinterp_main_f)"; [done| |done|].
    { intros ????? Heq; inversion Heq; subst.
      exact (cmpt_exp_tbl_disjoint_from_heap main_cmpt). }

    (* 6 - Close the world of C: its compartment becomes permanent, and the
       stack temporary, because main shares it with C; the exported entry
       [f] of main is safe to import; the export of C is safe to share. *)
    iMod (fw_close_adv_world (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts lse_firmware) default_fw_cmpt) _
            HC_l W0' C Hok eq_refl eq_refl ltac:(apply Forall_singleton; cbn; lia) ltac:(done)
           with "Hswitcher Hswitcher_static Hseal_switcher HC HC_pers Hstack [] Hworld_C")
      as "(Hworld_C & #Hinterp_stack_C & [#Hinterp_C _])".
    { iIntros "_". cbn [fc_name fc_imports fw_nth fw_cmpts lse_firmware].
      iSplit; first by iApply (fw_switcher_call_safe with "Hswitcher Hswitcher_static").
      iSplit; last done.
      rewrite /fw_import_safe /fw_word_of /note.
      cbv [fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts lse_firmware
           fc_name fc_body tb_exports fe_name String.eqb Ascii.eqb Bool.eqb andb addr_off].
      fw_fold_cmpt main_cmpt.
      change (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry 0)%a
        with (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry lse_entry_f)%a.
      fold main_f.
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
    cbn [fc_name fw_nth fw_cmpts lse_firmware]. rewrite HsbC.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt C_cmpt.

    (* 7 - We can apply the specification! *)
    iPoseProof (lse_run_spec (swlayout := swl) (assertlayout := asl) (C := C)
                  _ _ _ _ _ _ _ _ _ _ _ _ [] [] _
                 with "[ $Hassert $Hswitcher $Hswitcher_static
                         $Hmain_imports $Hmain_code $Hlse_data
                         $Hmain_etbl_pcc $Hmain_etbl_cgp $Hmain_etbl_f
                         $Hna
                         $Hworld_C
                         $HPC $Hcgp $Hcsp $Hcra $Hregs
                         $Hcstk $Hinterp_stack_C
                         $Hinterp_C $Hentry_Cf
                         $Hseal_switcher
                        ]") as "Hspec"; eauto using fw_cleared_regs_dom.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { eapply disjoint_from_shadow_not_in;
        first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
      apply withinBounds_true_iff; cbn in Hmain_data_size |- *; solve_addr+Hmain_data_size. }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { done. }
    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End lse_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_lse := | C.
#[local] Instance CmptNames_lse_eq_dec : EqDecision CmptNames_lse.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_lse_finite : finite.Finite CmptNames_lse.
Proof.
  refine {| finite.enum := [C] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_lse_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_lse; |}.

(** The logical compartment of the adversary. *)
Definition lse_adv_C : @CmptName CmptNames_lse_CmptNameG := C.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem lse_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  lse_initial_state_ok flag σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (lse_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & C & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_lse_CmptNameG) #[]
            lse_firmware (lse_img sw asrt t0 main C));
    [| exact Hfw | exact Hstep].
  apply (lse_fw_obligations (C := lse_adv_C)).
Qed.
