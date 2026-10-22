From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  cmdc_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import cmdc cmdc_spec.
From griotte Require Import switcher assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.

Section cmdc_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {B C : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the CMDC firmware: the thread
      runs safely from the export of [main], the untrusted compartments
      ["B"] and ["C"] being owned by the logical compartments [B] and
      [C]. *)
  Lemma cmdc_fw_obligations :
    B ≠ C →
    fw_obligations Σ cmdc_firmware.
  Proof.
    intros HBC. apply fw_obligations_of; first reflexivity.
    intros img σ ceriseg seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts cmdc_firmware
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
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry cmdc_B_entry_f)%a).
    set (C_g := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry cmdc_C_entry_g)%a).
    assert (cmpt_export_sb (cmpt_of img "B") cmdc_B_entry_f = B_f ∧
            cmpt_export_sb (cmpt_of img "C") cmdc_C_entry_g = C_g) as (HsbB & HsbC).
    { by rewrite /cmpt_export_sb /B_f /C_g /=. }
    assert (image.cmpt_imports (cmpt_of img "main") = @cmdc_main_imports swl asl B_f C_g)
      as main_imports'.
    { rewrite main_imports /cmdc_main_imports. done. }

    (* 3 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack cmdc_firmware 0) with 4 in Hentry_min_stack.
    iEval (cbv [cmdc_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "((Hmain & _ & _) & (HB & _ & #HB_pers) & (HC & _ & #HC_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt cmdc_firmware img 0) with (cmpt_of img "main").
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
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hworld_B Hworlds]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ C with "Hworlds") as "[Hworld_C _]".
    { apply elem_of_difference. split; last set_solver+HBC.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }

    (* 4 - Close the worlds of B and C: their compartments become permanent,
       and the stack is revoked, because main keeps it; their exports are
       safe to share. *)
    iMod (fw_close_adv_world_revoked _ _ _ 1 (fw_nth 1 (fw_cmpts cmdc_firmware) default_fw_cmpt)
            _ HB_l fw_world0 B Hok eq_refl eq_refl
            ltac:(apply Forall_singleton; cbn; rewrite /cmdc_B_f_args; lia) ltac:(done)
           with "Hswitcher Hswitcher_static Hseal_switcher HB HB_pers [] Hworld_B")
      as "(Hworld_B & Hrevoked_stack_B & [#Hinterp_B _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher Hswitcher_static"). }
    iMod (fw_close_adv_world_revoked _ _ _ 2 (fw_nth 2 (fw_cmpts cmdc_firmware) default_fw_cmpt)
            _ HC_l fw_world0 C Hok eq_refl eq_refl
            ltac:(apply Forall_singleton; cbn; rewrite /cmdc_C_g_args; lia) ltac:(done)
           with "Hswitcher Hswitcher_static Hseal_switcher HC HC_pers [] Hworld_C")
      as "(Hworld_C & Hrevoked_stack_C & [#Hinterp_C _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher Hswitcher_static"). }
    cbn [fc_name fw_nth fw_cmpts cmdc_firmware]. rewrite HsbB HsbC.
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
    assert (is_mmio_address (cmpt_b_cgp main_cmpt ^+ 1)%a = false) as Hmain1_shadow.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio main_cmpt).
      apply withinBounds_true_iff.
      pose proof Hmain_data_size as Hsize.
      rewrite /cmdc_main_data /= in Hsize. split; solve_addr. }
    assert (is_heap_address (cmpt_b_cgp main_cmpt ^+ 1)%a = false) as Hmain1_heap.
    { eapply disjoint_from_heap_not_in;
        first exact (cmpt_cgp_disjoint_from_heap main_cmpt).
      apply withinBounds_true_iff.
      pose proof Hmain_data_size as Hsize.
      rewrite /cmdc_main_data /= in Hsize. split; solve_addr. }
    iApply (cmdc_spec_full (swlayout := swl) (assertlayout := asl) (B := B) (C := C)
              _ _ _ _ _ _ _
              _ _ _ _ _
              [] [] _ _ (fun _ => True)%I fw_switcherN fw_switcherN_trap_disj
              (cmpt_pcc_disjoint_from_shadow main_cmpt)
              (cmpt_pcc_base_not_heap main_cmpt)
              Hmain_shadow (cmpt_cgp_base_not_heap main_cmpt)
              Hmain1_shadow Hmain1_heap
              (stack_disjoint_from_mmio swc)
              (stack_disjoint_from_heap swc)
             with "[ $Hassert $Hswitcher $Hswitcher_static $Hna
                    $Hworld_B $Hworld_C
                    $HPC $Hcgp $Hcsp $Hregs
                    $Hmain_imports $Hmain_code $Hmain_data $Hstack
                    $Hinterp_B $Hinterp_C $Hcstk $Hrevoked_stack_B $Hrevoked_stack_C
                    $Hentry_Bf $Hentry_Cg
                    ]"); eauto using fw_cleared_regs_dom.
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply (main_cgp_not_in_adv_world Revoked fw_world0 swc main_cmpt B_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply (main_cgp_not_in_adv_world Revoked fw_world0 swc main_cmpt C_cmpt); [done | done | | ].
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
    iModIntro. iIntros "H". proofmode.wp_end; by iIntros.
  Qed.
End cmdc_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_CMDC := | B | C.
#[local] Instance CmptNames_CMDC_eq_dec : EqDecision CmptNames_CMDC.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
#[local] Instance CmptNames_CMDC_finite : finite.Finite CmptNames_CMDC.
Proof.
  refine {| finite.enum := [B; C] |}.
  + constructor; [ by rewrite list_elem_of_singleton | apply NoDup_singleton ].
  + intros [|]; [ left | right; left ].
Defined.

#[local] Program Instance CmptNames_CMDC_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_CMDC; |}.

(** The logical compartments of the adversaries. *)
Definition cmdc_adv_B : @CmptName CmptNames_CMDC_CmptNameG := B.
Definition cmdc_adv_C : @CmptName CmptNames_CMDC_CmptNameG := C.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem cmdc_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  cmdc_initial_state_ok flag σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (cmdc_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & B & C & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_CmptNameG) #[]
            cmdc_firmware (cmdc_img sw asrt t0 main B C));
    [| exact Hfw | exact Hstep].
  apply (cmdc_fw_obligations (B := cmdc_adv_B) (C := cmdc_adv_C)). done.
Qed.
