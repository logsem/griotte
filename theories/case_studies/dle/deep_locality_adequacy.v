From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  dle_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import deep_locality deep_locality_spec.
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

Section dle_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {C : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the deep-locality firmware:
      the thread runs safely from the export of [main], the untrusted
      compartment ["C"] being owned by the logical compartment [C]. *)
  Lemma dle_fw_obligations :
    fw_obligations Σ dle_firmware.
  Proof.
    apply fw_obligations_of; first reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts dle_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb] in Hok_main.
    destruct Hok_main as (main_imports & _ & main_code & main_data & _).
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

    (* 2 - The export entry of C, imported by main *)
    set (C_f := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry dle_C_entry_f)).
    assert (cmpt_export_sb (cmpt_of img "C") dle_C_entry_f = C_f) as HsbC.
    { by rewrite /cmpt_export_sb /C_f /=. }
    assert (image.cmpt_imports (cmpt_of img "main") = @dle_main_imports swl asl C_f)
      as main_imports'.
    { rewrite main_imports /dle_main_imports. done. }

    (* 3 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack dle_firmware 0) with 4 in Hentry_min_stack.
    iEval (cbv [dle_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "((Hmain & _ & _) & (HC & _ & #HC_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt dle_firmware img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    rewrite main_imports' main_code main_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ dle_C_entry_f 1
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HC_pers")
      as "#Hentry_Cf"; [done|lia|].
    iEval (rewrite HsbC) in "Hentry_Cf".
    iDestruct (big_sepS_elem_of_acc _ _ C with "Hworlds") as "[Hworld_C _]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }

    (* 4 - Close the world of C: its compartment becomes Global regions, and the
       stack temporary, because main shares it with C; its export is safe
       to share. *)
    iMod (fw_close_adv_world (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts dle_firmware) default_fw_cmpt) _
            HC_l fw_world0 C Hok eq_refl eq_refl ltac:(apply Forall_singleton; cbn; lia) ltac:(done)
           with "Hswitcher Hswitcher_static HC HC_pers Hstack [] Hworld_C")
      as "(Hworld_C & #Hinterp_stack_C & [#Hinterp_C _])".
    { iIntros "_". iSplit; last done.
      by iApply (fw_switcher_call_safe with "Hswitcher Hswitcher_static"). }
    iEval (rewrite /fw_thread_csp) in "Hinterp_stack_C".
    cbn [fc_name fw_nth fw_cmpts dle_firmware]. rewrite HsbC.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt C_cmpt.

    (* 5 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    iPoseProof (dle_spec (swlayout := swl) (assertlayout := asl) (C := C)
                  _ _ _ _ _ _ _ _ _ _ [] [] _
                 with "[ $Hassert $Hswitcher $Hswitcher_static $Hna
                        $Hworld_C
                        $HPC $Hcgp $Hcsp $Hcra $Hregs
                        $Hmain_imports $Hmain_code $Hmain_data
                        $Hinterp_C $Hcstk
                        $Hentry_Cf $Hinterp_stack_C
                        ]") as "Hspec"; eauto using fw_cleared_regs_dom.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { exact (cmpt_cgp_disjoint_from_mmio main_cmpt). }
    { exact (cmpt_cgp_not_heap_range main_cmpt). }
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply (main_cgp_not_in_adv_world Temporary fw_world0 swc main_cmpt C_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply (main_cgp_not_in_adv_world Temporary fw_world0 swc main_cmpt C_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { done. }
    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End dle_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_dle := | C.
#[local] Instance CmptNames_dle_eq_dec : EqDecision CmptNames_dle.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_dle_finite : finite.Finite CmptNames_dle.
Proof.
  refine {| finite.enum := [C] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_dle_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_dle; |}.

(** The logical compartment of the adversary. *)
Definition dle_adv_C : @CmptName CmptNames_dle_CmptNameG := C.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem dle_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  dle_initial_state_ok flag σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (dle_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & C & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_dle_CmptNameG) #[]
            dle_firmware (dle_img sw asrt t0 main C));
    [| exact Hfw | exact Hstep].
  apply (dle_fw_obligations (C := dle_adv_C)).
Qed.
