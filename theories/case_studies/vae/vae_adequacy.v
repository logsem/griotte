From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  vae_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import vae vae_helper vae_spec_closure vae_spec.
From griotte Require Import assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.

Section vae_obligations.
  Context {Σ : gFunctors}.
  Context {cname : CmptNameG} {C : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the very awkward example's
      firmware: the thread runs safely from the export [entry] of [main],
      the untrusted compartment ["C"] being owned by the logical
      compartment [C]. *)
  Lemma vae_fw_obligations :
    fw_obligations Σ vae_firmware.
  Proof.
    pose (cthreads := {| cmpt_threads := λ _, {[UserThread 0]} |} : CmptThreads).
    assert (Hpin : ∀ C', cmpt_threads C' ⊆ {[UserThread 0]}) by (intros; reflexivity).
    assert (Hin : ∀ C', UserThread 0 ∈ cmpt_threads C') by (intros; rewrite /cthreads /=; set_solver).
    apply (fw_obligations_of Σ (cthreads := cthreads)); first reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts vae_firmware
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
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry vae_C_entry_adv)).
    assert (cmpt_export_sb (cmpt_of img "C") vae_C_entry_adv = C_f) as HsbC.
    { by rewrite /cmpt_export_sb /C_f /=. }
    assert (image.cmpt_imports (cmpt_of img "main") = @vae_main_imports swl asl C_f)
      as main_imports'.
    { rewrite main_imports /vae_main_imports. done. }
    assert (WInt (encode_entry_point InterruptEnabled 1%nat 4%nat 12%nat) =
              WInt (encode_entry_point InterruptEnabled 1 4
                      (length (@vae_main_imports swl asl C_f ++ VAE_main_code_init))))
      as Hentry_awk_word.
    { reflexivity. }

    (* 3 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) C (Hin C)) as "#Hthread_C".
    iDestruct (switcher_threads_pinned (UserThread 0) C (Hpin C) with "Hswitcher Hswitcher_static")
      as "#Hswitcher_threads_C".
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack vae_firmware 0) with 4 in Hentry_min_stack.
    iEval (cbv [vae_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "((Hmain & _ & #Hmain_pers) & (HC & _ & #HC_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt vae_firmware img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    rewrite main_imports' main_code main_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ vae_C_entry_adv 0
                 (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) with "HC_pers")
      as "#Hentry_Cf"; [done|lia|].
    iEval (rewrite HsbC) in "Hentry_Cf".
    (* The export table of main, which exports [awkward] (its first entry)
       to C *)
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
    assert (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry vae_entry_awkward ∈ₐ [cmpt_exp_tbl_pcc main_cmpt, cmpt_exp_tbl_entries_end main_cmpt)) as Hmain_exp_tbl_bounds.
    { pose proof (cmpt_exp_tbl_header_size main_cmpt) as Hheader.
      clear -Hmain_exp_tbl_size Hheader. rewrite /vae_entry_awkward. cbn in *. solve_addr. }
    iEval (rewrite big_sepL_cons) in "Hmain_etbl_entries".
    iDestruct "Hmain_etbl_entries" as "[Hmain_etbl_awk _]".
    rewrite (cmpt_exp_tbl_cgp_eq main_cmpt).
    rewrite Hentry_awk_word.

    (* 4 - The global [a] of main, in an invariant over a custom location
       of the world of C *)
    iDestruct (region_pointsto_single with "Hmain_data") as "[%v [Hcgp_b %Hv] ]".
    { solve_addr+Hmain_data_size. }
    rewrite /vae_main_data /= in Hv; simplify_eq.
    set (i := fresh_cus_name fw_world0).
    set (W1 := <l[i := false, (awk_rel_pub, awk_rel_priv)]l> fw_world0).
    iMod (world_interp_alloc_loc (th := UserThread 0) _ C false awk_rel_pub awk_rel_priv with "Hworld_C")
      as "(Hworld_C & %Hloc_fresh & %Hcus_fresh & Hst_i & #Hrel_i)".
    iMod (inv_alloc Nawk _ (awk_inv (th := UserThread 0) C i _)
           with "[Hcgp_b Hst_i]") as "#Hawk_inv".
    { iExists false; iFrame. }

    (* 5 - Seal the exported entry [awkward] of main with [ot_switcher] in
       the world of C *)
    set (C_f := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_entry vae_C_entry_adv)) in *.
    set (main_awk := SCap true RO Global (cmpt_exp_tbl_pcc main_cmpt)
                       (cmpt_exp_tbl_entries_end main_cmpt)
                       (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry vae_entry_awkward)) in *.
    iAssert (ot_switcher_prop (th := UserThread 0) W1 C (WSealable main_awk))
      as "#Hot_switcher_main_awk".
    { assert (is_Some (cmpt_b_pcc main_cmpt +
                         length (@vae_main_imports swl asl C_f ++ VAE_main_code_init))%a)
        as Hentry_some.
      { pose proof (cmpt_code_size main_cmpt) as Hcode_size.
        rewrite main_code /vae_main_code length_app in Hcode_size.
        rewrite length_app.
        solve_addr+Hmain_imports_size Hcode_size. }
      iApply (vae_awkward_spec (swlayout := swl) (assertlayout := asl)
                _ _ _ _ _ _ _ _ _ W1);
        last iFrame "Hswitcher_static #"; auto.
      { eapply disjoint_from_shadow_not_in;
          first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
        apply withinBounds_true_iff; cbn in Hmain_data_size |- *; solve_addr+Hmain_data_size. }
      { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
      { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
      { exact (cmpt_pcc_base_not_heap main_cmpt). }
      { exact (cmpt_cgp_base_not_heap main_cmpt). } }
    iDestruct (seal_main_export (th := UserThread 0) W1 C main_awk
                with "Hseal_switcher Hot_switcher_main_awk") as "#Hinterp_main_awk"; [done| |].
    { intros ????? Heq; inversion Heq; subst.
      exact (cmpt_exp_tbl_disjoint_from_heap main_cmpt). }

    (* 6 - Close the world of C: its compartment becomes permanent, and the
       stack temporary, because main shares it with C; the exported entry
       [awkward] of main and the own export [g] of C are safe to import;
       the exports of C are safe to share. *)
    iMod (fw_close_adv_world (th := UserThread 0)
            _ _ _ 1 (fw_nth 1 (fw_cmpts vae_firmware) default_fw_cmpt) _
            HC_l W1 C Hok eq_refl eq_refl
            ltac:(cbn; repeat apply Forall_cons_2; try apply Forall_nil_2; lia) ltac:(done)
           with "Hswitcher_threads_C Hswitcher_static HC HC_pers Hstack [] Hthread_C Hworld_C")
      as "(Hworld_C & #Hinterp_stack_C & [#Hinterp_C _])".
    { iIntros "(_ & _ & #Hexports)". cbn [fc_name fc_imports fw_nth fw_cmpts vae_firmware].
      iSplit; first by iApply (fw_switcher_call_safe with "Hswitcher_threads_C").
      rewrite /fw_import_safe /fw_word_of /note.
      iSplit; last iSplit; last done.
      - (* main.awkward *)
        cbv [fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts vae_firmware
             fc_name fc_body tb_exports fe_name String.eqb Ascii.eqb Bool.eqb andb addr_off].
        fw_fold_cmpt main_cmpt.
        change (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry 0)
          with (cmpt_exp_tbl_pcc main_cmpt ^+ ExportTable_offset_entry vae_entry_awkward).
        fold main_awk.
        iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t' W1 ∅ C); last done.
        iExact "Hinterp_main_awk".
      - (* C.g, the second export of C *)
        cbv [fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts vae_firmware
             fc_name fc_body ub_exports ue_name String.eqb Ascii.eqb Bool.eqb andb addr_off].
        pose proof (fc_export_nargs_length _ _ _ (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl))
          as HC_len.
        cbv [fc_export_nargs fc_body fc_name fw_map ub_exports ue_nargs] in HC_len.
        fw_fold_cmpt C_cmpt.
        iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t'
                    W1 ∅ C); last done.
        iApply (adversary_export_interp (th := UserThread 0) (swlayout := swl) _ _ C_cmpt
                  vae_C_entry_g with "Hexports");
          first done.
        rewrite -HC_len /vae_C_entry_g /=; lia. }
    iEval (rewrite /fw_thread_csp) in "Hinterp_stack_C".
    cbn [fc_name fw_nth fw_cmpts vae_firmware]. rewrite HsbC.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt C_cmpt.

    (* 7 - We can apply the specification! *)
    iPoseProof (vae_init_spec (swlayout := swl) (assertlayout := asl) (C := C)
                  _ _ _ _ _ _ _ _ _ _ _ _ [] [] _
                 with "[ $Hassert $Hthread_C $Hswitcher $Hswitcher_static
                         $Hmain_imports $Hmain_code
                         $Hmain_etbl_pcc $Hmain_etbl_cgp $Hmain_etbl_awk
                         $Hawk_inv $Hrel_i
                         $Hna
                         $Hworld_C
                         $HPC $Hcgp $Hcsp $Hcra $Hregs
                         $Hcstk $Hinterp_stack_C
                         $Hinterp_C $Hentry_Cf
                        ]") as "Hspec"; eauto using fw_cleared_regs_dom.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { eapply disjoint_from_shadow_not_in;
        first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
      apply withinBounds_true_iff; cbn in Hmain_data_size |- *; solve_addr+Hmain_data_size. }
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { rewrite /W1.
      rewrite !std_update_multiple_loc_sta.
      by simplify_map_eq. }
    { done. }
    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End vae_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_vae := | C.
#[local] Instance CmptNames_vae_eq_dec : EqDecision CmptNames_vae.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_vae_finite : finite.Finite CmptNames_vae.
Proof.
  refine {| finite.enum := [C] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_vae_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_vae; |}.

(** The logical compartment of the adversary. *)
Definition vae_adv_C : @CmptName CmptNames_vae_CmptNameG := C.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem vae_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  vae_initial_state_ok flag σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (vae_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & C & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_vae_CmptNameG) #[]
            vae_firmware (vae_img sw asrt t0 main C));
    [| exact Hfw | exact Hstep].
  apply (vae_fw_obligations (C := vae_adv_C)).
Qed.
