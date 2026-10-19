From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy cmdc_firmware.
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
Set Mangle Names.

Section cmdc_adv_imports.
  Context
    {Σ : gFunctors}
    {ceriseg : ceriseG Σ} {sealsg : sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP : MachineParameters}.

  (** The imports of an adversary, the switcher call sentry only, are safe
      to store in its memory. *)
  Lemma cmdc_adv_imports_safe {swl : switcherLayout} {swl_wf : switcherLayoutWf}
      (W : WORLD) (C' : CmptName) :
    na_inv cerise_nais fw_switcherN switcher_inv -∗
    switcher_static -∗
    [∗ list] v ∈ lword_of_word <$>
      [WSentry FwdDisable true XSRW_ Local switcher.b_switcher switcher.e_switcher
         switcher.a_switcher_call],
      interp_in_memC (W, C', v) ∗ future_priv_mono C' interp_in_memC v.
  Proof.
    iIntros "#Hswitcher #Hswitcher_static".
    iSplit; last done.
    assert (heap_authority_base
      (WSentry FwdDisable true XSRW_ Local switcher.b_switcher
        switcher.e_switcher switcher.a_switcher_call) = None) as Hcall_nonheap.
    { destruct (heap_authority_base _) as [b|] eqn:Hauth; last done.
      apply heap_authority_base_heap_cap_base in Hauth.
      pose proof switcher_call_sentry_not_heap as Hnonheap.
      unfold is_heap_cap in Hnonheap; rewrite Hauth in Hnonheap; discriminate. }
    iEval (cbn); iSplit.
    { iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      iApply interp_switcher_call; iFrame "Hswitcher Hswitcher_static". }
    { iIntros "!>" (W2 W3 Hrel) "H".
      iEval (rewrite /interp_in_mem_pre /=).
      rewrite filter_heap_nonheap; last exact Hcall_nonheap.
      iApply interp_switcher_call; iFrame "Hswitcher Hswitcher_static". }
  Qed.
End cmdc_adv_imports.

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
    intros HBC img σ ceriseg seal_storeg stsg relg cstackg Hok.
    pose proof Hok as (Hcmpts_ok & _ & _ & Hwf).

    (* 1 - The contents of the compartments, from the predicate *)
    cbv [cmdc_firmware fw_cmpts fw_map big_and] in Hcmpts_ok.
    destruct Hcmpts_ok as (Hok_main & Hok_B & Hok_C).
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words hole_exports export_word
      fe_offset fe_nargs fe_posture] in Hok_main, Hok_B, Hok_C.
    destruct Hok_main as (main_imports & _ & main_code & main_data & _).
    destruct Hok_B as (B_imports & _ & _ & _ & off_B & Hoff_B & B_exp_tbl).
    destruct Hok_C as (C_imports & _ & _ & _ & off_C & Hoff_C & C_exp_tbl).

    (* 2 - The layouts of the compartments and of the switcher *)
    pose proof (img_wf_cmpt_layout _ _ _ Hwf (list_elem_of_here _ _)) as Hmain_l.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf
                  (list_elem_of_further _ _ _ (list_elem_of_here _ _))) as HB_l.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf
                  (list_elem_of_further _ _ _
                     (list_elem_of_further _ _ _ (list_elem_of_here _ _)))) as HC_l.
    pose proof (cmpt_mem_layout img _ Hmain_l) as Hmem_main_eq.
    pose proof (fw_adv_cmpt_init (E := ⊤) img _ HB_l) as HB_init.
    pose proof (fw_adv_cmpt_init (E := ⊤) img _ HC_l) as HC_init.
    cbn [fc_name] in Hmem_main_eq, HB_init, HC_init, Hmain_l, HB_l, HC_l.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l) in *.
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l).
    set (C_cmpt := layout_cmpt_of (cmpt_of img "C") HC_l).
    change (image.cmpt_imports (cmpt_of img "main")) with (cmpt_imports main_cmpt) in main_imports.
    change (image.cmpt_code (cmpt_of img "main")) with (cmpt_code main_cmpt) in main_code.
    change (image.cmpt_data (cmpt_of img "main")) with (cmpt_data main_cmpt) in main_data.

    assert (fw_threads cmdc_firmware = [MkFwThread "main" 0 100 24])
      as Hthreads by reflexivity.
    pose proof (img_wf_switcher_layout _ _ _ _ Hthreads Hwf) as Hsw.
    pose proof (img_wf_trusted_stack_layout _ _ _ _ Hthreads Hwf) as Hts.
    pose proof (fw_switcher_layout_wf img _ _ Hts Hsw) as Hswl_wf.
    set (swl := fw_switcher_layout img) in *.
    pose (asl := mkAssertLayout (image.b_assert (img_asrt img)) (image.e_assert (img_asrt img))
                   (image.flag_assert (img_asrt img))).

    (* The disjointness of main from the adversaries and from the switcher. *)
    assert (main_cmpt ## B_cmpt) as HmainB.
    { apply (img_wf_cmpts_disjoint cmdc_firmware img 0 1
               (fw_nth 0 (fw_cmpts cmdc_firmware) default_fw_cmpt)
               (fw_nth 1 (fw_cmpts cmdc_firmware) default_fw_cmpt)); done. }
    assert (main_cmpt ## C_cmpt) as HmainC.
    { apply (img_wf_cmpts_disjoint cmdc_firmware img 0 2
               (fw_nth 0 (fw_cmpts cmdc_firmware) default_fw_cmpt)
               (fw_nth 2 (fw_cmpts cmdc_firmware) default_fw_cmpt)); done. }
    pose proof (img_wf_switcher_cmpt_disjoint cmdc_firmware img _ _
                  (fw_nth 0 (fw_cmpts cmdc_firmware) default_fw_cmpt) _ _ Hmain_l Hts Hsw
                  Hthreads Hwf (list_elem_of_here _ _)) as Hsw_main.
    set (swc := layout_switcher_of (img_sw img) (thread_of img 0) _ _ Hts Hsw) in Hsw_main.

    (* 3 - The export entries of B and C *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_entries_start B_cmpt)).
    set (C_g := SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                  (cmpt_exp_tbl_entries_start C_cmpt)).
    assert (cmpt_export_sb (cmpt_of img "B") 0 = B_f ∧
            cmpt_export_sb (cmpt_of img "C") 0 = C_g) as (HsbB & HsbC).
    { by rewrite /cmpt_export_sb /B_f /C_g /=. }

    (* 4 - The main compartment: its imports, and its entry point *)
    assert (cmpt_imports main_cmpt = @cmdc_main_imports swl asl B_f C_g)
      as main_imports'.
    { rewrite main_imports /cmdc_main_imports. done. }
    assert (cmpt_b_pcc main_cmpt ^+ 4 = cmpt_a_code main_cmpt)%a as Hmain_entry.
    { pose proof (cmpt_import_size main_cmpt) as H.
      rewrite main_imports in H. cbn in H |- *. solve_addr+H. }

    (* 5 - The resources of the image *)
    iIntros "Hshared Hthread".
    iNamed "Hshared". iNamed "Hthread".
    iDestruct "Hswitcher" as "#Hswitcher".
    iDestruct "Hswitcher_static" as "#Hswitcher_static".
    iDestruct "Hseal_switcher" as "#Hseal_switcher".
    iDestruct "Hassert" as "#Hassert".
    iEval (cbv [cmdc_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "(Hcmpt_main & Hcmpt_B & Hcmpt_C & _)".
    iEval (rewrite Hmem_main_eq) in "Hcmpt_main".
    iEval (cbv [fw_entries fw_flat_map fw_app fc_entries fc_export_nargs fw_imap fw_imap_from
                fw_map cmdc_firmware fw_cmpts fc_body fc_name fe_nargs]) in "Hentries".
    iEval (rewrite HsbB HsbC /=) in "Hentries".
    clear Hmem_main_eq main_imports.
    iDestruct "Hentries" as "(_ & [#Hentry_Bf #Hentry_Bf'] & [#Hentry_Cg #Hentry_Cg'] & _)".
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hworld_B Hworlds]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iDestruct (big_sepS_delete _ _ C with "Hworlds") as "[Hworld_C _]".
    { apply elem_of_difference. split; last set_solver+HBC.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    assert (fw_entry_pc cmdc_firmware img 0 =
              WCap true RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt)
                (cmpt_b_pcc main_cmpt ^+ 4)%a) as Hpc_eq by reflexivity.
    assert (fw_entry_cgp cmdc_firmware img 0 =
              WCap true RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
                (cmpt_b_cgp main_cmpt)) as Hcgp_eq by reflexivity.
    iEval (rewrite Hpc_eq Hmain_entry) in "HPC".
    iEval (rewrite Hcgp_eq) in "Hcgp".
    iEval (rewrite /fw_thread_csp) in "Hcsp".
    iEval (rewrite fw_thread_of_0) in "Hstack".
    clear Hpc_eq Hcgp_eq.

    (* 5.1 Compartments B and C *)
    iMod (HB_init with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & _ & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".
    iMod (HC_init with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & _ & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".

    (* 5.2 Compartment main *)
    iMod (initialise_compartment_pers (Σ := Σ) with "Hcmpt_main")
      as "(#Hmain_imports & #Hmain_code & Hmain_data & _ & _ & _ & _)".
    rewrite main_imports' main_code main_data.

    (* 6 - Close the worlds of B and C: their compartments become permanent,
       and the stack is revoked, because main keeps it. *)
    iMod (fw_close_adv_world_revoked cmdc_firmware img σ
            (fw_nth 1 (fw_cmpts cmdc_firmware) default_fw_cmpt)
            "B" [cmdc_B_f_args] HB_l fw_world0 B
           with "Hswitcher Hswitcher_static Hseal_switcher HB_imports HB_code HB_data
                 HB_etbl_pcc HB_etbl_cgp HB_etbl_entries [] [] Hworld_B")
      as "(Hworld_B & #Hinterp_pcc_B & #Hinterp_cgp_B & Hrevoked_stack_B & #HB_exports)".
    { exact Hok. }
    { apply list_elem_of_further, list_elem_of_here. }
    { done. }
    { apply Forall_singleton. rewrite /cmdc_B_f_args. lia. }
    { intros a _. done. }
    { cbv [fc_entries fc_export_nargs fw_imap fw_imap_from fc_body fc_name fw_nth
             fw_cmpts cmdc_firmware].
      rewrite HsbB /=. iFrame "Hentry_Bf Hentry_Bf'". }
    { iIntros "_".
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (image.cmpt_imports (cmpt_of img "B")).
      rewrite B_imports.
      iApply (cmdc_adv_imports_safe with "Hswitcher Hswitcher_static"). }
    iMod (fw_close_adv_world_revoked cmdc_firmware img σ
            (fw_nth 2 (fw_cmpts cmdc_firmware) default_fw_cmpt)
            "C" [cmdc_C_g_args] HC_l fw_world0 C
           with "Hswitcher Hswitcher_static Hseal_switcher HC_imports HC_code HC_data
                 HC_etbl_pcc HC_etbl_cgp HC_etbl_entries [] [] Hworld_C")
      as "(Hworld_C & #Hinterp_pcc_C & #Hinterp_cgp_C & Hrevoked_stack_C & #HC_exports)".
    { exact Hok. }
    { apply list_elem_of_further, list_elem_of_further, list_elem_of_here. }
    { done. }
    { apply Forall_singleton. rewrite /cmdc_C_g_args. lia. }
    { intros a _. done. }
    { cbv [fc_entries fc_export_nargs fw_imap fw_imap_from fc_body fc_name fw_nth
             fw_cmpts cmdc_firmware].
      rewrite HsbC /=. iFrame "Hentry_Cg Hentry_Cg'". }
    { iIntros "_".
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (image.cmpt_imports (cmpt_of img "C")).
      rewrite C_imports.
      iApply (cmdc_adv_imports_safe with "Hswitcher Hswitcher_static"). }

    (* 7 - The exported entry points of B and C are safe to share *)
    iAssert (interp _ B (WSealed switcher.ot_switcher B_f)) as "#Hinterp_B".
    { iApply (adversary_export_interp _ _ B_cmpt 0 with "HB_exports").
      - solve_addr.
      - change (cmpt_exp_tbl_entries B_cmpt) with (image.cmpt_exp_tbl_entries (cmpt_of img "B")).
        rewrite B_exp_tbl /=; lia.
    }
    iAssert (interp _ C (WSealed switcher.ot_switcher C_g)) as "#Hinterp_C".
    { iApply (adversary_export_interp _ _ C_cmpt 0 with "HC_exports").
      - solve_addr.
      - change (cmpt_exp_tbl_entries C_cmpt) with (image.cmpt_exp_tbl_entries (cmpt_of img "C")).
        rewrite C_exp_tbl /=; lia.
    }

    (* 8 - The registers *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    assert (dom fw_cleared_regs = all_registers_s ∖ {[cgp; csp]}) as Hrmap_dom.
    { by rewrite /fw_cleared_regs dom_gset_to_gmap. }

    (* 9 - We can apply the specification! *)
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
    clear HB_init HC_init.
    iApply (cmdc_spec_full (swlayout := swl) (assertlayout := asl) (B := B) (C := C)
              _ _ _ _ _ _ _
              _ _ _ _ _
              [] [] _ (fun _ => True)%I fw_switcherN []
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
                    ]"); eauto.
    { intros r Hr. rewrite Hrmap_dom in Hr.
      rewrite /fw_cleared_regs lookup_gset_to_gmap option_guard_True //. }
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
Theorem cmdc_adequacy `{MP : MachineParameters} sw asrt t0 main B C
    (σ σ' : ExecConf) es :
  cmdc_initial_state_ok sw asrt t0 main B C σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag_assert asrt = Some (WInt 0).
Proof.
  intros Hok Hstep.
  pose proof (cmdc_initial_state_ok_firmware_ok _ _ _ _ _ _ _ Hok) as Hfw.
  eapply (firmware_adequacy_closed (Cname := CmptNames_CMDC_CmptNameG) #[]
            cmdc_firmware (cmdc_img sw asrt t0 main B C));
    [| exact Hfw | exact Hstep].
  apply (cmdc_fw_obligations (B := cmdc_adv_B) (C := cmdc_adv_C)). done.
Qed.
