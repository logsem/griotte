From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations
  kvs_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  kvs kvs_main kvs_preamble kvs_main_spec kvs_spec_addOrUpdate_safe kvs_spec_read_safe kvs_spec_erase_safe.
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

Section kvs_obligations.
  Context {Σ : gFunctors}.
  Context {kvs_alloc_preg : gen_heapGpreS user_key_t kvs_user_map Σ}.
  Context {kvs_physical_user_preg : ghost_varG Σ kvs_physical_map}.
  Context {kvs_logical_user_preg : ghost_mapG Σ user_key_t (option LWord)}.
  Context {cname : CmptNameG} {B : CmptName}.
  Context {seal_registry_preg : sealRegistryPreG LAddr Σ}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the KVS firmware: the thread
      runs safely from the export of [main], the untrusted compartment
      ["B"] being owned by the logical compartment [B]. *)
  Lemma kvs_fw_obligations (ot_kvs : OType) (key_main key_B : Z) :
    key_main ≠ key_B →
    fw_obligations Σ (kvs_firmware ot_kvs key_main key_B).
  Proof.
    intros Hkeys.
    pose (cthreads := {| cmpt_threads := λ _, {[UserThread 0]} |} : CmptThreads).
    assert (Hpin : ∀ C', cmpt_threads C' ⊆ {[UserThread 0]}) by (intros; reflexivity).
    assert (Hin : ∀ C', UserThread 0 ∈ cmpt_threads C') by (intros; rewrite /cthreads /=; set_solver).
    apply (fw_obligations_of Σ (cthreads := cthreads)); first reflexivity.
    intros img σ ceriseb seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    pose proof (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) as Hok_kvs.
    pose proof (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) as Hok_B.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts kvs_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb] in Hok_main, Hok_kvs, Hok_B.
    destruct Hok_main as (main_imports & main_static_sealed & main_code & main_data & _).
    destruct Hok_kvs as (kvs_imports & _ & kvs_code & kvs_data & _ & kvs_exp_tbl).
    destruct Hok_B as (B_imports & B_static_sealed & _).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as Hmain_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as Hkvs_l.
    pose proof (fw_cmpt_layout_at _ _ _ 2 _ Hok eq_refl) as HB_l.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 1 _ Hkvs_l eq_refl) as Hsw_kvs.
    cbn [fc_name] in Hmain_l, Hkvs_l, HB_l, Hsw_kvs.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l).
    set (kvs_cmpt := layout_cmpt_of (cmpt_of img "kvs") Hkvs_l).
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l).
    fw_fold_cmpt main_cmpt. fw_fold_cmpt kvs_cmpt. fw_fold_cmpt B_cmpt.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    set (swl := fw_switcher_layout img) in *.

    (* 2 - The layout of the KVS *)
    pose (kvsl := @mkKvsLayout ot_kvs
            (cmpt_b_pcc kvs_cmpt) (cmpt_a_code kvs_cmpt) (cmpt_e_pcc kvs_cmpt)
            (cmpt_b_cgp kvs_cmpt) (cmpt_e_cgp kvs_cmpt)
            (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)).
    assert (ot_kvs ≠ switcher.ot_switcher) as Hot_kvs_switcher.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [Hot_nodup _].
      cbn in Hot_nodup. apply NoDup_cons in Hot_nodup as [Hot_notin _]. set_solver+Hot_notin. }
    assert (ot_kvs < ot_kvs ^+ 1)%ot as Hot_kvs_size.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [_ Hot_valid].
      cbn in Hot_valid. rewrite Forall_cons Forall_singleton in Hot_valid. apply Hot_valid. }
    assert kvsLayoutWf as kvsLayoutWfg.
    { refine (mkKvsLayoutWf _ _ _ _ _ _ _ _ _ _ _ _); cbn.
      - exact Hot_kvs_size.
      - pose proof (cmpt_import_size kvs_cmpt) as H.
        by rewrite kvs_imports in H.
      - pose proof (cmpt_code_size kvs_cmpt) as H.
        by rewrite kvs_code in H.
      - pose proof (cmpt_data_size kvs_cmpt) as H.
        by rewrite kvs_data in H.
      - pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
        pose proof (cmpt_exp_tbl_header_size kvs_cmpt) as H2.
        pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H3.
        rewrite kvs_exp_tbl in H3.
        rewrite /length_kvs_exports_tbl /kvs_nb_exports.
        cbn in *.
        solve_addr+H1 H2 H3.
      - exact (cmpt_cgp_disjoint_from_shadow kvs_cmpt).
      - exact (cmpt_pcc_disjoint_from_shadow kvs_cmpt).
      - exact (cmpt_exp_tbl_disjoint_from_shadow kvs_cmpt).
      - exact (cmpt_pcc_base_not_heap kvs_cmpt).
      - exact (cmpt_cgp_base_not_heap kvs_cmpt).
      - exact (cmpt_exp_tbl_base_not_heap kvs_cmpt).
    }
    (* The KVS's code is outside the switcher's: its faults are not resumed by
       the exception path *)
    assert (cmpt_b_pcc kvs_cmpt ≠ switcher.b_switcher) as Hkvs_switcher.
    { apply (switcher_cmpt_disjoint_pcc_b kvs_cmpt _ Hsw_kvs).
      pose proof (cmpt_import_size kvs_cmpt) as Himports_size.
      pose proof (cmpt_code_size kvs_cmpt) as Hcode_size.
      rewrite kvs_imports in Himports_size; cbn [length] in Himports_size.
      solve_addr+Himports_size Hcode_size. }

    (* 3 - The export entries of the KVS, at the addresses of the KVS layout,
       and the export entry of B *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry kvs_B_entry_f)).
    set (kvs_addOrUpdate := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
    set (kvs_addOrUpdate' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
    set (kvs_read := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
    set (kvs_read' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
    set (kvs_erase := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
    set (kvs_erase' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
    assert (cmpt_export_sb (cmpt_of img "B") kvs_B_entry_f = B_f) as HsbB.
    { rewrite /cmpt_export_sb /B_f /=. done. }

    (* 4 - The imports of main and B *)
    assert (cmpt_imports main_cmpt =
              kvs_main_imports (cmpt_b_static_sealed main_cmpt)
                switcher.b_switcher switcher.e_switcher switcher.a_switcher_call
                switcher.ot_switcher
                (image.b_assert (img_asrt img)) (image.e_assert (img_asrt img)) B_f)
      as main_imports'.
    { rewrite main_imports /kvs_main_imports /KVS_addOrUpdate /KVS_read /KVS_erase
        /kvs_user_seal_key /kvs_user_seal_key_scap.
      done. }
    assert (cmpt_imports B_cmpt =
              [Sentry FwdDisable XSRW_ Local
                 switcher.b_switcher switcher.e_switcher switcher.a_switcher_call;
               WSealed switcher.ot_switcher kvs_addOrUpdate;
               WSealed switcher.ot_switcher kvs_read;
               WSealed switcher.ot_switcher kvs_erase;
               WSealed ot_kvs (kvs_user_seal_key_scap Global (cmpt_b_static_sealed B_cmpt))])
      as B_imports'.
    { rewrite B_imports /kvs_addOrUpdate /kvs_read /kvs_erase /kvs_user_seal_key_scap.
      done. }
    clear B_imports.

    (* 5 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) B (Hin B)) as "#Hthread_B".
    iDestruct (switcher_family_pinned (UserThread 0) B (Hpin B) with "Hswitcher Hswitcher_static")
      as "#Hfamily_B".
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack (kvs_firmware ot_kvs key_main key_B) 0) with 6 in Hentry_min_stack.
    assert (∀ b e : Z, b + Z.of_nat 6 + StackEntry_reserved_space <= e →
              b + SpillSlot_size + 2 * StackEntry_reserved_space <= e)%Z as Hmin_bridge
      by (rewrite /SpillSlot_size /StackEntry_reserved_space; lia).
    apply Hmin_bridge in Hentry_min_stack; clear Hmin_bridge.
    iEval (cbv [kvs_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts"
      as "((Hmain & Hmain_static_sealed & _) & (Hkvs & _ & #Hkvs_pers) &
           (HB & HB_static_sealed & #HB_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt (kvs_firmware ot_kvs key_main key_B) img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    iDestruct "Hkvs" as "(Hkvs_imports & Hkvs_code & Hkvs_data)".
    iDestruct "Hkvs_pers" as "(Hkvs_etbl_pcc & Hkvs_etbl_cgp & Hkvs_etbl_nh & Hkvs_etbl_entries)".
    iEval (cbn [fw_handler_res fc_body tb_error_handler tb_error_handler_stackless]) in "Hkvs_etbl_nh".
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ kvs_B_entry_f 0
                 (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".
    iEval (cbv [kvs_firmware fw_otypes]) in "Hotypes".
    iDestruct "Hotypes" as "[Hseal_store_kvs _]".
    iDestruct (big_sepS_elem_of _ _ B with "Hworlds") as "Hworld_B".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    set (W0 := fw_world0).
    cbn [fc_name]. rewrite /fw_cmpt_static_res.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt kvs_cmpt. fw_fold_cmpt B_cmpt.
    rewrite main_imports' main_code main_data main_static_sealed.
    clear main_imports.

    (* 5.1 KVS compartment: initialise the KVS resources *)
    iEval (rewrite cmpt_code_codefrag) in "Hkvs_code".
    rewrite kvs_imports kvs_code kvs_data.
    iMod (user_kvs_init {[ key_main ; key_B ]}
           with "[$Hkvs_imports $Hkvs_code $Hkvs_data]")
      as (γpkvs kvs_logical_heapg γf) "(#Hkvs_static & #Hkvs & #Hkvs_logical & Hlukvs)".
    pose kvsphysicalg := Build_KvsPhysicalG Σ kvs_physical_user_preg γpkvs.
    pose kvslogicalg := Build_KvsLogicalG Σ kvs_logical_heapg.
    pose kvsuserg := Build_KvsUserG Σ kvs_logical_user_preg γf.
    pose kvsg := KvsG Σ kvsphysicalg kvslogicalg kvsuserg.

    iDestruct (big_sepS_delete _ _ key_main with "Hlukvs")
      as "[ [Hkvs_logical_user_K HK_lukvs_frag] Hlukvs]"; first by set_solver+.
    iDestruct (big_sepS_delete _ _ key_B with "Hlukvs")
      as "[ [Hkvs_logical_user_B HB_lukvs_frag] _]"; first by set_solver+Hkeys.

    pose proof (
        kvs_main_spec (th := UserThread 0) (kvsg := kvsg) (B := B)
      ) as Spec.

    (* 5.2 The static sealed key of B *)
    iEval (rewrite B_static_sealed) in "HB_static_sealed".
    iDestruct (region_pointsto_single with "HB_static_sealed") as "(%&Ha_user_key_B&%Hv_B)";
      try (cbn in Hv_B); simplify_eq.
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H1.
      rewrite B_static_sealed in H1; solve_addr+H1.
    }
    set (user_key_addr_B := cmpt_b_static_sealed B_cmpt).

    (* 5.3 Export table of the KVS *)
    rewrite kvs_exp_tbl.
    iEval (rewrite !big_sepL_cons) in "Hkvs_etbl_entries".
    iDestruct "Hkvs_etbl_entries"
      as "(Hkvs_etbl_entries_addOrUpdate & Hkvs_etbl_entries_read
          & Hkvs_etbl_entries_erase & _)".

    (* 5.4 The registry of the sealed user keys: B's key, valid in B *)
    iMod (ghost_map_alloc (∅ : gmap LAddr CmptName)) as (γreg) "[Hreg_auth _]".
    pose seal_registryg :=
      {| seal_registry_inG := seal_registry_preg; seal_registry_name := λ _, γreg |}.
    iMod (registry_auth_insert (seal_registryg := seal_registryg)
            ot_kvs ∅ (LNonHeap user_key_addr_B) B with "Hreg_auth")
      as "[Hreg_auth #Hel_B]"; first done.
    iMod (registry_alloc (th := UserThread 0) (seal_registryg := seal_registryg) Nkvs_otype ot_kvs
            (kvs_sealed_obj_resources (th := UserThread 0)) _ _
           with "Hreg_auth [Ha_user_key_B Hkvs_logical_user_B HB_lukvs_frag]") as "#Hreg".
    { iApply bi.later_intro.
      rewrite insert_empty big_sepM_singleton /kvs_sealed_obj_resources.
      iExists _, user_key_addr_B. iFrame "Ha_user_key_B Hkvs_logical_user_B".
      iSplit; first done.
      iApply (big_sepS_impl with "HB_lukvs_frag").
      iModIntro; iIntros (mk Hmk) "Hmk". rewrite /safe_kvs_pointsto. iRight. iExact "Hmk". }
    iAssert (kvs_otype_registry (th := UserThread 0) (seal_registryg := seal_registryg))
      as "#Hregistry".
    { iExact "Hreg". }

    iMod (seal_store_update_alloc _ SealGlobal
            (kvs_otype_propC (seal_registryg := seal_registryg))
           with "Hseal_store_kvs")
      as "#Hsealed_pred_ot_kvs".

    (* 6 - The exported entries of the KVS, sealed with [ot_switcher], are
       valid in the world of B *)
    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_addOrUpdate))
      as "#ot_switcher_kvs_addOrUpdate".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply kvs_addOrUpdate_entry_point_spec; [exact Hkvs_switcher | exact (Hpin B) |].
      iFrame "Hsealed_pred_ot_kvs Hregistry Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_nh Hkvs_etbl_entries_addOrUpdate".
    }

    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_read))
      as "#ot_switcher_kvs_read".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply kvs_read_entry_point_spec; [exact Hkvs_switcher | exact (Hpin B) |].
      iFrame "Hsealed_pred_ot_kvs Hregistry Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_nh Hkvs_etbl_entries_read".
    }

    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_erase))
      as "#ot_switcher_kvs_erase".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply kvs_erase_entry_point_spec; [exact Hkvs_switcher | exact (Hpin B) |].
      iFrame "Hsealed_pred_ot_kvs Hregistry Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_nh Hkvs_etbl_entries_erase".
    }

    iDestruct (seal_main_export (th := UserThread 0) W0 B kvs_addOrUpdate
                with "Hseal_switcher ot_switcher_kvs_addOrUpdate") as "#Hinterp_kvs_addOrUpdate".
    { done. }
    { intros ????? [= <- <- <- <- <-]. apply (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt). }
    iDestruct (seal_main_export (th := UserThread 0) W0 B kvs_read
                with "Hseal_switcher ot_switcher_kvs_read") as "#Hinterp_kvs_read".
    { done. }
    { intros ????? [= <- <- <- <- <-]. apply (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt). }
    iDestruct (seal_main_export (th := UserThread 0) W0 B kvs_erase
                with "Hseal_switcher ot_switcher_kvs_erase") as "#Hinterp_kvs_erase".
    { done. }
    { intros ????? [= <- <- <- <- <-]. apply (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt). }

    (* The sealed user key of B, recorded in the registry for B *)
    set ( kvs_user_key_B_sb := (kvs_user_seal_key_scap Global user_key_addr_B)).
    assert (static_word_shape (lword_of_word (WSealable kvs_user_key_B_sb))) as Hshape_B.
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H.
      rewrite B_static_sealed in H.
      apply static_word_shape_intro.
      - subst user_key_addr_B.
        cbn in H |- *; solve_addr+H.
      - subst user_key_addr_B.
        eapply disjoint_from_shadow_not_in.
        + exact (cmpt_static_sealed_disjoint_from_shadow B_cmpt).
        + apply withinBounds_true_iff.
          cbn in H |- *; solve_addr+H.
    }
    iAssert (kvs_otype_propC (seal_registryg := seal_registryg)
               (UserThread 0, W0, B, lword_of_word (WSealable kvs_user_key_B_sb)))
      as "#ot_kvs_user_key_B".
    { iApply (registry_propC_intro (seal_registryg := seal_registryg)
                ot_kvs sealed_cap_key static_word_shape (UserThread 0) W0 B
                (lword_of_word (WSealable kvs_user_key_B_sb))
                (LNonHeap user_key_addr_B) eq_refl Hshape_B
               with "Hel_B"). }
    iAssert (interp (th := UserThread 0) W0 B (WSealed ot_kvs kvs_user_key_B_sb))
      as "#Hinterp_kvs_user_key_B".
    { iApply (interp_sealed_of_seals (th := UserThread 0) W0 B ot_kvs
                (kvs_otype_propC (seal_registryg := seal_registryg)) kvs_user_key_B_sb
               with "Hsealed_pred_ot_kvs []").
      { intros ????? [= <- <- <- <- <-].
        subst user_key_addr_B.
        replace (cmpt_b_static_sealed B_cmpt ^+ 1)%a with (cmpt_e_static_sealed B_cmpt).
        2: { pose proof (cmpt_static_sealed_size B_cmpt) as Hsize.
             rewrite B_static_sealed in Hsize; cbn in Hsize |- *; solve_addr+Hsize. }
        apply (cmpt_static_sealed_disjoint_from_heap B_cmpt). }
      { iApply kvs_otype_kind_ok. }
      assert (lforce_global (lword_of_word (WSealable kvs_user_key_B_sb))
              = lword_of_word (WSealable kvs_user_key_B_sb)) as Heq by reflexivity.
      rewrite Heq.
      iApply bi.later_intro. iExact "ot_kvs_user_key_B". }

    (* 7 - Close the world of B: its compartment becomes Global regions, and
       the stack temporary; its export is safe to share. *)
    iMod (fw_close_adv_world (th := UserThread 0) _ _ _ 2
            (fw_nth 2 (fw_cmpts (kvs_firmware ot_kvs key_main key_B)) default_fw_cmpt) _
            HB_l W0 B Hok eq_refl eq_refl ltac:(apply Forall_singleton; cbn; lia) ltac:(done)
           with "Hfamily_B Hswitcher_static HB HB_pers Hstack [] Hthread_B Hworld_B")
      as "(Hworld_B & #Hinterp_stack_B & [#Hinterp_B_f _])".
    { iIntros "_".
      rewrite -(fw_imports_safe_words _ _
                  (fw_nth 2 (fw_cmpts (kvs_firmware ot_kvs key_main key_B)) default_fw_cmpt)
                  _ (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl)).
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (cmpt_imports B_cmpt).
      rewrite B_imports'.
      (* Switcher cross-compartment *)
      iApply big_sepL_cons; iSplitL.
      { iApply (fw_switcher_call_safe _ _ _ (cmpt_of img "B") with "Hfamily_B Hswitcher_static").
        exact Hok. }
      (* The KVS entries and the sealed user key are Global: valid in every world *)
      iApply big_sepL_cons; iSplitL.
      { iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t' W0 ∅ B); last done.
        iExact "Hinterp_kvs_addOrUpdate". }
      iApply big_sepL_cons; iSplitL.
      { iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t' W0 ∅ B); last done.
        iExact "Hinterp_kvs_read". }
      iApply big_sepL_cons; iSplitL.
      { iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t' W0 ∅ B); last done.
        iExact "Hinterp_kvs_erase". }
      iApply big_sepL_cons; iSplitL.
      { iEval (rewrite /interp_cmpt_threads /=). iIntros "!>" (t') "_".
        rewrite -(interp_global_thread_world_free (UserThread 0) t' W0 ∅ B); last done.
        iExact "Hinterp_kvs_user_key_B". }
      done. }

    cbn [fc_name fw_nth fw_cmpts kvs_firmware]. rewrite HsbB.
    fw_fold_cmpt B_cmpt.
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry kvs_B_entry_f)).

    iDestruct (big_sepS_elem_of _ _ 1%Z with "HK_lukvs_frag") as "HK_lukvs_1".
    { eapply is_uint16_in_kvs_all_map_keys; split; rewrite /UINT16_MIN /UINT16_MAX; lia. }

    (* 8 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    replace (cmpt_exp_tbl_cgp kvs_cmpt) with (b_kvs_exp_tbl ^+ ExportTable_offset_cgp)
      by (pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H; unfold kvsl; cbn in H |- *; solve_addr+H).
    pose proof (cmpt_static_sealed_base_not_heap main_cmpt) as Hstatic_key_nonheap.
    assert (is_heap_cap (WSealed switcher.ot_switcher B_f) = false) as HB_f_nonheap.
    { unfold B_f. apply sealed_cap_nonheap. exact (cmpt_exp_tbl_base_not_heap B_cmpt). }
    iPoseProof (Spec _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _
                  [] [] _
                 with "[ $Hassert $Hthread_B $Hswitcher $Hswitcher_static $Hkvs_static $Hkvs $Hkvs_logical
                        $Hkvs_logical_user_K
                        $Hkvs_etbl_pcc $Hkvs_etbl_cgp $Hkvs_etbl_entries_addOrUpdate $Hkvs_etbl_entries_read
                        $Hna $HPC $Hcgp $Hcsp $Hcra $Hregs
                        $Hmain_imports $Hmain_code $Hmain_data $Hmain_static_sealed
                        $HK_lukvs_1
                        $Hworld_B $Hcstk
                        $Hinterp_B_f $Hentry_Bf $Hinterp_stack_B
                        ]") as "Hspec"; eauto using fw_cleared_regs_dom.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { eapply disjoint_from_shadow_not_in.
      - exact (cmpt_static_sealed_disjoint_from_shadow main_cmpt).
      - apply withinBounds_true_iff.
        pose proof (cmpt_static_sealed_size main_cmpt) as Hsize.
        rewrite main_static_sealed in Hsize; cbn in Hsize |- *; solve_addr+Hsize.
    }
    { intros r Hr. by apply elem_of_dom. }
    { pose proof (cmpt_static_sealed_size main_cmpt) as Hsize.
      by rewrite main_static_sealed in Hsize.
    }
    { done. }

    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End kvs_obligations.

Inductive CmptNames_kvs := | B .
#[local] Instance CmptNames_kvs_eq_dec : EqDecision CmptNames_kvs.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
#[local] Instance CmptNames_kvs_finite : finite.Finite CmptNames_kvs.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_kvs_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_kvs; |}.


(** The logical compartment of the adversary. *)
Definition kvs_adv_name : @CmptName CmptNames_kvs_CmptNameG := B.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem kvs_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  kvs_initial_state_ok flag σ →
  rtc erased_step ([Exec], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (kvs_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & kvs & B & ot_kvs & key_main & key_B & <- & Hkeys & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_kvs_CmptNameG)
            #[gen_heapΣ user_key_t kvs_user_map; ghost_mapΣ user_key_t (option LWord);
              ghost_varΣ kvs_physical_map; @seal_registryΣ CmptNames_kvs_CmptNameG LAddr _ _]
            (kvs_firmware ot_kvs key_main key_B) (kvs_img sw asrt t0 main kvs B));
    [| exact Hfw | exact Hstep].
  apply (kvs_fw_obligations (B := kvs_adv_name)), Hkeys.
Qed.
