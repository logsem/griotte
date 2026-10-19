From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy kvs_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  kvs kvs_main kvs_preamble kvs_main_spec kvs_spec_addOrUpdate_safe kvs_spec_read_safe kvs_spec_erase_safe.
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

Section kvs_obligations.
  Context {Σ : gFunctors}.
  Context {kvs_alloc_preg : gen_heapGpreS user_key_t kvs_user_map Σ}.
  Context {kvs_physical_user_preg : ghost_varG Σ kvs_physical_map}.
  Context {kvs_logical_user_preg : ghost_mapG Σ user_key_t (option LWord)}.
  Context {cname : CmptNameG} {B : CmptName}.
  Context `{MP : MachineParameters}.

  Definition kvsN : namespace := nroot .@ "kvs" .@ "code".

  (** The obligations of the trusted code of the KVS firmware: the thread
      runs safely from the export of [main], the untrusted compartment
      ["B"] being owned by the logical compartment [B]. *)
  Lemma kvs_fw_obligations (ot_kvs : OType) (key_main key_B : Z) :
    key_main ≠ key_B →
    fw_obligations Σ (kvs_firmware ot_kvs key_main key_B).
  Proof.
    intros Hkeys img σ ceriseg seal_storeg stsg relg cstackg Hok.
    pose proof Hok as (Hcmpts_ok & _ & _ & Hwf).

    (* 1 - The contents of the compartments, from the predicate *)
    cbv [kvs_firmware fw_cmpts fw_map big_and] in Hcmpts_ok.
    destruct Hcmpts_ok as (Hok_main & Hok_kvs & Hok_B).
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words hole_exports export_word
      fe_offset fe_nargs fe_posture] in Hok_main, Hok_kvs, Hok_B.
    destruct Hok_main as (main_imports & main_static_sealed & main_code & main_data & main_exp_tbl).
    destruct Hok_kvs as (kvs_imports & kvs_static_sealed & kvs_code & kvs_data & kvs_exp_tbl).
    destruct Hok_B as (B_imports & B_static_sealed & _ & _ & off_B & Hoff_B & B_exp_tbl).

    (* 2 - The layouts of the compartments, of the switcher and of the KVS *)
    pose proof (img_wf_cmpt_layout _ _ _ Hwf (list_elem_of_here _ _)) as Hmain_l.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf
                  (list_elem_of_further _ _ _ (list_elem_of_here _ _))) as Hkvs_l.
    pose proof (img_wf_cmpt_layout _ _ _ Hwf
                  (list_elem_of_further _ _ _
                     (list_elem_of_further _ _ _ (list_elem_of_here _ _)))) as HB_l.
    pose proof (cmpt_mem_layout img _ Hmain_l) as Hmem_main_eq.
    pose proof (cmpt_mem_layout img _ Hkvs_l) as Hmem_kvs_eq.
    pose proof (fw_adv_cmpt_init (E := ⊤) img _ HB_l) as HB_init.
    cbn [fc_name] in Hmem_main_eq, Hmem_kvs_eq, HB_init, Hmain_l, Hkvs_l, HB_l.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l) in *.
    set (kvs_cmpt := layout_cmpt_of (cmpt_of img "kvs") Hkvs_l) in *.
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l).
    change (image.cmpt_imports (cmpt_of img "main")) with (cmpt_imports main_cmpt) in main_imports.
    change (image.cmpt_static_sealed (cmpt_of img "main")) with (cmpt_static_sealed main_cmpt) in main_static_sealed.
    change (image.cmpt_code (cmpt_of img "main")) with (cmpt_code main_cmpt) in main_code.
    change (image.cmpt_data (cmpt_of img "main")) with (cmpt_data main_cmpt) in main_data.
    change (image.cmpt_exp_tbl_entries (cmpt_of img "main")) with (cmpt_exp_tbl_entries main_cmpt) in main_exp_tbl.
    change (image.cmpt_imports (cmpt_of img "kvs")) with (cmpt_imports kvs_cmpt) in kvs_imports.
    change (image.cmpt_static_sealed (cmpt_of img "kvs")) with (cmpt_static_sealed kvs_cmpt) in kvs_static_sealed.
    change (image.cmpt_code (cmpt_of img "kvs")) with (cmpt_code kvs_cmpt) in kvs_code.
    change (image.cmpt_data (cmpt_of img "kvs")) with (cmpt_data kvs_cmpt) in kvs_data.
    change (image.cmpt_exp_tbl_entries (cmpt_of img "kvs")) with (cmpt_exp_tbl_entries kvs_cmpt) in kvs_exp_tbl.

    assert (fw_threads (kvs_firmware ot_kvs key_main key_B) = [MkFwThread "main" 0 100 24])
      as Hthreads by reflexivity.
    pose proof (img_wf_switcher_layout _ _ _ _ Hthreads Hwf) as Hsw.
    pose proof (img_wf_trusted_stack_layout _ _ _ _ Hthreads Hwf) as Hts.
    pose proof (fw_switcher_layout_wf img _ _ Hts Hsw) as Hswl_wf.
    set (swl := fw_switcher_layout img) in *.

    pose (kvsl := @mkKvsLayout ot_kvs
            (cmpt_b_pcc kvs_cmpt) (cmpt_a_code kvs_cmpt) (cmpt_e_pcc kvs_cmpt)
            (cmpt_b_cgp kvs_cmpt) (cmpt_e_cgp kvs_cmpt)
            (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)).
    assert kvs_namespaces as kvs_namespacesg.
    { refine (Build_kvs_namespaces
                (kvsN .@ "Nkvs")
                (kvsN .@ "Nkvs_otype")
                (kvsN .@ "Nkvs_exp_tbl")
                _).
      split; try solve_ndisj.
    }
    assert (ot_kvs ≠ switcher.ot_switcher) as Hot_kvs_switcher.
    { destruct (img_wf_otypes _ _ Hwf) as [Hot_nodup _]. cbn in Hot_nodup.
      apply NoDup_cons in Hot_nodup as [Hot_notin _]. set_solver+Hot_notin. }
    assert (ot_kvs < ot_kvs ^+ 1)%ot as Hot_kvs_size.
    { destruct (img_wf_otypes _ _ Hwf) as [_ Hot_valid]. cbn in Hot_valid.
      rewrite Forall_cons Forall_singleton in Hot_valid. apply Hot_valid. }
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
        pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
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

    (* 3 - The export entries of the KVS, at the addresses of the KVS layout,
       and the export entry of B *)
    assert (cmpt_exp_tbl_entries_start kvs_cmpt = kvs_addOrUpdate_exp_tbl_addr ∧
            (cmpt_exp_tbl_entries_start kvs_cmpt ^+ 1)%a = kvs_read_exp_tbl_addr ∧
            (cmpt_exp_tbl_entries_start kvs_cmpt ^+ 2)%a = kvs_erase_exp_tbl_addr)
      as (Hkvs_a0 & Hkvs_a1 & Hkvs_a2).
    { pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H3.
      rewrite kvs_exp_tbl in H3.
      rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_read_exp_tbl_addr /kvs_erase_exp_tbl_addr
        /kvs_addOrUpdate_exp_tbl_off /kvs_read_exp_tbl_off /kvs_erase_exp_tbl_off.
      cbn in *. split_and!; solve_addr+H1 H2 H3. }
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_entries_start B_cmpt)).
    set (kvs_addOrUpdate := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
    set (kvs_addOrUpdate' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
    set (kvs_read := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
    set (kvs_read' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
    set (kvs_erase := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
    set (kvs_erase' := SCap true RO Local b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
    assert (cmpt_export_sb (cmpt_of img "kvs") 0 = kvs_addOrUpdate ∧
            cmpt_export_sb (cmpt_of img "kvs") 1 = kvs_read ∧
            cmpt_export_sb (cmpt_of img "kvs") 2 = kvs_erase ∧
            cmpt_export_sb (cmpt_of img "B") 0 = B_f) as (Hsb0 & Hsb1 & Hsb2 & HsbB).
    { rewrite /cmpt_export_sb /kvs_addOrUpdate /kvs_read /kvs_erase /B_f /=.
      rewrite -Hkvs_a0 -Hkvs_a1 -Hkvs_a2. done. }

    (* 4 - The main compartment: its imports, and its entry point *)
    assert (cmpt_imports main_cmpt =
              kvs_main_imports (cmpt_b_static_sealed main_cmpt)
                switcher.b_switcher switcher.e_switcher switcher.a_switcher_call
                switcher.ot_switcher
                (image.b_assert (img_asrt img)) (image.e_assert (img_asrt img)) B_f)
      as main_imports'.
    { rewrite main_imports /kvs_main_imports /KVS_addOrUpdate /KVS_read /KVS_erase
        /kvs_user_seal_key /kvs_user_seal_key_scap.
      rewrite -Hkvs_a0 -Hkvs_a1 -Hkvs_a2. done. }
    assert (image.cmpt_imports (cmpt_of img "B") =
              [WSentry FwdDisable true XSRW_ Local
                 switcher.b_switcher switcher.e_switcher switcher.a_switcher_call;
               WSealed switcher.ot_switcher kvs_addOrUpdate;
               WSealed switcher.ot_switcher kvs_read;
               WSealed switcher.ot_switcher kvs_erase;
               WSealed ot_kvs (kvs_user_seal_key_scap Global (cmpt_b_static_sealed B_cmpt))])
      as B_imports'.
    { rewrite B_imports /kvs_addOrUpdate /kvs_read /kvs_erase /kvs_user_seal_key_scap.
      rewrite -Hkvs_a0 -Hkvs_a1 -Hkvs_a2. done. }
    clear B_imports.
    assert (cmpt_b_pcc main_cmpt ^+ 7 = cmpt_a_code main_cmpt)%a as Hmain_entry.
    { pose proof (cmpt_import_size main_cmpt) as H.
      rewrite main_imports in H. cbn in H |- *. solve_addr+H. }

    (* 5 - The resources of the image *)
    iIntros "Hshared Hthread".
    iNamed "Hshared". iNamed "Hthread".
    iDestruct "Hswitcher" as "#Hswitcher".
    iDestruct "Hswitcher_static" as "#Hswitcher_static".
    iDestruct "Hseal_switcher" as "#Hseal_switcher".
    iDestruct "Hassert" as "#Hassert".
    iEval (cbv [kvs_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts" as "(Hcmpt_main & Hcmpt_kvs & Hcmpt_B & _)".
    iEval (rewrite Hmem_main_eq) in "Hcmpt_main".
    iEval (rewrite Hmem_kvs_eq) in "Hcmpt_kvs".
    iEval (cbv [fw_entries fw_flat_map fw_app fc_entries fc_export_nargs fw_imap fw_imap_from
                fw_map kvs_firmware fw_cmpts fc_body fc_name fe_nargs replicate]) in "Hentries".
    iEval (rewrite Hsb0 Hsb1 Hsb2 HsbB /=) in "Hentries".
    clear Hmem_main_eq Hmem_kvs_eq main_imports Hsb0 Hsb1 Hsb2.
    iDestruct "Hentries"
      as "(_ & [#Hentry_kvs_addOrUpdate #Hentry_kvs_addOrUpdate']
          & [#Hentry_kvs_read #Hentry_kvs_read'] & [#Hentry_kvs_erase #Hentry_kvs_erase']
          & [#Hentry_Bf #Hentry_Bf'] & _)".
    iEval (cbv [kvs_firmware fw_otypes]) in "Hotypes".
    iDestruct "Hotypes" as "[Hseal_store_kvs _]".
    iDestruct (big_sepS_elem_of _ _ B with "Hworlds") as "Hworld_B".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    set (W0 := fw_world0).
    assert (fw_entry_pc (kvs_firmware ot_kvs key_main key_B) img 0 =
              WCap true RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt)
                (cmpt_b_pcc main_cmpt ^+ 7)%a) as Hpc_eq by reflexivity.
    assert (fw_entry_cgp (kvs_firmware ot_kvs key_main key_B) img 0 =
              WCap true RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
                (cmpt_b_cgp main_cmpt)) as Hcgp_eq by reflexivity.
    iEval (rewrite Hpc_eq Hmain_entry) in "HPC".
    iEval (rewrite Hcgp_eq) in "Hcgp".
    clear Hpc_eq Hcgp_eq.

    (* 5.1 KVS compartment: initialise the KVS resources *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_kvs")
      as "(Hkvs_imports & Hkvs_code & Hkvs_data & _ & Hkvs_etbl_pcc & Hkvs_etbl_cgp & Hkvs_etbl_entries)".
    iEval (rewrite cmpt_code_codefrag) in "Hkvs_code".
    rewrite kvs_imports kvs_code.
    rewrite kvs_data.

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
        @kvs_main_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _
          kvsg _ _ _ B
      ) as Spec.

    (* 5.2 CMPT B *)
    iMod (HB_init with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & HB_static_sealed & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".
    iEval (rewrite B_static_sealed) in "HB_static_sealed".
    iDestruct (region_pointsto_single with "HB_static_sealed") as "(%&Ha_user_key_B&%Hv_B)";
      try (cbn in Hv_B); simplify_eq.
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H1.
      cbn in H1. rewrite B_static_sealed in H1; solve_addr+H1.
    }
    set (user_key_addr_B := cmpt_b_static_sealed B_cmpt).

    (* 5.3 CMPT MAIN *)
    iMod (initialise_compartment_pers (Σ := Σ) with "Hcmpt_main")
      as "(#Hmain_imports & #Hmain_code & Hmain_data & Hmain_static_sealed & _ & _ & _)".
    rewrite main_imports' main_code main_data main_static_sealed.

    (* 5.4 Export table of the KVS *)
    rewrite kvs_exp_tbl.
    iEval (rewrite /region_pointsto) in "Hkvs_etbl_entries".
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start kvs_cmpt)).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite (finz_seq_between_cons ((cmpt_exp_tbl_entries_start kvs_cmpt) ^+ _)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite (finz_seq_between_cons (((cmpt_exp_tbl_entries_start kvs_cmpt) ^+ _) ^+ _)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite big_sepL2_cons.
    rewrite big_sepL2_cons.
    rewrite big_sepL2_cons.
    iDestruct "Hkvs_etbl_entries"
      as "(Hkvs_etbl_entries_addOrUpdate & Hkvs_etbl_entries_read
          & Hkvs_etbl_entries_erase & _)".

    iMod (seal_store_update_alloc _ ( kvs_otype_propC ) with "Hseal_store_kvs") as "#Hsealed_pred_ot_kvs".

    iMod (pointsto_persist with "Hkvs_etbl_pcc") as "#Hkvs_etbl_pcc".
    iMod (pointsto_persist with "Hkvs_etbl_cgp") as "#Hkvs_etbl_cgp".
    iMod (pointsto_persist with "Hkvs_etbl_entries_addOrUpdate") as "#Hkvs_etbl_entries_addOrUpdate".
    iMod (pointsto_persist with "Hkvs_etbl_entries_read") as "#Hkvs_etbl_entries_read".
    iMod (pointsto_persist with "Hkvs_etbl_entries_erase") as "#Hkvs_etbl_entries_erase".

    replace ((cmpt_exp_tbl_entries_start kvs_cmpt ^+ 1) ^+ 1)%a with kvs_erase_exp_tbl_addr; cycle 1.
    { rewrite -Hkvs_a2. pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1. }
    rewrite Hkvs_a1 Hkvs_a0.

    (* 6 - Seal the exported entries of the KVS with [ot_switcher] in the
       world of B *)
    set ( adversary_imports :=
            ({[ lword_of_word (WSealable kvs_addOrUpdate) ; lword_of_word (WSealable kvs_addOrUpdate')]}
              ∪
            {[ lword_of_word (WSealable kvs_read) ; lword_of_word (WSealable kvs_read')]}
              ∪
            {[ lword_of_word (WSealable kvs_erase) ; lword_of_word (WSealable kvs_erase')]} : gset LWord)
        ).

    set (W1 := <o[ switcher.ot_switcher := adversary_imports]o> W0).

    iAssert (ot_switcher_prop W1 B (WSealable kvs_addOrUpdate)) as "#ot_switcher_kvs_addOrUpdate".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_addOrUpdate_entry_point_spec.
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_entries_addOrUpdate
        Hentry_kvs_addOrUpdate Hentry_kvs_addOrUpdate'".
    }

    iAssert (ot_switcher_prop W1 B (WSealable kvs_read)) as "#ot_switcher_kvs_read".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_read_entry_point_spec.
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_entries_read
        Hentry_kvs_read Hentry_kvs_read'".
    }

    iAssert (ot_switcher_prop W1 B (WSealable kvs_erase)) as "#ot_switcher_kvs_erase".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_erase_entry_point_spec.
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hkvs Hkvs_logical Hswitcher Hswitcher_static
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_entries_erase
        Hentry_kvs_erase Hentry_kvs_erase'".
    }

    assert (switcher.ot_switcher ∉ dom (seal_std W0)) as Hot_notin_W0.
    { by subst W0. }
    iMod
      (world_interp_salloc W0 B ot_switcher_propC switcher.ot_switcher adversary_imports
        with "[$Hseal_switcher] [ ] [ ] [$Hworld_B]")
      as "(Hworld_B & Hseal_kvs_f)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { rewrite {2}/adversary_imports.
      rewrite 2!normalise_sealed_words_union.
      rewrite !normalise_sealed_words_borrow.
      iEval (rewrite union_comm_L); iApply big_sepS_insert_2; first (iFrame "ot_switcher_kvs_erase").
      iEval (rewrite union_comm_L); iApply big_sepS_insert_2; first (iFrame "ot_switcher_kvs_read").
      rewrite big_sepS_singleton; iFrame "ot_switcher_kvs_addOrUpdate".
    }
    subst W1; set (W1 := <o[ switcher.ot_switcher := adversary_imports]o> W0).

    iAssert ( interp W1 B (WSealed switcher.ot_switcher kvs_addOrUpdate)) as "#Hinterp_kvs_addOrUpdate".
    { iEval (rewrite interp_unfold /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint, (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt).
    }
    iAssert ( interp W1 B (WSealed switcher.ot_switcher kvs_read)) as "#Hinterp_kvs_read".
    { iEval (rewrite interp_unfold /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint, (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt).
    }
    iAssert ( interp W1 B (WSealed switcher.ot_switcher kvs_erase)) as "#Hinterp_kvs_erase".
    { iEval (rewrite interp_unfold /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint, (cmpt_exp_tbl_disjoint_from_heap kvs_cmpt).
    }

    set ( kvs_user_key_B_sb := (kvs_user_seal_key_scap Global user_key_addr_B)).
    set ( kvs_user_key_B_sb' := borrow_sb kvs_user_key_B_sb).
    set ( adversary_kvs_keys := ( {[ lword_of_word (WSealable kvs_user_key_B_sb) ; lword_of_word (WSealable kvs_user_key_B_sb')]} : gset LWord)).
    set (W1' := <o[ ot_kvs := adversary_kvs_keys ]o> W1).

    iAssert (kvs_otype_prop W1' B (WSealable kvs_user_key_B_sb))
      with "[$Hkvs_logical_user_B $Ha_user_key_B HB_lukvs_frag]" as "ot_kvs_user_key_B".
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H.
      cbn in H; rewrite B_static_sealed in H.
      repeat iSplit.
      - iPureIntro; auto.
      - iPureIntro.
        subst user_key_addr_B.
        cbn; solve_addr+H.
      - iPureIntro. subst user_key_addr_B.
        eapply disjoint_from_shadow_not_in.
        + exact (cmpt_static_sealed_disjoint_from_shadow B_cmpt).
        + apply withinBounds_true_iff.
          cbn; solve_addr+H.
      - iApply (big_sepS_impl with "HB_lukvs_frag").
        iModIntro; iIntros (mk Hmk) "$".
    }

    assert (ot_kvs ∉ dom (seal_std W1)) as Hot_notin_W1.
    { subst W0 W1; rewrite dom_insert_L dom_empty_L; set_solver+Hot_kvs_switcher. }
    iMod
      (world_interp_salloc W1 B kvs_otype_propC ot_kvs adversary_kvs_keys
        with "[$Hsealed_pred_ot_kvs] [ ] [ ot_kvs_user_key_B ] [$Hworld_B]")
      as "(Hworld_B & Hseal_kvs_ku)"; first done.
    { iIntros (w); iApply mono_priv_ot_kvs. }
    { rewrite normalise_sealed_words_borrow.
      rewrite big_sepS_singleton; iFrame "ot_kvs_user_key_B".
    }
    subst W1' ; set (W1' := <o[ ot_kvs := adversary_kvs_keys ]o> W1).

    iAssert ( interp W1' B (WSealed ot_kvs kvs_user_key_B_sb)) as "#Hinterp_kvs_user_key_B".
    { iEval (rewrite interp_unfold /= /interp_sb).
      iSplit; first (iApply (sts_seals_std_weaken with "Hseal_kvs_ku") ; last set_solver+).
      iPureIntro; cbn.
      apply heap_cap_valid_disjoint.
      subst user_key_addr_B.
      replace (image.cmpt_b_static_sealed (cmpt_of img "B") ^+ 1)%a
        with (image.cmpt_e_static_sealed (cmpt_of img "B")).
      2: { pose proof (cmpt_static_sealed_size B_cmpt) as Hsize.
           cbn in Hsize; rewrite B_static_sealed in Hsize; cbn; solve_addr+Hsize. }
      apply (cmpt_static_sealed_disjoint_from_heap B_cmpt).
    }

    (* 7 - Close the world of B: its compartment becomes permanent, and the
       stack temporary. *)
    iEval (rewrite fw_thread_of_0) in "Hstack".
    iMod (fw_close_adv_world (kvs_firmware ot_kvs key_main key_B) img σ
            (fw_nth 2 (fw_cmpts (kvs_firmware ot_kvs key_main key_B)) default_fw_cmpt)
            "B" 1 HB_l W1' B
           with "Hswitcher Hswitcher_static Hseal_switcher HB_imports HB_code HB_data
                 HB_etbl_pcc HB_etbl_cgp HB_etbl_entries Hstack [] [] Hworld_B")
      as "(Hworld_B & #Hinterp_pcc_B & #Hinterp_cgp_B & #Hinterp_stack_B & #HB_exports)".
    { exact Hok. }
    { apply list_elem_of_further, list_elem_of_further, list_elem_of_here. }
    { done. }
    { intros a _. done. }
    { cbv [fc_entries fc_export_nargs fw_imap fw_imap_from fc_body fc_name replicate fw_nth
             fw_cmpts kvs_firmware].
      rewrite HsbB /=. iFrame "Hentry_Bf Hentry_Bf'". }
    { iIntros "_".
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (image.cmpt_imports (cmpt_of img "B")).
      rewrite B_imports'.
      set (Winter := std_update_compartment W1' B_cmpt).
      assert (related_sts_priv_world W1' Winter) as Hrelated_W1'_Winter.
      {
        apply related_sts_pub_priv_world.
        subst Winter.
        eapply std_update_compartment_pub; eauto ; apply Forall_true; intros; done.
      }
      assert (related_sts_priv_world W1 Winter) as Hrelated_W1_Winter.
      {
        eapply related_sts_priv_trans_world; eauto.
        apply related_sts_pub_priv_world.
        subst W1'.
        apply related_sts_pub_world_update_ot.
      }
      (* Switcher cross-compartment *)
      iApply big_sepL_cons; iSplitL.
      { assert (heap_authority_base
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
          iApply interp_switcher_call; iFrame "Hswitcher Hswitcher_static". } }

      (* KVS.addOrUpdate *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply interp_to_in_mem.
          iApply (interp_monotone_sd_same_heap W1 Winter with "[]").
          { subst Winter. by rewrite std_update_compartment_heap. }
          { iPureIntro; exact Hrelated_W1_Winter. }
          iFrame "Hinterp_kvs_addOrUpdate".
        * iIntros (W2 W3) "!> %Hrelated Hinterp".
          iEval (cbn) in "Hinterp".
          iApply (interp_in_mem_monotone_nl W2 W3 B RWL (WSealed switcher.ot_switcher kvs_addOrUpdate)
                    with "Hinterp"); [exact Hrelated|by unfold kvs_addOrUpdate; cbn].
      }
      (* KVS.read *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply interp_to_in_mem.
          iApply (interp_monotone_sd_same_heap W1 Winter with "[]").
          { subst Winter. by rewrite std_update_compartment_heap. }
          { iPureIntro; exact Hrelated_W1_Winter. }
          iFrame "Hinterp_kvs_read".
        * iIntros (W2 W3) "!> %Hrelated Hinterp".
          iEval (cbn) in "Hinterp".
          iApply (interp_in_mem_monotone_nl W2 W3 B RWL (WSealed switcher.ot_switcher kvs_read)
                    with "Hinterp"); [exact Hrelated|by unfold kvs_read; cbn].
      }
      (* KVS.erase *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply interp_to_in_mem.
          iApply (interp_monotone_sd_same_heap W1 Winter with "[]").
          { subst Winter. by rewrite std_update_compartment_heap. }
          { iPureIntro; exact Hrelated_W1_Winter. }
          iFrame "Hinterp_kvs_erase".
        * iIntros (W2 W3) "!> %Hrelated Hinterp".
          iEval (cbn) in "Hinterp".
          iApply (interp_in_mem_monotone_nl W2 W3 B RWL (WSealed switcher.ot_switcher kvs_erase)
                    with "Hinterp"); [exact Hrelated|by unfold kvs_erase; cbn].
      }
      (* KVS sealed user key *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply interp_to_in_mem.
          iApply (interp_monotone_sd_same_heap W1' Winter with "[]").
          { subst Winter. by rewrite std_update_compartment_heap. }
          { iPureIntro; exact Hrelated_W1'_Winter. }
          iFrame "Hinterp_kvs_user_key_B".
        * iIntros (W2 W3) "!> %Hrelated Hinterp".
          iEval (cbn) in "Hinterp".
          iApply (interp_in_mem_monotone_nl W2 W3 B RWL (WSealed ot_kvs kvs_user_key_B_sb)
                    with "Hinterp"); [exact Hrelated|by unfold kvs_user_key_B_sb; cbn].
      }
      done. }

    (* 8 - The exported entry point of B is safe to share *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_entries_start B_cmpt)).
    iAssert (interp _ B (WSealed switcher.ot_switcher B_f)) as "#Hinterp_B_f".
    { iApply (adversary_export_interp _ _ B_cmpt 0 with "HB_exports").
      - solve_addr.
      - change (cmpt_exp_tbl_entries B_cmpt) with (image.cmpt_exp_tbl_entries (cmpt_of img "B")).
        rewrite B_exp_tbl /=; lia.
    }

    iDestruct (big_sepS_elem_of _ _ 1%Z with "HK_lukvs_frag") as "HK_lukvs_1".
    { eapply is_uint16_in_kvs_all_map_keys; split; rewrite /UINT16_MIN /UINT16_MAX; lia. }

    (* 9 - The registers *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    assert (dom fw_cleared_regs = all_registers_s ∖ {[cgp; csp]}) as Hrmap_dom.
    { by rewrite /fw_cleared_regs dom_gset_to_gmap. }

    replace (cmpt_exp_tbl_cgp kvs_cmpt) with (b_kvs_exp_tbl ^+ 1)%a
      by (pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H; unfold kvsl; cbn in H |- *; solve_addr+H).

    (* 10 - We can apply the specification! *)
    pose proof (cmpt_static_sealed_base_not_heap main_cmpt) as Hstatic_key_nonheap.
    assert (is_heap_cap (WSealed switcher.ot_switcher B_f) = false) as HB_f_nonheap.
    { unfold B_f. apply sealed_cap_nonheap. exact (cmpt_exp_tbl_base_not_heap B_cmpt). }
    iPoseProof (Spec _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _
                  [] [] [] fw_switcherN
                 with "[ $Hassert $Hswitcher $Hswitcher_static $Hkvs_static $Hkvs $Hkvs_logical
                        $Hkvs_logical_user_K
                        $Hkvs_etbl_pcc $Hkvs_etbl_cgp $Hkvs_etbl_entries_addOrUpdate $Hkvs_etbl_entries_read
                        $Hna $HPC $Hcgp $Hcsp $Hregs
                        $Hmain_imports $Hmain_code $Hmain_data $Hmain_static_sealed
                        $HK_lukvs_1
                        $Hworld_B $Hcstk
                        $Hinterp_B_f $Hentry_Bf $Hinterp_stack_B
                        ]") as "Hspec"; eauto.
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
Theorem kvs_adequacy `{MP : MachineParameters} sw asrt t0 main kvs B ot_kvs key_main key_B
    (σ σ' : ExecConf) es :
  kvs_initial_state_ok sw asrt t0 main kvs B ot_kvs key_main key_B σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag_assert asrt = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (kvs_initial_state_ok_firmware_ok _ _ _ _ _ _ _ _ _ _ Hok) as [Hkeys Hfw].
  eapply (firmware_adequacy_closed (Cname := CmptNames_kvs_CmptNameG)
            #[gen_heapΣ user_key_t kvs_user_map; ghost_mapΣ user_key_t (option LWord);
              ghost_varΣ kvs_physical_map]
            (kvs_firmware ot_kvs key_main key_B) (kvs_img sw asrt t0 main kvs B));
    [| exact Hfw | exact Hstep].
  apply (kvs_fw_obligations (B := kvs_adv_name)), Hkeys.
Qed.
