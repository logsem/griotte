From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy_obligations firmware_obligations
  firmware_thread_obligations kvs_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  kvs kvs_main kvs_preamble kvs_main_spec kvs_spec_addOrUpdate_safe kvs_spec_read_safe kvs_spec_erase_safe.
From griotte Require Import assert_spec logrel.
From griotte Require Import locks locks_spec.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  world_interp_revocation world_interp_allocation world_interp_allocation_compartments.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common_obligations.
From griotte Require Import allocator_resources heap_region.

Section kvs_obligations.
  Context {Σ : gFunctors}.
  Context {kvs_alloc_preg : gen_heapGpreS user_key_t kvs_user_map Σ}.
  Context {kvs_physical_user_preg : ghost_varG Σ kvs_physical_map}.
  Context {kvs_logical_user_preg : ghost_mapG Σ user_key_t (option LWord)}.
  Context {cname : CmptNameG} {B Sched : CmptName}.
  Context `{MP : MachineParameters}.

  (** The threads of the compartments: the context-switch thread in the
      scheduler's [Sched]; both user threads in [B], in shared mode. *)
  Definition kvs_cthreads : CmptThreads := {|
    cmpt_threads := λ X,
      if decide (X = Sched) then {[CtxSwitch]} else {[UserThread 0; UserThread 1]};
    cmpt_shared := λ X, if decide (X = Sched) then false else true;
    cmpt_threads_sep := ltac:(intros X t; cbv beta; repeat case_decide; set_solver) |}.

  (** The obligations of the trusted code of the KVS firmware: the thread 0
      runs safely from the export [entry] of [main], the thread 1 from the
      export [adv] of the untrusted compartment ["B"], owned by the logical
      compartment [B], which both threads run; both call the KVS service,
      whose table and users' maps are under a lock of the critical-section
      pool; the scheduler runs in [Sched]. *)
  Lemma kvs_fw_obligations (ot_kvs : OType) (key_main key_B : Z) :
    key_main ≠ key_B →
    B ≠ Sched →
    fw_obligations Σ (kvs_firmware ot_kvs key_main key_B).
  Proof.
    intros Hkeys HBS.
    exists kvs_cthreads, Sched.
    split; first by (cbn; rewrite decide_True; [set_solver | done]).
    split; first by (cbn; rewrite decide_True).
    set (cthreads := kvs_cthreads).
    assert (@cmpt_threads _ cthreads B = {[UserThread 0; UserThread 1]}) as HB_threads.
    { rewrite /cthreads /kvs_cthreads /=. by rewrite decide_False. }
    assert (@cmpt_shared _ cthreads B = true) as HB_shared.
    { rewrite /cthreads /kvs_cthreads /=. by rewrite decide_False. }
    assert (UserThread 0 ∈ @cmpt_threads _ cthreads B) as Hin0_B.
    { rewrite HB_threads. set_solver. }
    assert (UserThread 1 ∈ @cmpt_threads _ cthreads B) as Hin1_B.
    { rewrite HB_threads. set_solver. }
    assert (fw_threads (kvs_firmware ot_kvs key_main key_B) =
              [fw_thread_of (kvs_firmware ot_kvs key_main key_B) 0;
               fw_thread_of (kvs_firmware ot_kvs key_main key_B) 1])
      as Hthreads by reflexivity.
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
    set (swc := fw_switcher_cmpt _ _ _ Hok) in *.
    set (swl := fw_switcher_layout img) in *.

    (* 2 - The layout of the lock library, imported by the KVS: outside
       the heap *)
    set (lkl := fw_locks_layout img).
    assert (fw_uses_try_lock (kvs_firmware ot_kvs key_main key_B) ≠ []) as Huse_lock
      by (rewrite /fw_uses_try_lock /=; done).
    assert (is_heap_address (@b_locks lkl) = false) as Hlocks_heap.
    { pose proof Hok as (_ & _ & _ & Hwf_img).
      exact (proj1 (ill_not_heap _ (img_wf_locks_layout _ _ Hwf_img Huse_lock))). }

    (* 3 - The layout of the KVS *)
    pose (kvsl := @mkKvsLayout ot_kvs
            (cmpt_b_pcc kvs_cmpt) (cmpt_a_code kvs_cmpt) (cmpt_e_pcc kvs_cmpt)
            (cmpt_b_cgp kvs_cmpt) (cmpt_e_cgp kvs_cmpt)
            (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)).
    assert (ot_kvs ≠ switcher.ot_switcher) as Hot_kvs_switcher.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [Hot_nodup _].
      cbn in Hot_nodup. apply NoDup_cons in Hot_nodup as [Hot_notin _]. set_solver+Hot_notin. }
    assert (ot_kvs < ot_kvs ^+ 1)%ot as Hot_kvs_size.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [_ Hot_valid].
      cbn in Hot_valid. rewrite Forall_cons Forall_cons Forall_singleton in Hot_valid. apply Hot_valid. }
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
    (* The lock word, in the data of the KVS, is outside the heap *)
    assert (is_heap_address (@kvs_lock_addr kvsl) = false) as Hlock_heap.
    { pose proof (cmpt_data_size kvs_cmpt) as Hsize.
      rewrite kvs_data in Hsize.
      assert (length kvs.kvs_data = 49) as Hlen by reflexivity.
      rewrite Hlen in Hsize.
      eapply disjoint_from_heap_not_in;
        first exact (proj2 (cmpt_cgp_not_heap_range kvs_cmpt)).
      apply withinBounds_true_iff.
      rewrite /kvs_lock_addr /KVS_LOCK_OFFSET.
      cbn in Hsize |- *. solve_addr+Hsize. }

    (* 4 - The export entries of the KVS, at the addresses of the KVS layout,
       and the export entry of B *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry kvs_B_entry_f)).
    set (kvs_addOrUpdate := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr).
    set (kvs_read := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_read_exp_tbl_addr).
    set (kvs_erase := SCap true RO Global b_kvs_exp_tbl e_kvs_exp_tbl kvs_erase_exp_tbl_addr).
    assert (cmpt_export_sb (cmpt_of img "B") kvs_B_entry_f = B_f) as HsbB.
    { rewrite /cmpt_export_sb /B_f /=. done. }

    (* 5 - The imports of main and B *)
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

    (* 6 - The shared resources *)
    iIntros "Hshared". iNamed "Hshared".
    iDestruct "Hswitcher_static" as "#Hswitcher_static".
    iDestruct (fw_switcher_threads (cthreads := cthreads) (kvs_firmware ot_kvs key_main key_B) img B
                with "Hswitcher_static Hswitcher_tstacks")
      as "#Hswitcher_threads_B".
    { intros t Ht. rewrite HB_threads in Ht.
      apply elem_of_union in Ht as [Ht | Ht]; apply elem_of_singleton in Ht as ->;
        [exists 0 | exists 1]; split; done || (cbn; lia). }
    iClear "Hswitcher_tstacks".
    iEval (rewrite Hthreads big_sepL_cons big_sepL_singleton) in "Hswitcher_static".
    iDestruct "Hswitcher_static" as "[#Hswitcher_static #Hstatic1]".
    iDestruct (switcher_static_seal_pred with "Hswitcher_static") as "#Hseal_switcher".
    iDestruct (fw_lock_static (kvs_firmware ot_kvs key_main key_B) img σ (UserThread 0)
                 Hok Huse_lock with "Hlocks") as "#Hlock_static".
    iEval (cbv [kvs_firmware fw_cmpts]; rewrite !big_sepL_cons big_sepL_nil;
           cbv [fw_cmpt_res_user fc_body]) in "Hcmpts".
    iDestruct "Hcmpts"
      as "((Hmain & Hmain_static_sealed & _) & (Hkvs & _ & #Hkvs_pers) &
           (HB & HB_static_sealed & #HB_pers) & _)".
    iDestruct "Hkvs" as "(Hkvs_imports & Hkvs_code & Hkvs_data)".
    iDestruct "Hkvs_pers" as "(Hkvs_etbl_pcc & Hkvs_etbl_cgp & Hkvs_etbl_nh & Hkvs_etbl_entries)".
    iEval (cbn [fw_handler_res fc_body tb_error_handler tb_error_handler_stackless]) in "Hkvs_etbl_nh".
    iEval (cbv [kvs_firmware fw_otypes]) in "Hotypes".
    iDestruct "Hotypes" as "[Hseal_store_kvs _]".
    set (W0 := fw_world0).

    cbn [fc_name]. rewrite /fw_cmpt_static_res.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt kvs_cmpt. fw_fold_cmpt B_cmpt.

    (* 6.1 The KVS compartment: its resources, and the lock *)
    iEval (rewrite cmpt_code_codefrag) in "Hkvs_code".
    rewrite kvs_imports kvs_code kvs_data.
    iMod (user_kvs_init (th := UserThread 0) (KVS := kvsl) (LK := lkl) {[ key_main ; key_B ]}
           with "[$Hkvs_imports $Hkvs_code $Hlock_static $Hkvs_data]")
      as (γpkvs kvs_logical_heapg γf)
           "(#Hkvs_static & Hlock_word & Hkvs_physical & Hkvs_logical & Hlukvs)".
    pose kvsphysicalg := Build_KvsPhysicalG Σ kvs_physical_user_preg γpkvs.
    pose kvslogicalg := Build_KvsLogicalG Σ kvs_logical_heapg.
    pose kvsuserg := Build_KvsUserG Σ kvs_logical_user_preg γf.
    pose kvsg := KvsG Σ kvsphysicalg kvslogicalg kvsuserg.
    iDestruct (big_sepS_delete _ _ key_main with "Hlukvs")
      as "[ [Hkvs_logical_user_K HK_lukvs_frag] Hlukvs]"; first by set_solver+.
    iDestruct (big_sepS_delete _ _ key_B with "Hlukvs")
      as "[ [Hkvs_logical_user_B HB_lukvs_frag] _]"; first by set_solver+Hkeys.
    (* The users under the lock: B only; main keeps its own maps *)
    set (kvs_users := {[ key_B := B ]} : gmap user_key_t CmptName).
    iAssert (|={⊤}=> kvs_lock (kvsg := kvsg) (KVS := kvsl) kvs_users)%I
      with "[Hlock_word Hkvs_physical Hkvs_logical Hkvs_logical_user_B HB_lukvs_frag]"
      as ">#Hlock".
    { rewrite /kvs_lock.
      iApply (lock_inv_alloc with "Hlock_word").
      iNext. rewrite /kvs_R /kvs_users big_sepM_singleton.
      iSplitL "Hkvs_physical"; first iExact "Hkvs_physical".
      iSplitL "Hkvs_logical"; first iExact "Hkvs_logical".
      iSplitL "Hkvs_logical_user_B"; first iExact "Hkvs_logical_user_B".
      iApply (big_sepS_impl with "HB_lukvs_frag").
      iModIntro; iIntros (mk Hmk) "Hmk". rewrite /safe_kvs_pointsto. iRight. iExact "Hmk". }
    iMod (seal_store_update_alloc _ SealGlobal (kvs_otype_propC kvs_users)
           with "Hseal_store_kvs")
      as "#Hsealed_pred_ot_kvs".

    (* 6.2 The static sealed key of B, persisted *)
    iEval (rewrite B_static_sealed) in "HB_static_sealed".
    iDestruct (region_pointsto_single with "HB_static_sealed") as "(%&Ha_user_key_B&%Hv_B)";
      try (cbn in Hv_B); simplify_eq.
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H1.
      rewrite B_static_sealed in H1; solve_addr+H1.
    }
    set (user_key_addr_B := cmpt_b_static_sealed B_cmpt).
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry kvs_B_entry_f)).
    iMod (pointsto_persist with "Ha_user_key_B") as "#Ha_user_key_B".

    (* 6.3 The export table of the KVS *)
    rewrite kvs_exp_tbl.
    iEval (rewrite !big_sepL_cons) in "Hkvs_etbl_entries".
    iDestruct "Hkvs_etbl_entries"
      as "(Hkvs_etbl_entries_addOrUpdate & Hkvs_etbl_entries_read
          & Hkvs_etbl_entries_erase & _)".

    (* 7 - The exported entries of the KVS, sealed with [ot_switcher], are
       valid in the world of B, at both its threads *)
    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_addOrUpdate))
      as "#ot_switcher_kvs_addOrUpdate".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply (kvs_addOrUpdate_entry_point_spec (th := UserThread 0) (KVS_layout := kvsl) (LK := lkl)
                kvs_users Global W0 B Hkvs_switcher Hlock_heap Hlocks_heap).
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hlock Hswitcher_threads_B
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_nh Hkvs_etbl_entries_addOrUpdate".
    }
    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_read))
      as "#ot_switcher_kvs_read".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply (kvs_read_entry_point_spec (th := UserThread 0) (KVS_layout := kvsl) (LK := lkl)
                kvs_users Global W0 B Hkvs_switcher Hlock_heap Hlocks_heap).
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hlock Hswitcher_threads_B
        Hkvs_etbl_pcc Hkvs_etbl_cgp Hkvs_etbl_nh Hkvs_etbl_entries_read".
    }
    iAssert (ot_switcher_prop (th := UserThread 0) W0 B (WSealable kvs_erase))
      as "#ot_switcher_kvs_erase".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ ExportTable_offset_cgp) by solve_addr+H0.
      iApply (kvs_erase_entry_point_spec (th := UserThread 0) (KVS_layout := kvsl) (LK := lkl)
                kvs_users Global W0 B Hkvs_switcher Hlock_heap Hlocks_heap).
      iFrame "Hsealed_pred_ot_kvs Hkvs_static Hlock Hswitcher_threads_B
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

    (* The sealed user key of B: its key word, registered for B *)
    set (kvs_user_key_B_sb := (kvs_user_seal_key_scap Global user_key_addr_B)).
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
    iAssert (kvs_otype_propC kvs_users
               (UserThread 0, W0, B, lword_of_word (WSealable kvs_user_key_B_sb)))
      as "#ot_kvs_user_key_B".
    { iExists user_key_addr_B, key_B. iFrame "Ha_user_key_B".
      iPureIntro. split; first done. split; first exact Hshape_B.
      cbn [fst snd]. by rewrite /kvs_users lookup_singleton_eq. }
    iAssert (interp (th := UserThread 0) W0 B (WSealed ot_kvs kvs_user_key_B_sb))
      as "#Hinterp_kvs_user_key_B".
    { iApply (interp_sealed_of_seals (th := UserThread 0) W0 B ot_kvs
                (kvs_otype_propC kvs_users) kvs_user_key_B_sb
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

    (* 8 - B opened on its map of Permanent regions, which goes into its
       invariant; its imports are safe *)
    iDestruct (big_sepS_delete _ _ B with "Hworlds") as "[Hperm_B _]".
    { apply elem_of_difference. split; last set_solver+HBS.
      rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iPoseProof (thread_in_intro (Σ := Σ) (UserThread 0) B Hin0_B) as "#Hthread_B".
    iMod (fw_open_adv_cmpt_perm (th := UserThread 0)
            _ _ _ 2 (fw_nth 2 (fw_cmpts (kvs_firmware ot_kvs key_main key_B)) default_fw_cmpt)
            _ HB_l W0 B Hok eq_refl eq_refl ltac:(cbn; repeat constructor; lia)
           with "Hswitcher_threads_B Hswitcher_static HB HB_pers [] Hthread_B Hperm_B")
      as "(Hperm_B & #Hpcc_B & #Hcgp_B & #Hinterp_B_exports)".
    { iIntros "_".
      rewrite -(fw_imports_safe_words _ _
                  (fw_nth 2 (fw_cmpts (kvs_firmware ot_kvs key_main key_B)) default_fw_cmpt)
                  _ (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl)).
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (cmpt_imports B_cmpt).
      rewrite B_imports'.
      (* Switcher cross-compartment *)
      iApply big_sepL_cons; iSplitL.
      { iApply (fw_switcher_call_safe _ _ _ (cmpt_of img "B") with "Hswitcher_threads_B").
        exact Hok. }
      (* The KVS entries and the sealed user key are Global: valid in every
         world, at every thread *)
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
                (kvs_firmware ot_kvs key_main key_B) img σ 1
                (fw_thread_of (kvs_firmware ot_kvs key_main key_B) 1) _ B W0 HB_l
                Hok with "Hstatic1 HB_pers Hpcc_B Hcgp_B Hinv_B").
      - reflexivity.
      - reflexivity.
      - exact Hin1_B.
      - exact HB_shared.
    }

    (* 9 - The thread 0, in main: its world of B is its local map with its
       stack revoked, joined with the invariant of B *)
    iClear "Hstatic1".
    iIntros "Hthread _". iNamed "Hthread".
    iEval (rewrite (fw_entry_pc_code (kvs_firmware ot_kvs key_main key_B) img σ
                      ltac:(reflexivity) Hok)) in "HPC".
    iEval (rewrite fw_thread_cra_eq) in "Hcra".
    iEval (rewrite fw_thread_of_0) in "Hstack".
    iEval (rewrite /fw_thread_csp; cbv zeta) in "Hcsp".
    iEval (rewrite /fw_entry_cgp; cbv zeta) in "Hcgp".
    iEval (rewrite /fw_entry_frame /fw_thread_csp /fw_entry_tbl; cbv zeta) in "Hcstk".
    iDestruct (big_sepS_elem_of _ _ B with "Hlocals") as "Hlocal_B".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }
    iMod (fw_shared_caller_world img 0 B HB_shared with "Hinv_B Hlocal_B")
      as "[Hworld_B Hrevoked_stack_B]".
    set (Wk := std_update_multiple fw_world0
                 (finz.seq_between (image.b_stack (thread_of img 0))
                    (image.e_stack (thread_of img 0)))
                 Revoked).
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack (kvs_firmware ot_kvs key_main key_B) 0) with 6 in Hentry_min_stack.
    assert (∀ b e : Z, b + Z.of_nat 6 + StackEntry_reserved_space <= e →
              b + SpillSlot_size + 2 * StackEntry_reserved_space <= e)%Z as Hmin_bridge
      by (rewrite /SpillSlot_size /StackEntry_reserved_space; lia).
    apply Hmin_bridge in Hentry_min_stack; clear Hmin_bridge.
    cbn [fc_name].
    change (fw_entry_cmpt (kvs_firmware ot_kvs key_main key_B) img 0) with (cmpt_of img "main").
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ kvs_B_entry_f 0
                 (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".
    (* The export of B, from the empty world to the world of the call *)
    iEval (cbn [fc_name fw_nth fw_cmpts kvs_firmware]; rewrite HsbB) in "Hinterp_B_f".
    iDestruct (interp_sealed_global_kind_world_free fw_world0 Wk B _ _ _ None
                with "[] Hinterp_B_f") as "#Hinterp_B".
    { iApply (switcher_static_seal_pred with "Hswitcher_static"). }
    iClear "Hinterp_B_f Hpcc_B Hcgp_B HB_pers".
    fw_fold_cmpt main_cmpt.
    rewrite main_imports' main_code main_data main_static_sealed.
    clear main_imports.
    iDestruct (big_sepS_elem_of _ _ 1%Z with "HK_lukvs_frag") as "HK_lukvs_1".
    { eapply is_uint16_in_kvs_all_map_keys; split; rewrite /UINT16_MIN /UINT16_MAX; lia. }

    (* 10 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    replace (cmpt_exp_tbl_cgp kvs_cmpt) with (b_kvs_exp_tbl ^+ ExportTable_offset_cgp)
      by (pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H; unfold kvsl; cbn in H |- *; solve_addr+H).
    pose proof (cmpt_static_sealed_base_not_heap main_cmpt) as Hstatic_key_nonheap.
    assert (is_heap_cap (WSealed switcher.ot_switcher B_f) = false) as HB_f_nonheap.
    { unfold B_f. apply sealed_cap_nonheap. exact (cmpt_exp_tbl_base_not_heap B_cmpt). }
    iApply (kvs_main_spec (th := UserThread 0) (cthreads := cthreads) (swlayout := swl)
              (kvsg := kvsg) (KVS_layout := kvsl) (LK := lkl) (B := B) kvs_users
              _ _ _ _ _ _ _ _ _ _ key_main _ _ _ B_f Wk [] [] _ _ _
             with "[ $Hassert $Hthread_B $Hswitcher $Hswitcher_static $Hkvs_static $Hlock
                    $Hkvs_etbl_pcc $Hkvs_etbl_cgp $Hkvs_etbl_entries_addOrUpdate $Hkvs_etbl_entries_read
                    $Hna $HPC $Hcgp $Hcsp $Hcra $Hregs
                    $Hmain_imports $Hmain_code $Hmain_data $Hmain_static_sealed $Hstack
                    $Hkvs_logical_user_K $HK_lukvs_1
                    $Hworld_B $Hcstk
                    $Hinterp_B $Hentry_Bf $Hrevoked_stack_B
                    $HMIE $Hheld
                    ]").
    all: eauto using fw_cleared_regs_dom.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { eapply disjoint_from_shadow_not_in.
      - exact (cmpt_static_sealed_disjoint_from_shadow main_cmpt).
      - apply withinBounds_true_iff.
        pose proof (cmpt_static_sealed_size main_cmpt) as Hsize.
        rewrite main_static_sealed in Hsize; cbn in Hsize |- *; solve_addr+Hsize.
    }
    { exact (stack_disjoint_from_mmio swc). }
    { exact (stack_disjoint_from_heap swc). }
    { intros r Hr. by apply elem_of_dom. }
    { pose proof (cmpt_static_sealed_size main_cmpt) as Hsize.
      by rewrite main_static_sealed in Hsize.
    }
    { rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    { done. }
    { by rewrite /route_pre. }
  Qed.
End kvs_obligations.
