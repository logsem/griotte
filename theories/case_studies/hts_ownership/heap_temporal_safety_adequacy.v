From iris.proofmode Require Import proofmode.
(* Imported first: the fields of the layout records of [compartment_layout]
   and [switcher] shadow those of the image records. *)
From griotte Require Import image firmware firmware_ok firmware_adequacy firmware_obligations.
From griotte.case_studies.hts_ownership Require Import hts_firmware.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import assert_spec.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_base_interp.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.
From griotte Require Import allocator_resources heap_region.
From griotte.case_studies.hts_ownership Require Import
  heap_temporal_safety heap_temporal_safety_preamble heap_temporal_safety_spec.
From griotte.allocators.ownership Require Import
  allocator allocator_preamble allocator_resource_spec allocator_malloc_safe allocator_free_safe
  allocator_adequacy.

Section hts_obligations.
  Context {Σ : gFunctors}.
  Context {allocator_owner_preg : allocatorOwnerPreG Σ}.
  Context {cname : CmptNameG} {B : CmptName}.
  Context `{MP : MachineParameters}.

  (** The obligations of the trusted code of the heap temporal safety
      firmware: the thread runs safely from the export [entry] of [main],
      the untrusted compartment ["B"] being owned by the logical compartment
      [B]. *)
  Lemma hts_fw_obligations (ot_alloc : OType) :
    fw_obligations Σ (hts_firmware ot_alloc).
  Proof.
    apply fw_obligations_of; first reflexivity.
    intros img σ ceriseg seal_storeg stsg relg cstackg Hok.

    (* 1 - The contents and the layouts of the compartments *)
    pose proof (fw_cmpt_ok_at _ _ _ 0 _ Hok eq_refl) as Hok_main.
    pose proof (fw_cmpt_ok_at _ _ _ 1 _ Hok eq_refl) as Hok_alloc.
    pose proof (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) as Hok_B.
    cbv [cmpt_ok section body_ok fc_name fc_body fc_imports fc_static_sealed fw_imap
      fw_imap_from fw_word_of note addr_off nat_str chunks_words export_word
      fe_offset fe_nargs fe_min_stack fe_posture tb_code tb_data tb_exports
      fc_unknown_export fw_words_unknown fw_word_unknown chunks_fw_words fw_flat_map fw_app
      fw_export_index fw_body_export_index fw_index_of fw_cmpt_of fw_cmpts hts_firmware
      fe_name ue_name ub_exports ss_name ss_word fw_map String.eqb Ascii.eqb Bool.eqb andb]
      in Hok_main, Hok_alloc, Hok_B.
    destruct Hok_main as (main_imports & main_static & main_code & main_data & _).
    destruct Hok_alloc as (alloc_imports & _ & alloc_code & alloc_data & _ & alloc_exp_tbl).
    destruct Hok_B as (B_imports & B_static & _).
    pose proof (fw_cmpt_layout_at _ _ _ 0 _ Hok eq_refl) as Hmain_l.
    pose proof (fw_cmpt_layout_at _ _ _ 1 _ Hok eq_refl) as Halloc_l.
    pose proof (fw_cmpt_layout_at _ _ _ 2 _ Hok eq_refl) as HB_l.
    pose proof (fw_switcher_layout_wf_of _ _ _ Hok) as Hswl_wf.
    pose proof (fw_cmpts_disjoint_at _ _ _ 0 2 _ _ Hmain_l HB_l Hok ltac:(done) eq_refl eq_refl)
      as HmainB.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 0 _ Hmain_l eq_refl) as Hsw_main.
    pose proof (fw_switcher_cmpt_disjoint_at _ _ _ Hok 1 _ Halloc_l eq_refl) as Hsw_alloc.
    cbn [fc_name] in Hmain_l, Halloc_l, HB_l, HmainB, Hsw_main, Hsw_alloc.
    set (main_cmpt := layout_cmpt_of (cmpt_of img "main") Hmain_l) in *.
    set (alloc_cmpt := layout_cmpt_of (cmpt_of img "allocator") Halloc_l) in *.
    set (B_cmpt := layout_cmpt_of (cmpt_of img "B") HB_l) in *.
    set (swc := fw_switcher_cmpt _ _ _ Hok) in *.
    set (swl := fw_switcher_layout img) in *.
    set (asl := fw_assert_layout img).

    (* 2 - The layout of the allocator *)
    assert (ot_alloc ≠ switcher.ot_switcher) as Hot_alloc_switcher.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [Hot_nodup _].
      cbn in Hot_nodup. apply NoDup_cons in Hot_nodup as [Hot_notin _]. set_solver+Hot_notin. }
    assert (ot_alloc < ot_alloc ^+ 1)%ot as Hot_alloc_size.
    { destruct (img_wf_otypes _ _ (proj2 (proj2 (proj2 Hok)))) as [_ Hot_valid].
      cbn in Hot_valid. rewrite Forall_cons Forall_singleton in Hot_valid. apply Hot_valid. }
    destruct (fw_heap_machine _ _ _ Hok ltac:(by cbn)) as [Haffine Hrevoker].
    pose (alloclayout := img_allocator_layout (cmpt_of img "allocator") ot_alloc).
    assert (image.cmpt_imports (cmpt_of img "allocator") = img_allocator_imports ot_alloc)
      as alloc_imports'.
    { by rewrite alloc_imports. }
    assert allocatorLayoutWf as allocwf.
    { by apply img_allocator_layout_wf. }
    fw_fold_cmpt main_cmpt. fw_fold_cmpt alloc_cmpt. fw_fold_cmpt B_cmpt.
    (* The allocator's code is outside the switcher's: its faults are not
       resumed by the exception path *)
    assert (allocator_pcc_b ≠ switcher.b_switcher) as Halloc_switcher.
    { apply (switcher_cmpt_disjoint_pcc_b alloc_cmpt swc Hsw_alloc).
      pose proof allocator_size_imports as Himports_size.
      pose proof allocator_size_code as Hcode_size.
      cbn in Himports_size, Hcode_size |- *.
      solve_addr. }
    (* 3 - The export entries, imported by main and B *)
    set (B_f := SCap true RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                  (cmpt_exp_tbl_pcc B_cmpt ^+ ExportTable_offset_entry hts_B_entry_adv)%a).
    set (malloc_f := allocator_malloc Global).
    set (free_f := allocator_free Global).
    assert (cmpt_export_sb (cmpt_of img "B") hts_B_entry_adv = B_f ∧
            cmpt_export_sb (cmpt_of img "allocator") allocator_entry_malloc = malloc_f ∧
            cmpt_export_sb (cmpt_of img "allocator") allocator_entry_free = free_f)
      as (HsbB & Hsb0 & Hsb1).
    { by split_and!. }
    assert (cmpt_imports main_cmpt = hts_main_imports (cmpt_b_static_sealed main_cmpt) B_f)
      as main_imports'.
    { by rewrite main_imports /hts_main_imports. }

    (* 4 - The resources of the image *)
    iIntros "Hres". iNamed "Hres".
    pose proof (fw_entry_min_stack_ok _ _ _ Hok) as Hentry_min_stack.
    change (fw_entry_min_stack (hts_firmware ot_alloc) 0) with 7 in Hentry_min_stack.
    assert (∀ b e : Z, b + Z.of_nat 7 + StackEntry_reserved_space <= e →
              b + 1 + SpillSlot_size + 2 * StackEntry_reserved_space <= e)%Z as Hmin_bridge
      by (rewrite /SpillSlot_size /StackEntry_reserved_space; lia).
    apply Hmin_bridge in Hentry_min_stack; clear Hmin_bridge.
    iEval (cbv [hts_firmware fw_cmpts]) in "Hcmpts".
    iDestruct "Hcmpts"
      as "((Hmain & Hmain_static & _) & (Halloc & _ & #Halloc_pers) & (HB & HB_static & #HB_pers) & _)".
    cbn [fc_name].
    change (fw_entry_cmpt (hts_firmware ot_alloc) img 0) with (cmpt_of img "main").
    iEval (cbv [hts_firmware fw_otypes]) in "Hotypes".
    iDestruct "Hotypes" as "[Hseal_store_alloc _]".
    iEval (cbv [hts_firmware fw_heap_roots fw_set]) in "Hclaims".

    (* 5 - Ghost state: one owner identifier for main, one for B *)
    pose (FA := (free_auth_owner : FreeAuth Σ)).
    iMod (allocator_owners_init {[hts_main_owner_id; hts_adv_owner_id]})
      as (allocator_ownerg) "[Howners Hids]".
    iDestruct (big_sepS_insert with "Hids") as "[Hid_main Hid_adv]".
    { rewrite /hts_main_owner_id /hts_adv_owner_id. set_solver. }
    iEval (rewrite big_sepS_singleton) in "Hid_adv".
    iMod (seal_store_update_alloc AllocOtype allocator_otype_propC with "Hseal_store_alloc")
      as "#Hsealed_pred_alloc".

    (* 6 - The allocator: its service invariant owns the heap *)
    iMod (allocator_init img (fw_nth 1 (fw_cmpts (hts_firmware ot_alloc)) default_fw_cmpt)
            ot_alloc {[hts_main_owner_id; hts_adv_owner_id]} _ Halloc_l allocwf
            alloc_imports' alloc_code alloc_data alloc_exp_tbl eq_refl eq_refl eq_refl
           with "Halloc Halloc_pers Howners Hheap Hshadow Hclaims")
      as "(#Hservice & #Hservice_static & #Halloc_etbl_pcc & #Halloc_etbl_cgp & #Halloc_etbl_nh
           & #Hexport_malloc & #Hexport_free)".
    cbn [fc_name fw_nth fw_cmpts hts_firmware].
    fw_fold_cmpt main_cmpt. fw_fold_cmpt alloc_cmpt. fw_fold_cmpt B_cmpt.
    iMod (fw_cmpt_mem_persist with "Hmain") as "(#Hmain_imports & #Hmain_code & Hmain_data)";
      first exact Hmain_l.
    fw_fold_cmpt main_cmpt.
    rewrite main_imports' main_code main_data.
    iDestruct (fw_cmpt_pers_res_export_nargs _ _ _ hts_B_entry_adv 1
                 (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl) with "HB_pers")
      as "#Hentry_Bf"; [done|lia|].
    iEval (rewrite HsbB) in "Hentry_Bf".
    iDestruct (big_sepS_elem_of_acc _ _ B with "Hworlds") as "[Hworld_B _]".
    { rewrite /CNames elem_of_list_to_set. apply finite.elem_of_enum. }

    (* 7 - The owner words, in the static sealed regions *)
    set (adv_owner_a := cmpt_b_static_sealed B_cmpt).
    set (main_owner_a := cmpt_b_static_sealed main_cmpt).
    assert ((adv_owner_a + 1)%a = Some (cmpt_e_static_sealed B_cmpt)) as Hadv_owner_size.
    { pose proof (cmpt_static_sealed_size B_cmpt) as Hsize.
      by rewrite B_static in Hsize. }
    assert ((main_owner_a + 1)%a = Some (cmpt_e_static_sealed main_cmpt)) as Hmain_owner_size.
    { pose proof (cmpt_static_sealed_size main_cmpt) as Hsize.
      by rewrite main_static in Hsize. }
    rewrite /fw_cmpt_static_res. fw_fold_cmpt main_cmpt. fw_fold_cmpt B_cmpt.
    iEval (rewrite B_static) in "HB_static".
    iDestruct (region_pointsto_single with "HB_static")
      as (w_adv_owner) "[Hadv_owner %Hw_adv_owner]"; first exact Hadv_owner_size.
    injection Hw_adv_owner as <-.
    iEval (rewrite main_static) in "Hmain_static".
    iDestruct (region_pointsto_single with "Hmain_static")
      as (w_main_owner) "[Hmain_owner %Hw_main_owner]"; first exact Hmain_owner_size.
    injection Hw_main_owner as <-.

    (* 8 - Seal the exported entries of the allocator in the world of B *)
    iMod (seal_service_exports fw_world0 B [malloc_f; free_f]
           with "Hseal_switcher [] Hworld_B")
      as "(Hworld_B & #Hseal_alloc)"; [by repeat constructor | done | |].
    { iModIntro. iSplit; last iSplit; last done.
      - iApply (malloc_entry_point_spec Global _ B);
          [exact Halloc_switcher |].
        iFrame "#".
      - iApply (free_entry_point_spec Global _ B);
          [exact Halloc_switcher |].
        iFrame "#". }
    set (W1 := <o[ switcher.ot_switcher := exports_words [malloc_f; free_f] ]o> fw_world0).

    (* 9 - Seal the allocator capability of B, with its owner identifier *)
    set (adv_alloc_sb := allocator_capability_scap Global adv_owner_a).
    set (adv_alloc_words :=
      ({[lword_of_word (WSealable adv_alloc_sb);
         lword_of_word (borrow (WSealable adv_alloc_sb))]} : gset LWord)).
    set (W1' := <o[AllocOtype := adv_alloc_words]o> W1).
    iAssert (allocator_otype_propC (W1', B, lword_of_word (WSealable adv_alloc_sb)))
      with "[Hadv_owner Hid_adv]" as "Hadv_alloc_prop".
    { iExists hts_adv_owner_id, adv_owner_a, ∅. iFrame "Hadv_owner Hid_adv".
      rewrite /allocator_owned_rights big_sepS_empty.
      iPureIntro. split; first reflexivity. split.
      - apply withinBounds_true_iff. solve_addr+Hadv_owner_size.
      - split; last done.
        eapply disjoint_from_shadow_not_in.
        + exact (cmpt_static_sealed_disjoint_from_shadow B_cmpt).
        + apply withinBounds_true_iff. subst adv_owner_a.
          solve_addr+Hadv_owner_size. }
    assert (AllocOtype ∉ dom (seal_std W1)) as Halloc_fresh.
    { subst W1. rewrite dom_insert_L dom_empty_L.
      apply not_elem_of_union. split; last set_solver+.
      apply not_elem_of_singleton. intros Heq. by apply Hot_alloc_switcher. }
    iMod (world_interp_salloc W1 B allocator_otype_propC AllocOtype adv_alloc_words
           with "[$Hsealed_pred_alloc] [] [Hadv_alloc_prop] [$Hworld_B]")
      as "(Hworld_B & #Hseal_alloc_adv)"; first exact Halloc_fresh.
    { iIntros (w); iApply mono_priv_ot_allocator. }
    { rewrite normalise_sealed_words_borrow big_sepS_singleton.
      iNext. iExact "Hadv_alloc_prop". }

    (* 10 - Close the world of B: its compartment becomes permanent, and the
       stack temporary, because main shares it with B; the imports of B are
       safe; its export is safe to share. *)
    iMod (fw_close_adv_world _ _ _ 2 (fw_nth 2 (fw_cmpts (hts_firmware ot_alloc)) default_fw_cmpt) _
            HB_l W1' B Hok eq_refl eq_refl ltac:(apply Forall_singleton; cbn; lia) ltac:(done)
           with "Hswitcher Hswitcher_static Hseal_switcher HB HB_pers Hstack [] Hworld_B")
      as "(Hworld_B & #Hinterp_stack_B & [#Hinterp_B_f _])".
    { iIntros "_".
      rewrite -(fw_imports_safe_words _ _
                  (fw_nth 2 (fw_cmpts (hts_firmware ot_alloc)) default_fw_cmpt)
                  _ _ (fw_cmpt_ok_at _ _ _ 2 _ Hok eq_refl)).
      change (image.cmpt_imports (cmpt_of img (fc_name _))) with (cmpt_imports B_cmpt).
      rewrite B_imports.
      iSplit; first by iApply (fw_switcher_call_safe _ _ _ (cmpt_of img "B")
                                 with "Hswitcher Hswitcher_static").
      iSplit.
      { iApply (sealed_import_safe with "Hseal_alloc"); [done | |].
        - rewrite -Hsb0 /cmpt_export_sb /=. apply exports_words_elem_of. set_solver.
        - intros ? ? ? ? ? Heq; injection Heq; intros; subst.
          apply (cmpt_exp_tbl_disjoint_from_heap alloc_cmpt). }
      iSplit.
      { iApply (sealed_import_safe with "Hseal_alloc"); [done | |].
        - rewrite -Hsb1 /cmpt_export_sb /=. apply exports_words_elem_of. set_solver.
        - intros ? ? ? ? ? Heq; injection Heq; intros; subst.
          apply (cmpt_exp_tbl_disjoint_from_heap alloc_cmpt). }
      iSplit; last done.
      iApply (sealed_import_safe with "Hseal_alloc_adv"); [done | done |].
      intros ? ? ? ? ? Heq; injection Heq; intros; subst.
      fw_fold_cmpt B_cmpt.
      replace (cmpt_b_static_sealed B_cmpt ^+ 1)%a with (cmpt_e_static_sealed B_cmpt)
        by (rewrite /adv_owner_a in Hadv_owner_size; solve_addr+Hadv_owner_size).
      apply cmpt_static_sealed_disjoint_from_heap. }
    iEval (rewrite /fw_thread_csp) in "Hinterp_stack_B".
    cbn [fc_name fw_nth fw_cmpts hts_firmware]. rewrite HsbB.
    fw_fold_cmpt main_cmpt. fw_fold_cmpt B_cmpt.

    (* 11 - We can apply the specification! *)
    pose proof (main_spec_size_obligations _ _ _ _ main_imports' main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    iPoseProof (hts_main_spec (swlayout := swl) (assertlayout := asl) (alloclayout := alloclayout)
                  (C := B) _ _ _ _ _ _ _ _ B_f main_owner_a _ [] [] _
                 with "[$Hassert $Hservice $Hservice_static $Hswitcher $Hswitcher_static
                        $Halloc_etbl_pcc $Halloc_etbl_cgp $Hexport_malloc $Hexport_free
                        $Hna $Hid_main $Hmain_owner $HPC $Hcgp $Hcsp $Hcra $Hregs
                        $Hmain_imports $Hmain_code $Hmain_data
                        $Hworld_B $Hcstk
                        $Hinterp_B_f $Hentry_Bf $Hinterp_stack_B]")
      as "Hspec"; eauto using fw_cleared_regs_dom.
    { eapply disjoint_from_shadow_not_in.
      - exact (cmpt_static_sealed_disjoint_from_shadow main_cmpt).
      - apply withinBounds_true_iff. subst main_owner_a. solve_addr+Hmain_owner_size. }
    { apply withinBounds_true_iff. solve_addr+Hmain_owner_size. }
    { exact (proj1 (cmpt_static_sealed_not_heap_range main_cmpt)). }
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { exact (cmpt_cgp_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_cgp_not_heap_range main_cmpt). }
    { intros r Hr. by rewrite fw_cleared_regs_lookup. }
    { apply (main_cgp_not_in_adv_world Temporary W1' swc main_cmpt B_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size. }
    { by rewrite (adv_world_with_heap Temporary W1' swc B_cmpt). }
    { done. }
    iModIntro.
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End hts_obligations.

(** We initialise concretely the compartments name typeclass. *)

Inductive CmptNames_hts := | B.
#[local] Instance CmptNames_hts_eq_dec : EqDecision CmptNames_hts.
Proof. intros C1 C2; destruct C1, C2; solve_decision. Qed.
#[local] Instance CmptNames_hts_finite : finite.Finite CmptNames_hts.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_hts_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_hts; |}.

(** The logical compartment of the adversary. *)
Definition hts_adv_B : @CmptName CmptNames_hts_CmptNameG := B.

(* The fields of the image records, for the end-to-end statement. *)
Import image.

(** END-TO-END THEOREM *)
Theorem hts_adequacy `{MP : MachineParameters} (flag : Addr) (σ σ' : ExecConf) es :
  hts_initial_state_ok flag σ →
  rtc erased_step ([Seq (Instr Executable)], σ) (es, σ') →
  mem σ' !! flag = Some (WInt 0).
Proof.
  intros Hok Hstep.
  destruct (hts_initial_state_ok_start _ _ Hok)
    as (sw & asrt & t0 & main & allocator & B & ot_alloc & <- & Hfw).
  eapply (firmware_adequacy_closed (Cname := CmptNames_hts_CmptNameG) allocator_ownerΣ
            (hts_firmware ot_alloc) (hts_img sw asrt t0 main allocator B));
    [| exact Hfw | exact Hstep].
  apply (hts_fw_obligations (B := hts_adv_B)).
Qed.
