From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import stack_object stack_object_spec_closure stack_object_spec.
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

Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adv compartments C *)
    C_cmpt : cmpt ;
    offset_adv_f : nat;
    offset_adv_g : nat;
    offset_adv_f_valid :
      is_Some (cmpt_b_pcc C_cmpt + offset_adv_f%nat)%a;
    offset_adv_g_valid :
      is_Some (cmpt_b_pcc C_cmpt + offset_adv_g%nat)%a;

    (* disjointness *)
    cmpts_disjoints :
    main_cmpt ## C_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint main_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint C_cmpt switcher_cmpt ;

    assert_cmpt_disjoints :
    assert_cmpt_disjoint main_cmpt assert_cmpt
    ∧ assert_cmpt_disjoint C_cmpt assert_cmpt ;

    assert_switcher_disjoints :
    assert_switcher_disjoint assert_cmpt switcher_cmpt;
  }.
#[export] Hint Mode memory_layout - : typeclass_instances.

#[local] Instance memory_layout_switcherLayout `{memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

#[local] Instance memory_layout_switcherLayoutWf `{memory_layout} : switcherLayoutWf.
Proof.
  pose proof (ot_switcher_size switcher_cmpt).
  pose proof (switcher_size switcher_cmpt).
  pose proof (switcher_call_entry_point switcher_cmpt).
  pose proof (switcher_return_entry_point switcher_cmpt).
  pose proof (trusted_stack_disjoint_from_shadow switcher_cmpt).
  pose proof (switcher_base_not_shadow switcher_cmpt).
  pose proof (compartment_layout.switcher_not_heap_range switcher_cmpt).
  pose proof (compartment_layout.trusted_stack_not_heap switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _ _ _ _ _); cbn in *; auto.
Defined.

#[local] Instance memory_layout_assertLayout `{memory_layout} : assertLayout.
Proof.
  exact (cmptAssert_assertLayout assert_cmpt).
Defined.

Definition mk_initial_program_memory `{memory_layout} :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt C_cmpt.


(** Initial allocator memory is separate from all compartment resources. *)
Definition mk_initial_memory `{memory_layout} : Mem :=
  initial_heap_memory ∪ mk_initial_program_memory.

Definition is_initial_registers `{memory_layout} := is_initial_registers_of switcher_cmpt main_cmpt.

Definition is_initial_sregisters `{@memory_layout MP} := is_initial_sregisters_of switcher_cmpt.

Definition is_initial_memory `{@memory_layout MP} (mem: Mem) :=
  let b_switcher := (b_switcher switcher_cmpt) in
  let e_switcher := (e_switcher switcher_cmpt) in
  let a_switcher_call := (a_switcher_call switcher_cmpt) in
  let ot_switcher := (ot_switcher switcher_cmpt) in
  let switcher_entry :=
    WSentry FwdDisable true XSRW_ Local
      b_switcher
      e_switcher
      a_switcher_call
  in
  let C_f :=
    SCap true RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      (cmpt_exp_tbl_entries_start C_cmpt)
  in
  let C_g :=
    SCap true RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      ((cmpt_exp_tbl_entries_start C_cmpt) ^+ 1)%a
  in

  mem = mk_initial_memory
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = so_main_imports C_f
  ∧ (cmpt_code main_cmpt) = so_main_code
  ∧ (cmpt_data main_cmpt) = so_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = so_export_table_entries
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed main_cmpt)

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) =
  [switcher_entry
   ; WSealed ot_switcher (so_entry_f_sb (cmpt_exp_tbl_pcc main_cmpt)
                            (cmpt_exp_tbl_entries_end main_cmpt))
   ; WSealed ot_switcher C_g
  ]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point InterruptEnabled 0 offset_adv_f); WInt (encode_entry_point InterruptEnabled 2 offset_adv_g)]
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed C_cmpt)

  (* initial stack *)
  ∧ Forall is_z (stack_content switcher_cmpt)
.

Lemma mk_initial_cmpt_C_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt
    ##ₘ mk_initial_cmpt C_cmpt.
Proof.
  pose proof cmpts_disjoints as HmainC.
  pose proof switcher_cmpt_disjoints as (_ & HswitcherC).
  pose proof assert_cmpt_disjoints as ( _ & HassertC).
  do 2 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_main_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt
    ##ₘ mk_initial_cmpt main_cmpt.
Proof.
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _).
  pose proof assert_cmpt_disjoints as (HassertMain & _).
  rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {C : CmptName}.
  Context {inv_preg: invGpreS Σ}.
  Context {cerise_preg : ceriseGpreS Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invariants.na_invG Σ}.
  Context {sts_preg: STS_preG LAddr region_type OType LWord Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [C]) }.

  Definition flagN : namespace := nroot .@ "so" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "so" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "so" .@ "assert_flag".
  Definition soN : namespace := nroot .@ "so" .@ "code".

  Lemma so_adequacy' `{Layout: @memory_layout MP}
    (pc pc' : Word) (reg reg': Reg) (sreg sreg': SReg) (m m': Mem) (sh sh': ShadowTbl)
    (es: list griotte_lang.expr):
    is_initial_registers pc reg →
    is_initial_sregisters sreg →
    is_initial_memory m →
    sh = initial_heap_shadow →
    initial_heap_memory ##ₘ mk_initial_program_memory →
    rtc erased_step ([Seq (Instr Executable)], (pc, reg, sreg, m, sh)) (es, (pc', reg', sreg', m', sh')) →
    m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
  Proof.
    intros Hreg Hsreg Hm Hshadow_initial Hheap_disjoint Hstep.
    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl & main_static
                    & C_imports & C_code & C_data & C_exp_tbl & C_static
                    & Hstack
                   ).
    set (C_f := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt)).
    set (C_g := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt ^+ 1)%a).
    set (SO_f := cmpt_export main_cmpt (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a).
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as HC_exp_tbl_size.
    rewrite C_exp_tbl /= in HC_exp_tbl_size.

    (* Iris adequacy: the program-logic resources of the initial state *)
    eapply (cerise_flag_adequacy Σ (ot_switcher switcher_cmpt) [(C_f, 0); (C_g, 2); (SO_f, 2)]
              flagN (flag_assert assert_cmpt) ∅);
      [| by repeat constructor | | | | exact Hstep].
    { assert (C_f ≠ C_g) by (intros ?; simplify_eq; solve_addr).
      assert (C_f ≠ SO_f) by apply not_eq_sym, cmpt_export_disjoint, cmpts_disjoints.
      assert (C_g ≠ SO_f) by apply not_eq_sym, cmpt_export_disjoint, cmpts_disjoints.
      cbn; repeat (apply NoDup_cons; split); try apply NoDup_nil; set_solver.
    }
    { (* No allocator: the initial configuration has no heap root. *)
      subst sh m.
      apply (ghost_init_cond_initial_layout switcher_cmpt assert_cmpt main_cmpt
             [main_cmpt; C_cmpt]);
        [done | exact Hheap_disjoint | exact Hreg | exact Hsreg | exact Hstack |
         | eapply (mem_exec_ok_initial_cmpts switcher_cmpt assert_cmpt);
             [exact Hheap_disjoint | solve_initial_exec_cmpts] ].
      repeat constructor.
      - apply mem_rooted_initial_cmpt.
        + rewrite main_imports. repeat constructor; apply word_rooted_not_heap_cap.
          * apply switcher_call_sentry_not_heap.
          * rewrite /is_heap_cap /heap_cap_base /memory_cap_base /=.
            by rewrite (assert_code_nonheap assert_cmpt).
          * apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
        + rewrite main_code /so_main_code /SO_main_code_run /SO_main_code_f !Forall_app.
          repeat split; (apply word_rooted_instrs || apply Forall_nil_2).
        + rewrite main_data /so_main_data. apply Forall_nil_2.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite main_exp_tbl /so_export_table_entries. apply Forall_singleton.
          rewrite /so_exp_tbl_entry_f. apply word_rooted_int.
      - apply mem_rooted_initial_cmpt.
        + rewrite C_imports. repeat constructor; apply word_rooted_not_heap_cap.
          * exact switcher_call_sentry_not_heap.
          * apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
          * apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
        + by apply word_rooted_ints.
        + eapply Forall_impl; first exact C_data.
          intros w Hw. by eapply word_rooted_initial_data.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite C_exp_tbl. repeat constructor; apply word_rooted_int. }
    { destruct Hreg as (_&_&_&Hr). apply Hr. set_solver. }
    iIntros (ceriseg) "HPC Hreg Hsreg Hmem _ _ Hna
                       ([#Hentry_Cf #Hentry_Cf'] & [#Hentry_Cg #Hentry_Cg'] & [#Hentry_SOf #Hentry_SOf'] & _)".
    (* Use the non-atomic invariant pool of [ceriseg] *)
    clear na_invg.
    iMod (initialise_world [C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_interp_C _])";
      [done | apply NoDup_singleton |].

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first (apply lookup_delete_Some; split; [|exact (Hsreg MTDC)]; done).

    (* Separate all compartments *)
    rewrite Hm /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[_ Hmem]"; first exact Hheap_disjoint.
    rewrite /mk_initial_program_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* Assert *)
    iMod ( initialise_assert_compartment (Σ := Σ) _ flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* Switcher *)
    rewrite big_sepS_singleton.
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & #Hswitcher_static & Hstack)".

    (* CMPT C *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & _ & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".

    (* CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & _ & _ & Hmain_etbl_pcc & Hmain_etbl_cgp & Hmain_etbl_entries)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    rewrite main_code main_exp_tbl /so_export_table_entries.
    pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hmain_exp_tbl_size.
    rewrite main_exp_tbl /= in Hmain_exp_tbl_size.
    iAssert ((cmpt_exp_tbl_entries_start main_cmpt) ↦ₐ
               WInt (encode_entry_point InterruptEnabled 2 (length (cmpt_imports main_cmpt ++ SO_main_code_run))))%I
      with "[Hmain_etbl_entries]" as "Hmain_etbl_entries".
    { rewrite /region_pointsto
        (finz_seq_between_singleton (cmpt_exp_tbl_entries_start main_cmpt)); last done.
      rewrite main_imports.
      by rewrite big_sepL2_singleton.
    }
    rewrite main_imports (cmpt_exp_tbl_entries_start_eq main_cmpt) (cmpt_exp_tbl_cgp_eq main_cmpt).
    iMod (region_pointsto_persist with "Hmain_imports") as "#Hmain_imports".
    iMod (codefrag_persist with "Hmain_code") as "#Hmain_code".
    iMod (pointsto_persist with "Hmain_etbl_pcc") as "#Hinv_etbl_PCC".
    iMod (pointsto_persist with "Hmain_etbl_cgp") as "#Hinv_etbl_CGP".
    iMod (pointsto_persist with "Hmain_etbl_entries") as "#Hinv_etbl_entry_awkward".
    assert (cmpt_exp_tbl_pcc main_cmpt <= cmpt_exp_tbl_pcc main_cmpt ^+ 2
            < cmpt_exp_tbl_entries_end main_cmpt)%a as Hmain_exp_tbl_bounds.
    { pose proof (cmpt_exp_tbl_entries_start_eq main_cmpt).
      pose proof (cmpt_exp_tbl_pcc_size main_cmpt).
      solve_addr. }
    (* Seal the exported entry of the main compartment with [ot_switcher] in
       the world *)
    set (W0 := (∅, (∅, ∅), ∅, ∅) : WORLD).
    set (W0' := <o[ ot_switcher switcher_cmpt :=
                    {[ lword_of_word (WSealable SO_f);
                       lword_of_word (borrow (WSealable SO_f)) ]} ]o> W0).
    iAssert (ot_switcher_prop W0' C (WSealable SO_f)) as "#Hot_switcher_SO_f".
    { assert (is_Some (cmpt_b_pcc main_cmpt +
                         length (so_main_imports
                                   (SCap true RO Global (cmpt_exp_tbl_pcc C_cmpt)
                                      (cmpt_exp_tbl_entries_end C_cmpt)
                                      (cmpt_exp_tbl_entries_start C_cmpt))
                                 ++ SO_main_code_run))%a)
        as Hentry_some.
      { pose proof (cmpt_code_size main_cmpt) as Hcode_size.
        rewrite main_code /so_main_code length_app in Hcode_size.
        rewrite length_app.
        solve_addr+Hmain_imports_size Hcode_size. }
      iApply (stack_object_f_spec _ _ _ _ _ _ _ _ _ W0' switcherN);
        last iFrame "#"; auto.
      { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
      { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
      { exact (cmpt_pcc_base_not_heap main_cmpt). }
      { exact (cmpt_cgp_base_not_heap main_cmpt). } }
    iMod (seal_main_export W0 C SO_f
           with "Hsealed_pred_ot_switcher Hot_switcher_SO_f Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_SO)"; [done| |done|].
    { intros ????? Heq; inversion Heq; subst.
      apply cmpt_exp_tbl_disjoint_from_heap. }

    (* Initialises the world for C *)
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_C).
    iMod (initialise_adversary_world W0' switcher_cmpt _ C
           with "Hsealed_pred_ot_switcher HC_imports HC_code HC_data Hstack [] [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & #Hinterp_stack_C & #HC_exports)";
      [auto..| | |].
    { (* The exported entries C.f and C.g satisfy the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(InterruptEnabled, 0, offset_adv_f); (InterruptEnabled, 2, offset_adv_g)]
               with "Hswitcher Hswitcher_static HC_etbl_pcc HC_etbl_cgp HC_etbl_entries");
        [by rewrite C_exp_tbl | by repeat constructor |
         by apply Forall_cons; split;
           [apply offset_adv_f_valid | apply Forall_singleton, offset_adv_g_valid] |].
      rewrite /= finz_add_0_default.
      iFrame "Hentry_Cf Hentry_Cf' Hentry_Cg Hentry_Cg'".
    }
    { rewrite C_imports.
      iIntros "(#Hpcc_interp & #Hcgp_interp & #Hexports)".
      (* Switcher cross-compartment *)
      iSplit.
      { assert (heap_authority_base
          (WSentry FwdDisable true XSRW_ Local (b_switcher switcher_cmpt)
            (e_switcher switcher_cmpt) (a_switcher_call switcher_cmpt)) = None) as Hcall_nonheap.
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
      (* SO.f *)
      iSplit.
      { iSplit.
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
          done.
      }
      (* C.g *)
      iSplit; last done.
      iSplit.
      { iApply interp_to_in_mem.
        iApply (adversary_export_interp _ _ _ 1 with "Hexports").
        - done.
        - rewrite C_exp_tbl /=; lia. }
      iIntros (W2 W3) "!> %Hrelated Hinterp".
      iEval (cbn) in "Hinterp".
      iApply (interp_in_mem_monotone_nl W2 W3 C RWL with "Hinterp"); first exact Hrelated.
      done.
    }
    iAssert (interp (adv_world W0' switcher_cmpt C_cmpt) C
               (WSealed (ot_switcher switcher_cmpt) C_f)) as "#Hinterp_C_f".
    { iApply (adversary_export_interp _ _ _ 0 with "HC_exports").
      - solve_addr.
      - rewrite C_exp_tbl /=; lia.
    }

    (* Extract registers *)
    iDestruct (initial_registers_split with "[$HPC $Hreg]")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.

    iPoseProof (@so_init_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ C
                  _ _ _ _ _ _ _ _
                  _ (cmpt_exp_tbl_entries_end main_cmpt)
                  _ _ [] [] switcherN
                 with "[ $Hassert $Hswitcher $Hswitcher_static $Hmain_imports $Hmain_code
                         $Hinv_etbl_PCC $Hinv_etbl_CGP $Hinv_etbl_entry_awkward
                         $Hna
                         $Hworld_interp_C
                         $HPC $Hcgp $Hcsp $Hrmap
                         $Hcstk_frag $Hinterp_stack_C
                         $Hinterp_C_f $Hentry_Cf $Hentry_SOf $Hentry_SOf'
                         $Hsealed_pred_ot_switcher
                        ]") as "Hspec"; eauto.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { done. }

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End Adequacy.

Inductive CmptNames_so := | B .
#[local] Instance CmptNames_so_eq_dec : EqDecision CmptNames_so.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
#[local] Instance CmptNames_so_finite : finite.Finite CmptNames_so.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

#[local] Program Instance CmptNames_so_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_so; |}.

(** END-TO-END THEOREM *)
Theorem so_adequacy `{Layout: memory_layout}
  (pc pc' : Word) (reg reg': Reg) (sreg sreg': SReg) (m m': Mem) (sh sh': ShadowTbl)
  (es: list griotte_lang.expr)
  :
  is_initial_registers pc reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
    sh = initial_heap_shadow →
    initial_heap_memory ##ₘ mk_initial_program_memory →
  rtc erased_step ([Seq (Instr Executable)], (pc, reg, sreg, m, sh)) (es, (pc', reg', sreg', m', sh')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ? ? ?.
  set ( cnames := CmptNames_so_CmptNameG ).
  set (Σ := #[invΣ
              ; ceriseGpreΣ
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ LAddr region_type OType LWord ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * LWord)
      ]).
  eapply (@so_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
