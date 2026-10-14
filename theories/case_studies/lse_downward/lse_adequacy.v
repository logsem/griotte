From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import lse lse_spec_closure lse_spec.
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
    offset_adv_f_valid :
      is_Some (cmpt_b_pcc C_cmpt + offset_adv_f%nat)%a;

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

Local Instance memory_layout_switcherLayout `{memory_layout} : switcherLayout.
Proof.
  exact (cmptSwitcher_switcherLayout switcher_cmpt).
Defined.

Local Instance memory_layout_switcherLayoutWf `{memory_layout} : switcherLayoutWf.
Proof.
  pose proof (ot_switcher_size switcher_cmpt).
  pose proof (switcher_size switcher_cmpt).
  pose proof (switcher_call_entry_point switcher_cmpt).
  pose proof (switcher_return_entry_point switcher_cmpt).
  pose proof (trusted_stack_disjoint_from_shadow switcher_cmpt).
  pose proof (switcher_base_not_shadow switcher_cmpt).
  pose proof (compartment_layout.switcher_not_heap_range switcher_cmpt).
  refine (mkSwitcherLayoutWf _ _ _ _ _ _ _ _); cbn in *; auto.
Defined.

Local Instance memory_layout_assertLayout `{memory_layout} : assertLayout.
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
    WSentry true XSRW_ Local
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

  mem = mk_initial_memory
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = lse_main_imports C_f
  ∧ (cmpt_code main_cmpt) = lse_main_code
  ∧ (cmpt_data main_cmpt) = lse_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = lse_export_table_entries
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed main_cmpt)

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) =
  [switcher_entry
   ; WSealed ot_switcher (lse_entry_f_sb (cmpt_exp_tbl_pcc main_cmpt)
                            (cmpt_exp_tbl_entries_end main_cmpt))
  ]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point 0 offset_adv_f)]
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

  Definition flagN : namespace := nroot .@ "lse" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "lse" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "lse" .@ "assert_flag".
  Definition lseN : namespace := nroot .@ "lse" .@ "code".

  Lemma lse_adequacy' `{Layout: @memory_layout MP}
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
    set (main_f := cmpt_export main_cmpt (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a).

    (* Iris adequacy: the program-logic resources of the initial state *)
    eapply (cerise_flag_adequacy Σ (ot_switcher switcher_cmpt) [(C_f, 0); (main_f, 0)]
              flagN (flag_assert assert_cmpt) ∅);
      [| by repeat constructor | | | | exact Hstep].
    { cbn; apply NoDup_cons; split; last apply NoDup_singleton.
      rewrite list_elem_of_singleton.
      apply not_eq_sym, cmpt_export_disjoint, cmpts_disjoints.
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
        + rewrite main_code /lse_main_code /LSE_main_code_run /LSE_main_code_f
            !Forall_app.
          repeat split; (apply word_rooted_instrs || apply Forall_nil_2).
        + rewrite main_data /lse_main_data. repeat constructor; apply word_rooted_int.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite main_exp_tbl /lse_export_table_entries. apply Forall_singleton.
          rewrite /lse_exp_tbl_entry_f. apply word_rooted_int.
      - apply mem_rooted_initial_cmpt.
        + rewrite C_imports. repeat constructor; apply word_rooted_not_heap_cap.
          * exact switcher_call_sentry_not_heap.
          * apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
        + by apply word_rooted_ints.
        + eapply Forall_impl; first exact C_data.
          intros w Hw. by eapply word_rooted_initial_data.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite C_exp_tbl. repeat constructor; apply word_rooted_int. }
    { destruct Hreg as (_&_&_&Hr). apply Hr. set_solver. }
    iIntros (ceriseg) "HPC Hreg Hsreg Hmem _ _ Hna ([#Hentry_Cf #Hentry_Cf'] & [#Hentry_mainf #Hentry_mainf'] & _)".
    (* Use the non-atomic invariant pool of [ceriseg] *)
    clear na_invg.
    iMod (initialise_world [C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_interp_C _])";
      [done | apply NoDup_singleton |].

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.

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
      as "(Hmain_imports & Hmain_code & Hmain_data & _ & Hmain_etbl_pcc & Hmain_etbl_cgp & Hmain_etbl_entries)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    iDestruct (region_pointsto_single with "Hmain_data") as "[%v [Hcgp_b %Hv] ]".
    { solve_addr+Hmain_data_size. }
    rewrite main_data /lse_main_data /= in Hv; simplify_eq.
    rewrite main_imports main_code main_exp_tbl /lse_export_table_entries.
    pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hmain_exp_tbl_size.
    rewrite main_exp_tbl /= in Hmain_exp_tbl_size.
    iEval (rewrite /region_pointsto
             (finz_seq_between_singleton (cmpt_exp_tbl_entries_start main_cmpt));
           last done; rewrite big_sepL2_singleton) in "Hmain_etbl_entries".
    rewrite (cmpt_exp_tbl_entries_start_eq main_cmpt) (cmpt_exp_tbl_cgp_eq main_cmpt).
    iMod (region_pointsto_persist with "Hmain_imports") as "#Hmain_imports".
    iMod (codefrag_persist with "Hmain_code") as "#Hmain_code".
    iMod (na_inv_alloc cerise_nais _ lseN _ with "Hcgp_b") as "#Hlse_data".
    iMod (pointsto_persist with "Hmain_etbl_pcc") as "#Hinv_etbl_PCC".
    iMod (pointsto_persist with "Hmain_etbl_cgp") as "#Hinv_etbl_CGP".
    iMod (pointsto_persist with "Hmain_etbl_entries") as "#Hinv_etbl_entry_f".
    assert (cmpt_exp_tbl_pcc main_cmpt <= cmpt_exp_tbl_pcc main_cmpt ^+ 2
            < cmpt_exp_tbl_entries_end main_cmpt)%a as Hmain_exp_tbl_bounds.
    { pose proof (cmpt_exp_tbl_entries_start_eq main_cmpt).
      pose proof (cmpt_exp_tbl_pcc_size main_cmpt).
      solve_addr. }

    (* Seal the exported entry of the main compartment with [ot_switcher] in
       the world *)
    set (W0 := (∅, (∅, ∅), ∅, ∅) : WORLD).
    set (W0' := <o[ ot_switcher switcher_cmpt :=
                    {[ lword_of_word (WSealable main_f);
                       lword_of_word (borrow (WSealable main_f)) ]} ]o> W0).
    iAssert (ot_switcher_prop W0' C (WSealable main_f)) as "#Hot_switcher_main_f".
    { assert (is_Some (cmpt_b_pcc main_cmpt +
                         (length_lse_main_imports + length LSE_main_code_run))%a)
        as Hentry_some.
      { pose proof (cmpt_code_size main_cmpt) as Hcode_size.
        rewrite main_code /lse_main_code /LSE_main_code_run /LSE_main_code_f /= in Hcode_size.
        rewrite /lse_main_imports /= in Hmain_imports_size.
        rewrite /length_lse_main_imports /lse_main_imports /LSE_main_code_run /=.
        solve_addr+Hmain_imports_size Hcode_size. }
      iApply (lse_f_spec _ _ _ _ _ _ _ _ _ W0' switcherN lseN);
        last iFrame "#"; auto.
      { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
      { eapply disjoint_from_shadow_not_in;
          first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
        apply withinBounds_true_iff; cbn in Hmain_data_size; solve_addr. }
      { exact (cmpt_cgp_base_not_heap main_cmpt). }
      { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
      { exact (cmpt_pcc_base_not_heap main_cmpt). }
      all: rewrite /switcherN /lseN; solve_ndisj. }
    iMod (seal_main_export W0 C main_f
           with "Hsealed_pred_ot_switcher Hot_switcher_main_f Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_LSE)"; [done| |done|].
    { intros ????? Heq; inversion Heq; subst.
      apply cmpt_exp_tbl_disjoint_from_heap. }

    (* Initialises the world for C *)
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_C).
    iMod (initialise_adversary_world W0' switcher_cmpt _ C
           with "Hsealed_pred_ot_switcher HC_imports HC_code HC_data Hstack [] [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & #Hinterp_stack_C & #HC_exports)";
      [auto..| | |].
    { (* The exported entry C.f satisfies the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(0, offset_adv_f)]
               with "Hswitcher Hswitcher_static HC_etbl_pcc HC_etbl_cgp HC_etbl_entries");
        [by rewrite C_exp_tbl | by repeat constructor |
         by apply Forall_singleton, offset_adv_f_valid |].
      rewrite /= finz_add_0_default; iFrame "Hentry_Cf Hentry_Cf'".
    }
    { rewrite C_imports.
      iIntros "(#Hpcc_interp & #Hcgp_interp & _)".
      iSplit.
      { assert (heap_authority_base
          (WSentry true XSRW_ Local (b_switcher switcher_cmpt)
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
      iSplit; last done.
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
        by rewrite /lse_entry_f_sb.
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

    iPoseProof (@lse_run_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ C
                  _ _ _ _ _ _ _ _
                  _ (cmpt_exp_tbl_entries_end main_cmpt)
                  _ _ [] [] switcherN lseN
                 with "[ $Hassert $Hswitcher $Hswitcher_static
                         $Hmain_imports $Hmain_code $Hlse_data
                         $Hinv_etbl_PCC $Hinv_etbl_CGP $Hinv_etbl_entry_f
                         $Hna
                         $Hworld_interp_C
                         $HPC $Hcgp $Hcsp $Hrmap
                         $Hcstk_frag $Hinterp_stack_C
                         $Hinterp_C_f $Hentry_Cf $Hentry_mainf $Hentry_mainf'
                         $Hsealed_pred_ot_switcher
                        ]") as "Hspec"; eauto.
    { exact (cmpt_pcc_disjoint_from_shadow main_cmpt). }
    { eapply disjoint_from_shadow_not_in;
        first exact (cmpt_cgp_disjoint_from_shadow main_cmpt).
      apply withinBounds_true_iff; cbn in Hmain_data_size; solve_addr. }
    { exact (cmpt_cgp_base_not_heap main_cmpt). }
    { exact (cmpt_exp_tbl_disjoint_from_shadow main_cmpt). }
    { exact (cmpt_pcc_base_not_heap main_cmpt). }
    { solve_ndisj. }
    all: try (apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap).
    all: try done.

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End Adequacy.

Inductive CmptNames_lse := | B .
Local Instance CmptNames_lse_eq_dec : EqDecision CmptNames_lse.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_lse_finite : finite.Finite CmptNames_lse.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_lse_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_lse; |}.

(** END-TO-END THEOREM *)
Theorem lse_adequacy `{Layout: memory_layout}
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
  set ( cnames := CmptNames_lse_CmptNameG ).
  set (Σ := #[invΣ
              ; ceriseGpreΣ
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ LAddr region_type OType LWord; relPreΣ
              ; savedPredΣ (WorldT * CmptName * LWord)
      ]).
  eapply (@lse_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
