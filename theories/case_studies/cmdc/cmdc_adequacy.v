From iris.proofmode Require Import proofmode.
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


(** We define the memory layout typeclass,
    which describes the initial memory layout.

    It contains:
    - the switcher compartment
    - the assert compartment
    - the main compartment
    - the adversaries compartments (B and C for the CMDC)

    And it describes that all the compartments are disjoints from each others. *)
Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adv compartments B and C *)
    B_cmpt : cmpt ;
    offset_B_f : nat;
    offset_B_f_valid :
      is_Some (cmpt_b_pcc B_cmpt + offset_B_f%nat)%a;
    C_cmpt : cmpt ;
    offset_C_g : nat;
    offset_C_g_valid :
      is_Some (cmpt_b_pcc C_cmpt + offset_C_g%nat)%a;

    (* disjointness *)
    cmpts_disjoints :
    main_cmpt ## B_cmpt
    ∧ main_cmpt ## C_cmpt
    ∧ B_cmpt ## C_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint main_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint B_cmpt switcher_cmpt
    ∧ switcher_cmpt_disjoint C_cmpt switcher_cmpt ;

    assert_cmpt_disjoints :
    assert_cmpt_disjoint main_cmpt assert_cmpt
    ∧ assert_cmpt_disjoint B_cmpt assert_cmpt
    ∧ assert_cmpt_disjoint C_cmpt assert_cmpt ;

    assert_switcher_disjoints :
    assert_switcher_disjoint assert_cmpt switcher_cmpt;
  }.
#[export] Hint Mode memory_layout - : typeclass_instances.


(** We instantiate the switcher and assert layout with the memory layout. *)
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
    mk_initial_cmpt B_cmpt ∪
    mk_initial_cmpt C_cmpt.


(** We describe the initial register file. *)
(** Initial allocator memory is separate from all compartment resources. *)
Definition mk_initial_memory `{memory_layout} : Mem :=
  initial_heap_memory ∪ mk_initial_program_memory.

(** We describe the initial register file. *)
Definition is_initial_registers `{memory_layout} := is_initial_registers_of switcher_cmpt main_cmpt.

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{@memory_layout MP} := is_initial_sregisters_of switcher_cmpt.

(** We describe the initial memory. *)
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
  let B_f :=
    SCap true RO Global
      (cmpt_exp_tbl_pcc B_cmpt)
      (cmpt_exp_tbl_entries_end B_cmpt)
      (cmpt_exp_tbl_entries_start B_cmpt)
  in
  let C_g :=
    SCap true RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      (cmpt_exp_tbl_entries_start C_cmpt)
  in

  mem = mk_initial_memory
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = cmdc_main_imports B_f C_g
  ∧ (cmpt_code main_cmpt) = cmdc_main_code
  ∧ (cmpt_data main_cmpt) = cmdc_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed main_cmpt)

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point cmdc_B_f_args offset_B_f)]
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed B_cmpt)

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point cmdc_C_g_args offset_C_g)]
  ∧ Forall (λ w, is_heap_cap w = false ∧ executable_word w = false) (cmpt_static_sealed C_cmpt)

  (* initial stack *)
  ∧ Forall is_z (stack_content switcher_cmpt)
.

(** We derive some disjointness properties *)
Lemma mk_initial_cmpt_C_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt ∪ mk_initial_cmpt B_cmpt
    ##ₘ mk_initial_cmpt C_cmpt.
Proof.
  pose proof cmpts_disjoints as (_ & HmainC & HBC).
  pose proof switcher_cmpt_disjoints as (_ & _ & HswitcherC).
  pose proof assert_cmpt_disjoints as (_ & _ & HassertC).
  do 3 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_B_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as (HmainB & _ & _).
  pose proof switcher_cmpt_disjoints as (_ & HswitcherB & _).
  pose proof assert_cmpt_disjoints as (_ & HassertB & _).
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
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _ & _).
  pose proof assert_cmpt_disjoints as (HassertMain & _ & _).
  rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
Qed.

(** We prove that, in the initial configuration,
    at any step of execution, the assert flag contains 0
    (which means that assert never failed).

    We start by showing an helper lemma [cmdc_adequacy'] that pre-initialises
    Iris typeclasses, as well as the compartment names. *)
Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {B C : CmptName}.
  Context {inv_preg: invGpreS Σ}.
  Context {cerise_preg : ceriseGpreS Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invariants.na_invG Σ}.
  Context {sts_preg: STS_preG LAddr region_type OType LWord Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.

  Definition flagN : namespace := nroot .@ "cmdc" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "cmdc" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "cmdc" .@ "assert_flag".


  Lemma cmdc_adequacy' `{Layout: @memory_layout MP}
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
                    & B_imports & B_code & B_data & B_exp_tbl & B_static
                    & C_imports & C_code & C_data & C_exp_tbl & C_static
                    & Hstack
                   ).
    pose proof cmpts_disjoints as (HmainB & HmainC & HBC).

    (* 1 - We give a name to the exported entry points for which we want
       to know the number of arguments. *)
    set (B_f := cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)).
    set (C_g := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt)).

    (* 2 - We use the Iris adequacy theorem, which initialises the program
       logic resources: registers, memory, entry points and NA invariants. *)
    eapply (cerise_flag_adequacy Σ (ot_switcher switcher_cmpt)
              [(B_f, cmdc_B_f_args); (C_g, cmdc_C_g_args)]
              flagN (flag_assert assert_cmpt) ∅);
      [| by repeat constructor | | | | exact Hstep].
    { cbn; apply NoDup_cons; split; last apply NoDup_singleton.
      rewrite list_elem_of_singleton.
      by apply cmpt_export_disjoint.
    }
    { (* No allocator: the initial configuration has no heap root. *)
      subst sh m.
      apply (ghost_init_cond_initial_layout switcher_cmpt assert_cmpt main_cmpt
             [main_cmpt; B_cmpt; C_cmpt]);
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
          * apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap.
        + rewrite main_code /cmdc_main_code !Forall_app.
          repeat split; apply word_rooted_instrs.
        + rewrite main_data /cmdc_main_data. repeat constructor; apply word_rooted_int.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite main_exp_tbl. apply Forall_nil_2.
      - apply mem_rooted_initial_cmpt.
        + rewrite B_imports. repeat constructor; apply word_rooted_not_heap_cap.
          exact switcher_call_sentry_not_heap.
        + by apply word_rooted_ints.
        + eapply Forall_impl; first exact B_data.
          intros w Hw. by eapply word_rooted_initial_data.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite B_exp_tbl. repeat constructor; apply word_rooted_int.
      - apply mem_rooted_initial_cmpt.
        + rewrite C_imports. repeat constructor; apply word_rooted_not_heap_cap.
          exact switcher_call_sentry_not_heap.
        + by apply word_rooted_ints.
        + eapply Forall_impl; first exact C_data.
          intros w Hw. by eapply word_rooted_initial_data.
        + apply word_rooted_not_heap_caps.
          eapply Forall_impl; first done. by intros ? [? _].
        + rewrite C_exp_tbl. repeat constructor; apply word_rooted_int. }
    { destruct Hreg as (_&_&_&Hr). apply Hr. set_solver. }
    iIntros (ceriseg) "HPC Hreg Hsreg Hmem _ _ Hna ([#Hentry_Bf #Hentry_Bf'] & [#Hentry_Cg #Hentry_Cg'] & _)".

    (* 3 - We initialise the seal store, the call stack and the world
       interpretations of B and C *)
    iMod (initialise_world [B;C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg)
           "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_interp_B [Hworld_interp_C _]])";
      [done | exact HCNamesNoDup |].

    (* 4 - Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact (Hsreg MTDC).

    (* 5 - Separate all compartments *)
    rewrite Hm /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[_ Hmem]"; first exact Hheap_disjoint.
    rewrite /mk_initial_program_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* 5.1 Assert compartment *)
    iMod ( initialise_assert_compartment (Σ := Σ) _ flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* 5.2 Switcher compartment *)
    rewrite big_sepS_singleton.
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & #Hswitcher_static & Hstack)".

    (* 5.3 CMPT B *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & _ & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".

    (* 5.4 CMPT C *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & _ & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".

    (* 5.5 CMPT MAIN *)
    iMod (initialise_compartment_pers (Σ := Σ) with "Hcmpt_main")
      as "(#Hmain_imports & #Hmain_code & Hmain_data & _ & _ & _ & _)".
    rewrite main_imports main_code main_data.

    (* 6 - Initialise the worlds of B and C: their compartments become
       permanent, and the stack is allocated as revoked, because we keep
       its points-to predicates. *)
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_B & Hsw_C).
    iMod (initialise_adversary_world_revoked _ switcher_cmpt _ B
           with "Hsealed_pred_ot_switcher HB_imports HB_code HB_data [] [] Hworld_interp_B")
      as "(Hworld_interp_B & #Hinterp_pcc_B & #Hinterp_cgp_B & Hrevoked_stack_B & #HB_exports)";
      [auto..| | |].
    { (* The exported entry B.f satisfies the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(cmdc_B_f_args, offset_B_f)]
               with "Hswitcher Hswitcher_static HB_etbl_pcc HB_etbl_cgp HB_etbl_entries");
        [by rewrite B_exp_tbl | by repeat constructor |
         by apply Forall_singleton, offset_B_f_valid |].
      rewrite /= finz_add_0_default; iFrame "Hentry_Bf Hentry_Bf'".
    }
    { rewrite B_imports.
      iIntros "_".
      iSplit; last done.
      assert (heap_authority_base
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
      { iIntros "!>" (W W' Hrel) "H".
        iEval (rewrite /interp_in_mem_pre /=).
        rewrite filter_heap_nonheap; last exact Hcall_nonheap.
        iApply interp_switcher_call; iFrame "Hswitcher Hswitcher_static". }
    }
    iMod (initialise_adversary_world_revoked _ switcher_cmpt _ C
           with "Hsealed_pred_ot_switcher HC_imports HC_code HC_data [] [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & Hrevoked_stack_C & #HC_exports)";
      [auto..| | |].
    { (* The exported entry C.g satisfies the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(cmdc_C_g_args, offset_C_g)]
               with "Hswitcher Hswitcher_static HC_etbl_pcc HC_etbl_cgp HC_etbl_entries");
        [by rewrite C_exp_tbl | by repeat constructor |
         by apply Forall_singleton, offset_C_g_valid |].
      rewrite /= finz_add_0_default; iFrame "Hentry_Cg Hentry_Cg'".
    }
    { rewrite C_imports.
      iIntros "_".
      iSplit; last done.
      assert (heap_authority_base
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
      { iIntros "!>" (W W' Hrel) "H".
        iEval (rewrite /interp_in_mem_pre /=).
        rewrite filter_heap_nonheap; last exact Hcall_nonheap.
        iApply interp_switcher_call; iFrame "Hswitcher Hswitcher_static". }
    }

    (* 7 - The exported entry points of B and C are safe to share *)
    iAssert (interp (adv_world_revoked (∅, (∅, ∅), ∅, ∅) switcher_cmpt B_cmpt) B
               (WSealed (ot_switcher switcher_cmpt) B_f)) as "#Hinterp_B".
    { iApply (adversary_export_interp _ _ _ 0 with "HB_exports").
      - solve_addr.
      - rewrite B_exp_tbl /=; lia.
    }
    iAssert (interp (adv_world_revoked (∅, (∅, ∅), ∅, ∅) switcher_cmpt C_cmpt) C
               (WSealed (ot_switcher switcher_cmpt) C_g)) as "#Hinterp_C".
    { iApply (adversary_export_interp _ _ _ 0 with "HC_exports").
      - solve_addr.
      - rewrite C_exp_tbl /=; lia.
    }

    (* 8 - Extract registers *)
    iDestruct (initial_registers_split with "[$HPC $Hreg]")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).

    (* 9 - We can apply the specification! *)
    assert (is_mmio_address (cmpt_b_cgp main_cmpt) = false) as Hmain_shadow.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio main_cmpt).
      apply withinBounds_true_iff.
      pose proof (cmpt_data_size main_cmpt) as Hsize.
      rewrite main_data in Hsize; cbn in Hsize; solve_addr+Hsize. }
    assert (is_mmio_address (cmpt_b_cgp main_cmpt ^+ 1)%a = false) as Hmain1_shadow.
    { eapply disjoint_from_mmio_not_in;
        first exact (cmpt_cgp_disjoint_from_mmio main_cmpt).
      apply withinBounds_true_iff.
      pose proof (cmpt_data_size main_cmpt) as Hsize.
      rewrite main_data in Hsize; cbn in Hsize; solve_addr+Hsize. }
    assert (is_heap_address (cmpt_b_cgp main_cmpt ^+ 1)%a = false) as Hmain1_heap.
    { eapply disjoint_from_heap_not_in;
        first exact (cmpt_cgp_disjoint_from_heap main_cmpt).
      apply withinBounds_true_iff.
      pose proof (cmpt_data_size main_cmpt) as Hsize.
      rewrite main_data in Hsize; cbn in Hsize; solve_addr+Hsize. }
    iModIntro; iFrame "Hassert_flag".
    iApply (@cmdc_spec_full Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ B C
              _ _ _ _ _ _ _
              _ _ _ _ _
              [] [] _ (fun _ => True)%I switcherN []
              (cmpt_pcc_disjoint_from_shadow main_cmpt)
              (cmpt_pcc_base_not_heap main_cmpt)
              Hmain_shadow (cmpt_cgp_base_not_heap main_cmpt)
              Hmain1_shadow Hmain1_heap
              (stack_disjoint_from_mmio switcher_cmpt)
              (stack_disjoint_from_heap switcher_cmpt)
             with "[ $Hassert $Hswitcher $Hswitcher_static $Hna
                    $Hworld_interp_B $Hworld_interp_C
                    $HPC $Hcgp $Hcsp $Hrmap
                    $Hmain_imports $Hmain_code $Hmain_data $Hstack
                    $Hinterp_B $Hinterp_C $Hcstk_frag $Hrevoked_stack_B $Hrevoked_stack_C
                    $Hentry_Bf $Hentry_Cg
                    ]"); eauto.
    { apply (main_cgp_not_in_adv_world _ _ _ main_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply (main_cgp_not_in_adv_world _ _ _ main_cmpt); [done | done | | ].
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { apply sealed_cap_nonheap, cmpt_exp_tbl_base_not_heap. }
    { rewrite /revoked_addresses /adv_world_with Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    { rewrite /revoked_addresses /adv_world_with Forall_forall.
      intros a Ha.
      by apply std_sta_update_multiple_lookup_in_i.
    }
    iNext; iIntros "H". proofmode.wp_end; by iIntros.
  Qed.
End Adequacy.


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

(** END-TO-END THEOREM *)
Theorem cmdc_adequacy `{Layout: memory_layout}
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
  intros ? ? ? ? ? ?.
  set ( cnames := CmptNames_CMDC_CmptNameG ).
  set (Σ := #[invΣ
              ; ceriseGpreΣ
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ LAddr region_type OType LWord ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * LWord)
      ]).
  eapply (@cmdc_adequacy' Σ cnames B C); eauto; try typeclasses eauto.
  apply NoDup_cons; split ; [set_solver | apply NoDup_singleton].
Qed.
