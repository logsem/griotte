From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import deep_immutability deep_immutability_spec.
From griotte Require Import switcher assert_spec logrel.
From griotte Require Import mkregion_helpers.
From griotte Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From griotte Require Import disjoint_regions_tactics.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import compartment_layout switcher_adequacy adequacy_helpers adequacy_common.

Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adv compartments C *)
    C_cmpt : cmpt ;

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
  refine (mkSwitcherLayoutWf _ _ _ _ _); cbn in *; auto.
Defined.

Local Instance memory_layout_assertLayout `{memory_layout} : assertLayout.
Proof.
  exact (cmptAssert_assertLayout assert_cmpt).
Defined.

Definition mk_initial_memory `{memory_layout} :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt C_cmpt.


Definition is_initial_registers `{memory_layout} := is_initial_registers_of switcher_cmpt main_cmpt.

Definition is_initial_sregisters `{@memory_layout MP} := is_initial_sregisters_of switcher_cmpt.

Definition is_initial_memory `{@memory_layout MP} (mem: Mem) :=
  let b_switcher := (b_switcher switcher_cmpt) in
  let e_switcher := (e_switcher switcher_cmpt) in
  let a_switcher_call := (a_switcher_call switcher_cmpt) in
  let ot_switcher := (ot_switcher switcher_cmpt) in
  let switcher_entry :=
    WSentry XSRW_ Local
      b_switcher
      e_switcher
      a_switcher_call
  in
  let C_f :=
    SCap RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      (cmpt_exp_tbl_entries_start C_cmpt)
  in

  mem = mk_initial_memory
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = droe_main_imports C_f
  ∧ (cmpt_code main_cmpt) = droe_main_code
  ∧ (cmpt_data main_cmpt) = droe_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point 1 1)]

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
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [C]) }.

  Definition flagN : namespace := nroot .@ "droe" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "droe" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "droe" .@ "assert_flag".


  Lemma droe_adequacy' `{Layout: @memory_layout MP}
    (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
    (es: list griotte_lang.expr):
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory m →
    rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
    m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
  Proof.
    intros Hreg Hsreg Hm Hstep.
    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                    & Hstack
                   ).
    set (C_f := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt)).

    (* Iris adequacy: the program-logic resources of the initial state *)
    eapply (cerise_flag_adequacy Σ (ot_switcher switcher_cmpt) [(C_f, 1)]
              flagN (flag_assert assert_cmpt));
      [apply NoDup_singleton | by repeat constructor | | exact Hstep].
    iIntros (ceriseg) "Hreg Hsreg Hmem Hna [[#Hentry_Cf #Hentry_Cf'] _]".
    iMod (initialise_world [C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_interp_C _])";
      [done | apply NoDup_singleton |].

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.

    (* Separate all compartments *)
    rewrite Hm /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* Assert *)
    iMod ( initialise_assert_compartment (Σ := Σ) _ assertN flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* Switcher *)
    rewrite big_sepS_singleton.
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack)".

    (* CMPT C *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ C with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".

    (* CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data & _ & _ & _)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    rewrite main_imports main_code main_data.

    (* Initialises the world for C *)
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_C).
    iMod (initialise_adversary_world _ switcher_cmpt _ C
           with "HC_imports HC_code HC_data Hstack [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & #Hinterp_stack_C)"; auto.
    { rewrite C_imports.
      iIntros "_".
      iSplit; last done.
      iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done.
    }
    iAssert (interp (adv_world (∅, (∅, ∅)) switcher_cmpt C_cmpt) C
               (WSealed (ot_switcher switcher_cmpt) C_f)) as "#Hinterp_C".
    { iApply (adversary_export_interp _ _ _ _ _ 0 1 1
               with "Hswitcher Hsealed_pred_ot_switcher HC_etbl_pcc HC_etbl_cgp HC_etbl_entries
                     Hinterp_pcc_C Hinterp_cgp_C Hentry_Cf Hentry_Cf'").
      - by rewrite C_exp_tbl.
      - pose proof (cmpt_exp_tbl_entries_size C_cmpt); solve_addr.
      - lia.
    }

    (* Extract registers *)
    iDestruct (initial_registers_split with "Hreg")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).

    iPoseProof (@droe_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ C
                  _ _ _ _ _ _ _ _ _ _ [] [] assertN switcherN []
                 with "[ $Hassert $Hswitcher $Hna
                        $Hworld_interp_C
                        $HPC $Hcgp $Hcsp $Hrmap
                        $Hmain_imports $Hmain_code $Hmain_data
                        $Hinterp_C $Hcstk_frag
                        $Hentry_Cf $Hinterp_stack_C
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
    { apply (main_cgp_not_in_adv_world _ _ _ main_cmpt).
      - apply cmpts_disjoints.
      - done.
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { apply (main_cgp_not_in_adv_world _ _ _ main_cmpt).
      - apply cmpts_disjoints.
      - done.
      - rewrite /= dom_empty_L; set_solver+.
      - rewrite elem_of_finz_seq_between; solve_addr+Hmain_data_size.
    }
    { done. }

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End Adequacy.

Inductive CmptNames_droe := | B .
Local Instance CmptNames_droe_eq_dec : EqDecision CmptNames_droe.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_droe_finite : finite.Finite CmptNames_droe.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_droe_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_droe; |}.

(** END-TO-END THEOREM *)
Theorem droe_adequacy `{Layout: memory_layout}
  (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
  (es: list griotte_lang.expr):
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ?.
  set ( cnames := CmptNames_droe_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; relPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
      ]).
  eapply (@droe_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
