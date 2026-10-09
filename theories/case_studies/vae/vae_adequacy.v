From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import vae vae_helper vae_spec_closure vae_spec.
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
    offset_adv_f : nat;
    offset_adv_g : nat;

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

Local Instance memory_layoutr_switcherLayout `{memory_layout} : switcherLayout.
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
  let C_g :=
    SCap RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      ((cmpt_exp_tbl_entries_start C_cmpt) ^+ 1)%a
  in

  mem = mk_initial_memory
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = vae_main_imports C_f
  ∧ (cmpt_code main_cmpt) = vae_main_code
  ∧ (cmpt_data main_cmpt) = vae_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = vae_export_table_entries

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) =
  [switcher_entry
   ; WSealed ot_switcher (vae_entry_awkward_sb (cmpt_exp_tbl_pcc main_cmpt)
                            (cmpt_exp_tbl_entries_end main_cmpt))
   ; WSealed ot_switcher C_g
  ]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall (is_initial_data_word C_cmpt) (cmpt_data C_cmpt)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point 0 offset_adv_f); WInt (encode_entry_point 0 offset_adv_g)]

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

  Definition flagN : namespace := nroot .@ "vae" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "vae" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "vae" .@ "assert_flag".
  Definition vaeN : namespace := nroot .@ "vae" .@ "code".

  Lemma vae_adequacy' `{Layout: !memory_layout}
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
    set (C_g := cmpt_export C_cmpt (cmpt_exp_tbl_entries_start C_cmpt ^+ 1)%a).
    set (awk_f := cmpt_export main_cmpt (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a).
    pose proof (cmpt_exp_tbl_entries_size C_cmpt) as HC_exp_tbl_size.
    rewrite C_exp_tbl /= in HC_exp_tbl_size.

    (* Iris adequacy: the program-logic resources of the initial state *)
    eapply (cerise_flag_adequacy Σ (ot_switcher switcher_cmpt) [(C_f, 0); (C_g, 0); (awk_f, 1)]
              flagN (flag_assert assert_cmpt));
      [| by repeat constructor | | exact Hstep].
    { assert (C_f ≠ C_g) by (intros ?; simplify_eq; solve_addr).
      assert (C_f ≠ awk_f) by apply not_eq_sym, cmpt_export_disjoint, cmpts_disjoints.
      assert (C_g ≠ awk_f) by apply not_eq_sym, cmpt_export_disjoint, cmpts_disjoints.
      cbn; repeat (apply NoDup_cons; split); try apply NoDup_nil; set_solver.
    }
    iIntros (ceriseg) "Hreg Hsreg Hmem Hna
                       ([#Hentry_Cf #Hentry_Cf'] & [#Hentry_Cg #Hentry_Cg'] & [#Hentry_awkf #Hentry_awkf'] & _)".
    (* Use the non-atomic invariant pool of [ceriseg] *)
    clear na_invg.
    iMod (initialise_world [C] {[ ot_switcher switcher_cmpt ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_interp_C _])";
      [done | apply NoDup_singleton |].
    set (W0 := (∅, (∅, ∅))).

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
      as "(Hmain_imports & Hmain_code & Hmain_data & Hmain_etbl_pcc & Hmain_etbl_cgp & Hmain_etbl_entries)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).
    iDestruct (region_pointsto_single with "Hmain_data") as "[%v [Hcgp_b %Hv] ]".
    { solve_addr+Hmain_data_size. }
    rewrite main_data /vae_main_data in Hv; simplify_eq.
    rewrite main_code main_exp_tbl /vae_export_table_entries.
    pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hmain_exp_tbl_size.
    rewrite main_exp_tbl /= in Hmain_exp_tbl_size.
    iAssert ((cmpt_exp_tbl_entries_start main_cmpt) ↦ₐ
               WInt (encode_entry_point 1 (length (cmpt_imports main_cmpt ++ VAE_main_code_init))))%I
      with "[Hmain_etbl_entries]" as "Hmain_etbl_entries".
    { rewrite /region_pointsto
        (finz_seq_between_singleton (cmpt_exp_tbl_entries_start main_cmpt)); last done.
      rewrite big_sepL2_singleton /vae_exp_tbl_entry_awkward.
      rewrite main_imports; done.
    }
    rewrite main_imports (cmpt_exp_tbl_entries_start_eq main_cmpt) (cmpt_exp_tbl_cgp_eq main_cmpt).
    iCombine "Hmain_imports Hmain_code" as "Hmain_code".
    iMod (na_inv_alloc cerise_nais _ vaeN _ with "Hmain_code") as "#Hmain_code".
    iMod (inv_alloc (export_table_PCCN vaeN) ⊤ _ with "Hmain_etbl_pcc") as "#Hinv_etbl_PCC".
    iMod (inv_alloc (export_table_CGPN vaeN) ⊤ _ with "Hmain_etbl_cgp") as "#Hinv_etbl_CGP".
    iMod (inv_alloc (export_table_entryN vaeN (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a) ⊤ _
           with "Hmain_etbl_entries") as "#Hinv_etbl_entry_awkward".
    assert (cmpt_exp_tbl_pcc main_cmpt <= cmpt_exp_tbl_pcc main_cmpt ^+ 2
            < cmpt_exp_tbl_entries_end main_cmpt)%a as Hmain_exp_tbl_bounds.
    { pose proof (cmpt_exp_tbl_entries_start_eq main_cmpt).
      pose proof (cmpt_exp_tbl_pcc_size main_cmpt).
      solve_addr. }

    (* Allocate the custom invariant *)
    set (i := (fresh_cus_name W0)).
    set (W1 := (<l[i:=false,(awk_rel_pub, awk_rel_priv)]l>W0)).
    iDestruct (world_interp_alloc_loc _ C false awk_rel_pub awk_rel_priv with "Hworld_interp_C")
      as ">(Hworld_interp_C & %Hloc_fresh & %Hcus_fresh & Hst_i & #Hrel_i)"; auto.

    iDestruct (inv_alloc awkN _ (awk_inv C i _) with "[Hcgp_b Hst_i]") as ">#Hawk_inv".
    { iExists false; iFrame. }

    iAssert (interp W1 C (WSealed (ot_switcher switcher_cmpt) awk_f)) as "#Hinterp_VAE".
    { iApply (vae_awkward_safe _ _ _ _ _ _ _ _ W1 assertN switcherN vaeN vaeN);
        try iFrame "#"; eauto; solve_ndisj. }

    (* Initialises the world for C *)
    pose proof switcher_cmpt_disjoints as (Hsw_main & Hsw_C).
    iMod (initialise_adversary_world W1 switcher_cmpt _ C
           with "HC_imports HC_code HC_data Hstack [] Hworld_interp_C")
      as "(Hworld_interp_C & #Hinterp_pcc_C & #Hinterp_cgp_C & #Hinterp_stack_C)"; auto.
    { rewrite C_imports.
      iIntros "[#Hpcc_interp #Hcgp_interp]".
      (* Switcher cross-compartment *)
      iSplit.
      { iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done. }
      (* VAE.awk *)
      iSplit.
      { iSplit.
        - iApply interp_monotone_sd; auto.
          iPureIntro.
          apply related_sts_pub_priv_world.
          eapply std_update_compartment_pub; eauto; (apply Forall_true; intros; done).
        - iIntros (??) "!> % ?".
          iApply interp_monotone_sd; auto.
      }
      (* C.g *)
      iSplit; last done.
      iSplit; last (iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto).
      iApply (adversary_export_interp _ _ _ _ _ 1 0 offset_adv_g
               with "Hswitcher Hsealed_pred_ot_switcher HC_etbl_pcc HC_etbl_cgp HC_etbl_entries
                     Hpcc_interp Hcgp_interp Hentry_Cg Hentry_Cg'").
      - by rewrite C_exp_tbl.
      - done.
      - lia.
    }
    iAssert (interp (adv_world W1 switcher_cmpt C_cmpt) C
               (WSealed (ot_switcher switcher_cmpt) C_f)) as "#Hinterp_C_f".
    { iApply (adversary_export_interp _ _ _ _ _ 0 0 offset_adv_f
               with "Hswitcher Hsealed_pred_ot_switcher HC_etbl_pcc HC_etbl_cgp HC_etbl_entries
                     Hinterp_pcc_C Hinterp_cgp_C Hentry_Cf Hentry_Cf'").
      - by rewrite C_exp_tbl.
      - solve_addr.
      - lia.
    }

    (* Extract registers *)
    iDestruct (initial_registers_split with "Hreg")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.

    iPoseProof (@vae_init_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ C
                  _ _ _ _ _ _ _ _
                  _ (cmpt_exp_tbl_entries_end main_cmpt)
                  _ _ [] [] assertN switcherN vaeN
                 with "[ $Hassert $Hswitcher $Hmain_code
                         $Hinv_etbl_PCC $Hinv_etbl_CGP $Hinv_etbl_entry_awkward
                         $Hna
                         $Hworld_interp_C
                         $HPC $Hcgp $Hcsp $Hrmap
                         $Hcstk_frag $Hinterp_stack_C
                         $Hinterp_C_f $Hentry_Cf $Hentry_awkf $Hentry_awkf'
                         $Hsealed_pred_ot_switcher
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
    { solve_ndisj. }
    { solve_ndisj. }
    { rewrite /adv_world_with /std_update_compartment /W1.
      rewrite !std_update_multiple_loc_sta.
      by simplify_map_eq.
    }
    { done. }

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.
End Adequacy.

Inductive CmptNames_vae := | B .
Local Instance CmptNames_vae_eq_dec : EqDecision CmptNames_vae.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_vae_finite : finite.Finite CmptNames_vae.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_vae_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_vae; |}.

(** END-TO-END THEOREM *)
Theorem vae_adequacy `{Layout: memory_layout}
  (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
  (es: list griotte_lang.expr)
  :
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ?.
  set ( cnames := CmptNames_vae_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; relPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
      ]).
  eapply (@vae_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
