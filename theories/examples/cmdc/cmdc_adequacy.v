From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel.
From cap_machine Require Import compartment_layout.
From cap_machine Require Import cmdc cmdc_spec.
From cap_machine Require Import switcher switcher_spec assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_allocation.

Class memory_layout `{MachineParameters} := {

    (* switcher *)
    switcher_cmpt : cmptSwitcher;

    (* assert *)
    assert_cmpt : cmptAssert;

    (* main compartment *)
    main_cmpt : cmpt ;

    (* adv compartments B and C *)
    B_cmpt : cmpt ;
    C_cmpt : cmpt ;

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

Definition mk_initial_memory `{memory_layout} (mem: Mem) :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt B_cmpt ∪
    mk_initial_cmpt C_cmpt.


Definition is_initial_registers `{memory_layout} (reg: Reg) :=
  reg !! PC = Some (WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)) ∧
  reg !! cgp = Some (WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt) (cmpt_b_cgp main_cmpt)) ∧
  reg !! csp = Some (WCap RWL Local (b_switcher switcher_cmpt) (e_switcher switcher_cmpt) (b_switcher switcher_cmpt)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

Definition is_initial_sregisters `{memory_layout} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (b_trusted_stack switcher_cmpt)
                         (e_trusted_stack switcher_cmpt)
                         (b_trusted_stack switcher_cmpt)).

Definition is_initial_memory `{memory_layout} (mem: Mem) :=
  let switcher_entry :=
    WCap E_XSRW_ Global
      (b_switcher switcher_cmpt)
      (e_switcher switcher_cmpt)
      (a_switcher_cc switcher_cmpt)
  in
  let B_f :=
    SCap RO Global
      (cmpt_exp_tbl_pcc B_cmpt)
      (cmpt_exp_tbl_entries_end B_cmpt)
      (cmpt_exp_tbl_entries_start B_cmpt)
  in
  let C_g :=
    SCap RO Global
      (cmpt_exp_tbl_pcc C_cmpt)
      (cmpt_exp_tbl_entries_end C_cmpt)
      (cmpt_exp_tbl_entries_start C_cmpt)
  in

  mem = mk_initial_memory mem
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) =
    cmdc_main_imports
      (b_switcher switcher_cmpt) (e_switcher switcher_cmpt)
      (a_switcher_cc switcher_cmpt) (ot_switcher switcher_cmpt)
      (b_assert assert_cmpt) (e_assert assert_cmpt)
      B_f C_g
  ∧ (cmpt_code main_cmpt) = cmdc_main_code
  ∧ (cmpt_data main_cmpt) = cmdc_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [] (* TODO imports !! *)
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data B_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (switcher.encode_entry_point 1 0)]

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [] (* TODO imports !! *)
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data C_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (switcher.encode_entry_point 1 0)]
.

From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cname : CmptNameG}.
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context {B C : CmptName}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation CVIEW := (prodO STS_STD STS).
  Notation WORLD := (gmapO CmptName CVIEW).

  Definition flagN : namespace := nroot .@ "cmdc" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "cmdc" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "cmdc" .@ "assert_flag".

  Lemma mcdc_adequacy' `{Layout: @memory_layout MP}
    (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
    (es: list cap_lang.expr):
    is_initial_registers reg →
    is_initial_sregisters sreg →
    is_initial_memory m →
    rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
    m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
  Proof.
    intros Hreg Hsreg Hm Hstep.
    pose proof (@wp_invariance Σ cap_lang _ NotStuck) as WPI. cbn in WPI.
    pose (fun (c: ExecConf) => c.2 !! (flag_assert assert_cmpt) = Some (WInt 0%Z)) as state_is_good.
    specialize (WPI (Seq (Instr Executable)) (reg, sreg, m) es (reg', sreg', m')
                  (state_is_good (reg', sreg', m'))).
    eapply WPI. 2: assumption. intros Hinv κs. clear WPI.

    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl
                    & B_imports & B_code & B_data & B_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                   ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (seal_store_init) as (seal_storeg) "Hseal_store".

    (* TODO something seems wrong, why do I allocate 2 STS ? *)
    unshelve iMod gen_sts_init as (stsg) "Hsts"; eauto. (*XX*)
    iMod (heap_init) as (heapg) "HRELS".
    rewrite HCNames.
    iDestruct (big_sepS_elements with "Hsts") as "Hsts".
    iDestruct (big_sepS_elements with "HRELS") as "HRELS".
    setoid_rewrite elements_list_to_set; auto.

    iDestruct (big_sepL_cons with "Hsts") as "[Hsts_B Hsts_C]".
    iDestruct (big_sepL_cons with "Hsts_C") as "[Hsts_C _]".
    iDestruct (big_sepL_cons with "HRELS") as "[HRELS_B HRELS_C]".
    iDestruct (big_sepL_cons with "HRELS_C") as "[HRELS_C _]".

    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose ceriseg := CeriseG Σ Hinv mem_heapg reg_heapg sreg_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose proof (
        @cmdc_spec_full Σ ceriseg seal_storeg _ _ _ logrel_na_invs MP B C
      ) as Spec.

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; eauto.

    (* Separate all compartments *)
    rewrite {2}Hm.
    rewrite /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { admit. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { admit. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { admit. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { admit. }

    (* Assert *)
    rewrite /mk_initial_assert.
    iDestruct (big_sepM_union with "Hcmpt_assert") as "[Hassert Hassert_flag]".
    { admit. }
    iDestruct (big_sepM_union with "Hassert") as "[Hassert Hassert_cap]".
    { admit. }
    rewrite /cmpt_assert_flag_mregion.
    rewrite /mkregion.
    rewrite finz_seq_between_singleton.
    2: { admit. }
    cbn.
    iDestruct (big_sepM_insert with "Hassert_flag") as "[Hassert_flag _]"; first done.
    iMod (inv_alloc flagN ⊤ (flag_assert assert_cmpt ↦ₐ WInt 0%Z) with "Hassert_flag")%I
     as "#Hinv_assert_flag".
    rewrite /cmpt_assert_cap_mregion.
    rewrite /mkregion.
    rewrite finz_seq_between_singleton.
    2: { admit. }
    cbn.
    iDestruct (big_sepM_insert with "Hassert_cap") as "[Hassert_cap _]"; first done.

    rewrite /cmpt_assert_code_mregion.
    iDestruct (mkregion_prepare with "[Hassert]") as ">Hassert"; auto.
    { admit. }
    iAssert (assert.assert_inv
               (b_assert assert_cmpt)
               (e_assert assert_cmpt)
               (flag_assert assert_cmpt))
            with "[Hassert Hassert_cap]" as "Hassert".
    { rewrite /assert.assert_inv. iExists (cap_assert assert_cmpt).
      rewrite /codefrag /region_pointsto.
      replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)%a
        with (cap_assert assert_cmpt) by admit.
      iFrame.
      admit.
    }
    iMod (na_inv_alloc logrel.logrel_nais _ assertN _ with "Hassert") as "#Hassert".

    (* Switcher *)
    rewrite /mk_initial_switcher.
    iDestruct (big_sepM_union with "Hcmpt_switcher") as "[Hswitcher Hstack]".
    { admit. }
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher Htrusted_stack]".
    { admit. }

    rewrite /cmpt_switcher_code_mregion.
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
    { admit. }
    iEval (rewrite /mkregion) in "Hswitcher_sealing".
    rewrite finz_seq_between_singleton.
    2: { admit. }
    iEval (cbn) in "Hswitcher_sealing".
    iDestruct (big_sepM_insert with "Hswitcher_sealing") as "[Hswitcher_sealing _]"; first done.
    iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
    { admit. }
    rewrite /cmpt_switcher_trusted_stack_mregion.
    iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
    { admit. }
    iAssert (switcher_spec.switcher_inv
               (b_switcher switcher_cmpt)
               (e_switcher switcher_cmpt)
               (a_switcher_cc switcher_cmpt)
               (ot_switcher switcher_cmpt))
      with "[Hswitcher Hswitcher_sealing Htrusted_stack Hmtdc]" as "Hswitcher".
    {
      rewrite /switcher_spec.switcher_inv /codefrag /region_pointsto.
      replace (a_switcher_cc switcher_cmpt ^+ length switcher_instrs)%a
        with (e_switcher switcher_cmpt) by admit.
      iFrame.
      admit.
    }
    iMod (na_inv_alloc logrel.logrel_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".

    (* CMPT B *)
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_B".
    iDestruct (big_sepM_union with "Hcmpt_B") as "[HB HB_etbl]".
    { admit. }
    iDestruct (big_sepM_union with "HB") as "[HB_code HB_data]".
    { admit. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "HB_code") as "[HB_imports HB_code]".
    { admit. }
    rewrite B_imports. iClear "HB_imports".
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[HB_code]") as ">HB_code"; auto.
    { admit. }

    (* Initialises the world for B *)
    iAssert (region {[B := (∅, (∅, ∅))]} B) with "[HRELS_B]" as "Hr_B".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      - by rewrite /std /std_cview lookup_insert.
      - rewrite /region_map_def. by rewrite big_sepM_empty. }

    iMod (extend_region_perm_sepL2 _ {[B := (∅, (∅, ∅))]} B
            (finz.seq_between (cmpt_a_code B_cmpt) (cmpt_e_pcc B_cmpt))
            (cmpt_code B_cmpt) RX interpC _
           with "Hsts_B Hr_B [HB_code]") as "(Hr_B & HB_code & Hsts_B)".
    2: {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HB_code]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ B_code Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply interp_weakening.future_priv_mono_interp_z.
      - iFrame.
    }




    iAssert (region {[C := (∅, (∅, ∅))]} C) with "[HRELS_C]" as "Hr_C".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      - by rewrite /std /std_cview lookup_insert.
      - rewrite /region_map_def. by rewrite big_sepM_empty. }


    iPoseProof (Spec _ _ _ _ _ _ _ _ _ _ _ _
                  (b_assert assert_cmpt) (e_assert assert_cmpt) (flag_assert assert_cmpt)
                  _ _ _ _ _ assertN switcherN
                 with "[-
                        $Hassert $Hswitcher $Hna
                        Hr_B Hr_C $Hsts_B $Hsts_C]") as "Hspec".
    10: {

    }
    iAssert (WP Seq (Instr Executable) {{ _, True }})%I as "Spec".
    iModIntro.
    iExists (fun σ _ _ => ((gen_heap_interp σ.1.1) ∗ (gen_heap_interp σ.1.2) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    Set Printing All.
    iFrame "Spec".

    iIntros "[Hreg' Hmem']". iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    unfold minv_sep. iDestruct "Hx" as (mi) "(Hmi & Hmi_dom & %)".
    iDestruct "Hmi_dom" as %Hmi_dom.
    iDestruct (gen_heap_valid_inclSepM with "Hmem' Hmi") as %Hmi_incl.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
    eapply minv_sub_extend; [| |eassumption].
    rewrite Hmi_dom //. auto.

    iPoseProof (Spec with "[]") as "Hspec".

    iApply (Spec with "[]").
    (*     try eassumption. *)


  Admitted.
