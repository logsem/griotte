From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel.
From cap_machine Require Import compartment_layout.
From cap_machine Require Import cmdc cmdc_spec.
From cap_machine Require Import switcher switcher_spec assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_allocation.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.

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
  reg !! csp = Some (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

Definition is_initial_sregisters `{memory_layout} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (b_trusted_stack switcher_cmpt)
                         (e_trusted_stack switcher_cmpt)
                         (b_trusted_stack switcher_cmpt)).

Definition is_initial_memory `{memory_layout} (mem: Mem) :=
  let switcher_entry :=
    WSentry XSRW_ Local
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
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data B_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (switcher.encode_entry_point 1 0)]

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data C_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (switcher.encode_entry_point 1 0)]
.

Lemma mk_initial_cmpt_C_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  is_initial_memory m →
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt ∪ mk_initial_cmpt B_cmpt
    ##ₘ mk_initial_cmpt C_cmpt.
Proof.
  intros (Hm & main_imports & main_code & main_data & main_exp_tbl
          & B_imports & B_code & B_data & B_exp_tbl
          & C_imports & C_code & C_data & C_exp_tbl
         ).
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
  is_initial_memory m →
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  intros (Hm & main_imports & main_code & main_data & main_exp_tbl
          & B_imports & B_code & B_data & B_exp_tbl
          & C_imports & C_code & C_data & C_exp_tbl
         ).
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
  is_initial_memory m →
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt
    ##ₘ mk_initial_cmpt main_cmpt.
Proof.
  intros (Hm & main_imports & main_code & main_data & main_exp_tbl
          & B_imports & B_code & B_data & B_exp_tbl
          & C_imports & C_code & C_data & C_exp_tbl
         ).
  pose proof switcher_cmpt_disjoints as (HswitcherMain & _ & _).
  pose proof assert_cmpt_disjoints as (HassertMain & _ & _).
  rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
Qed.

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
  Notation WORLD := (prodO STS_STD STS).

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

    pose proof Hm as Hm'.
    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl
                    & B_imports & B_code & B_data & B_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                   ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (seal_store_init ({[ (ot_switcher switcher_cmpt) ]} : gset _)) as (seal_storeg) "Hseal_store".

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
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* Assert *)
    rewrite /mk_initial_assert.
    iDestruct (big_sepM_union with "Hcmpt_assert") as "[Hassert Hassert_flag]".
    { eapply cmpt_assert_flag_mregion_disjoint ; eauto. }
    iDestruct (big_sepM_union with "Hassert") as "[Hassert Hassert_cap]".
    { eapply cmpt_assert_cap_mregion_disjoint ; eauto. }
    rewrite /cmpt_assert_flag_mregion.
    rewrite /mkregion.
    rewrite finz_seq_between_singleton.
    2: { pose proof (assert_flag_size assert_cmpt) as H; solve_addr+H. }
    cbn.
    iDestruct (big_sepM_insert with "Hassert_flag") as "[Hassert_flag _]"; first done.
    iMod (inv_alloc flagN ⊤ (flag_assert assert_cmpt ↦ₐ WInt 0%Z) with "Hassert_flag")%I
     as "#Hinv_assert_flag".
    rewrite /cmpt_assert_cap_mregion.
    rewrite /mkregion.
    rewrite finz_seq_between_singleton.
    2: { pose proof (assert_cap_size assert_cmpt) as H; solve_addr+H. }
    cbn.
    iDestruct (big_sepM_insert with "Hassert_cap") as "[Hassert_cap _]"; first done.

    rewrite /cmpt_assert_code_mregion.
    iDestruct (mkregion_prepare with "[Hassert]") as ">Hassert"; auto.
    { apply (assert_code_size assert_cmpt). }
    iAssert (assert.assert_inv
               (b_assert assert_cmpt)
               (e_assert assert_cmpt)
               (flag_assert assert_cmpt))
            with "[Hassert Hassert_cap]" as "Hassert".
    { rewrite /assert.assert_inv. iExists (cap_assert assert_cmpt).
      rewrite /codefrag /region_pointsto.
      replace (b_assert assert_cmpt ^+ length assert_subroutine_instrs)%a
        with (cap_assert assert_cmpt).
      2: { pose proof (assert_code_size assert_cmpt); solve_addr+H. }
      iFrame.
      iSplit; first (iPureIntro ; apply (assert_code_size assert_cmpt)).
      iSplit; iPureIntro.
      + apply (assert_cap_size assert_cmpt).
      + by rewrite (assert_flag_size assert_cmpt).
    }
    iMod (na_inv_alloc logrel.logrel_nais _ assertN _ with "Hassert") as "#Hassert".

    (* Switcher *)
    rewrite /mk_initial_switcher.
    iDestruct (big_sepM_union with "Hcmpt_switcher") as "[Hswitcher Hstack]".
    { eapply cmpt_switcher_stack_mregion_disjoint ; eauto. }
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher Htrusted_stack]".
    { eapply cmpt_switcher_trusted_stack_mregion_disjoint ; eauto. }

    rewrite /cmpt_switcher_code_mregion.
    iDestruct (big_sepM_union with "Hswitcher") as "[Hswitcher_sealing Hswitcher]".
    { eapply cmpt_switcher_code_stack_mregion_disjoint ; eauto. }
    iEval (rewrite /mkregion) in "Hswitcher_sealing".
    rewrite finz_seq_between_singleton.
    2: { apply (switcher_cc_entry_point switcher_cmpt). }
    iEval (cbn) in "Hswitcher_sealing".
    iDestruct (big_sepM_insert with "Hswitcher_sealing") as "[Hswitcher_sealing _]"; first done.
    iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
    { apply (switcher_size switcher_cmpt). }
    rewrite /cmpt_switcher_trusted_stack_mregion.
    iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
    { apply (trusted_stack_size switcher_cmpt). }
    rewrite  big_sepS_singleton.
    iMod (seal_store_update_alloc _ ( ot_switcher_prop ) with "Hseal_store") as "#Hsealed_pred_ot_switcher".
    iAssert ( switcher_spec.switcher_inv
               (b_switcher switcher_cmpt)
               (e_switcher switcher_cmpt)
               (a_switcher_cc switcher_cmpt)
               (ot_switcher switcher_cmpt))%I
      with "[Hswitcher Hswitcher_sealing Htrusted_stack Hmtdc]" as "Hswitcher".
    {
      rewrite /switcher_spec.switcher_inv /codefrag /region_pointsto.
      replace (a_switcher_cc switcher_cmpt ^+ length switcher_instrs)%a
        with (e_switcher switcher_cmpt).
      2: { pose proof (switcher_size switcher_cmpt) as H ; solve_addr+H. }
      iFrame.
      iExists (tl (trusted_stack_content switcher_cmpt)).
      iSplitR.
      + iPureIntro.
        rewrite /SubBounds.
        clear.
        pose proof (switcher_size switcher_cmpt).
        pose proof (switcher_cc_entry_point switcher_cmpt).
        solve_addr.
      + destruct (trusted_stack_content switcher_cmpt); cbn;
        iDestruct (big_sepL2_alt with "Htrusted_stack") as "[%Hlen Htrusted_stack]".
        admit.
        admit.
    }
    iMod (na_inv_alloc logrel.logrel_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".

    (* CMPT B *)
    (* assert ( *)
    (*    (finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_a_code B_cmpt))  = [cmpt_a_code B_cmpt] *)
    (*   ) as Himport_B_size. *)
    (* { admit. } *)

    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_B".
    iDestruct (big_sepM_union with "Hcmpt_B") as "[HB HB_etbl]".
    { eapply cmpt_exp_tbl_disjoint ; eauto. }
    iDestruct (big_sepM_union with "HB") as "[HB_code HB_data]".
    { eapply cmpt_cgp_disjoint ; eauto. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "HB_code") as "[HB_imports HB_code]".
    { eapply cmpt_code_disjoint ; eauto. }
    rewrite B_imports.
    iEval (rewrite /mkregion) in "HB_imports".
    rewrite finz_seq_between_singleton.
    2: { pose proof (cmpt_import_size B_cmpt) as HB_import_size.
         by rewrite B_imports /= in HB_import_size.
    }
    cbn.
    iDestruct (big_sepM_insert with "HB_imports") as "[HB_imports _]"; first done.
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[HB_code]") as ">HB_code"; auto.
    { apply (cmpt_code_size B_cmpt). }
    iDestruct (mkregion_prepare with "[HB_data]") as ">HB_data"; auto.
    { apply (cmpt_data_size B_cmpt). }

    (* Initialises the world for B *)
    iAssert (region (∅, (∅, ∅)) B) with "[HRELS_B]" as "Hr_B".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }
    iMod (extend_region_perm_sepL2 _ (∅, (∅, ∅)) B
            (finz.seq_between (cmpt_a_code B_cmpt) (cmpt_e_pcc B_cmpt))
            (cmpt_code B_cmpt)
            RX interpC
           with "Hsts_B Hr_B [HB_code]") as "(Hr_B & HB_code & Hsts_B)".
    { done. }
    { apply Forall_true. intros.
      by rewrite /std lookup_empty.
    }
    {
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

    iMod (extend_region_perm_sepL2 _ _ B
            (finz.seq_between (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt))
            (cmpt_data B_cmpt)
            RW interpC
           with "Hsts_B Hr_B [HB_data]") as "(Hr_B & HB_data & Hsts_B)".
    { done. }
    { admit. }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HB_data]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ B_data Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply interp_weakening.future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (extend_region_perm_sepL2 _ _ B
            [cmpt_b_pcc B_cmpt]
            (cmpt_imports B_cmpt)
            RX interpC
           with "Hsts_B Hr_B [HB_imports]") as "(Hr_B & HB_imports & Hsts_B)".
    { done. }
    { admit. }
    {
      iDestruct (switcher_interp with "[$Hswitcher]") as "#Hswitcher_interp".
      iDestruct (future_priv_mono_interp_switcher with "[$Hswitcher]") as "#Hswitcher_mono".
      rewrite B_imports /=.
      iFrame "#∗".
    }
    match goal with
    | H: _ |- context [  (sts_full_world ?W B) ] => set (Winit_B := W)
    end.
    set (B_f := (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt))).
    iAssert ( interp Winit_B B (WSealed (ot_switcher switcher_cmpt) B_f)) with
      "[HB_etbl HB_code Hr_B HB_data Hsts_B]" as "#Hinterp_B".
    { admit. } (* TODO we need to define what it means to be safe to share for entry point*)
    iClear "HB_etbl HB_code HB_data".

    (* CMPT C *)
    (* assert ( *)
    (*    (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt)) = [cmpt_a_code C_cmpt] *)
    (*   ) as Himport_C_size. *)
    (* { admit. } *)
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
    iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
    { eapply cmpt_exp_tbl_disjoint ; eauto. }
    iDestruct (big_sepM_union with "HC") as "[HC_code HC_data]".
    { eapply cmpt_cgp_disjoint ; eauto. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "HC_code") as "[HC_imports HC_code]".
    { eapply cmpt_code_disjoint ; eauto. }
    rewrite C_imports.
    iEval (rewrite /mkregion) in "HC_imports".
    rewrite finz_seq_between_singleton.
    2: { pose proof (cmpt_import_size C_cmpt) as HC_import_size.
         by rewrite C_imports /= in HC_import_size.
    }
    iDestruct (big_sepM_insert with "HC_imports") as "[HC_imports _]"; first done.
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[HC_code]") as ">HC_code"; auto.
    { apply (cmpt_code_size C_cmpt). }
    iDestruct (mkregion_prepare with "[HC_data]") as ">HC_data"; auto.
    { apply (cmpt_data_size C_cmpt). }

    (* Initialises the world for C *)
    iAssert (region (∅, (∅, ∅)) C) with "[HRELS_C]" as "Hr_C".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    iMod (extend_region_perm_sepL2 _ (∅, (∅, ∅)) C
            (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
            (cmpt_code C_cmpt)
            RX interpC
           with "Hsts_C Hr_C [HC_code]") as "(Hr_C & HC_code & Hsts_C)".
    { done. }
    { apply Forall_true. intros.
      by rewrite /std lookup_empty.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HC_code]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ C_code Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply interp_weakening.future_priv_mono_interp_z.
      - iFrame.
    }
    iMod (extend_region_perm_sepL2 _ _ C
            (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
            (cmpt_data C_cmpt)
            RW interpC
           with "Hsts_C Hr_C [HC_data]") as "(Hr_C & HC_data & Hsts_C)".
    { done. }
    { admit. }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HC_data]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ C_data Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply interp_weakening.future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (extend_region_perm_sepL2 _ _ C
            [cmpt_b_pcc C_cmpt]
            (cmpt_imports C_cmpt)
            RX interpC
           with "Hsts_C Hr_C [HC_imports]") as "(Hr_C & HC_imports & Hsts_C)".
    { done. }
    { admit. }
    {
      iDestruct (switcher_interp with "[$Hswitcher]") as "#Hswitcher_interp".
      iDestruct (future_priv_mono_interp_switcher with "[$Hswitcher]") as "#Hswitcher_mono".
      rewrite C_imports /=.
      iFrame "#∗".
    }
    match goal with
    | H: _ |- context [  (sts_full_world ?W C) ] => set (Winit_C := W)
    end.
    set (C_g := (SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    iAssert ( interp Winit_C C (WSealed (ot_switcher switcher_cmpt) C_g)) with
      "[HC_etbl HC_code Hr_C HC_data Hsts_C]" as "#Hinterp_C".
    { admit. } (* TODO we need to define what it means to be safe to share for entry point*)
    iClear "HC_etbl HC_code HC_data".

    (* CMPT MAIN *)
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_main".
    iDestruct (big_sepM_union with "Hcmpt_main") as "[Hmain Hmain_etbl]".
    { eapply cmpt_exp_tbl_disjoint ; eauto. }
    iDestruct (big_sepM_union with "Hmain") as "[Hmain_code Hmain_data]".
    { eapply cmpt_cgp_disjoint ; eauto. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "Hmain_code") as "[Hmain_imports Hmain_code]".
    { eapply cmpt_code_disjoint ; eauto. }
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[Hmain_imports]") as ">Hmain_imports"; auto.
    { apply (cmpt_import_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_code]") as ">Hmain_code"; auto.
    { apply (cmpt_code_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_data]") as ">Hmain_data"; auto.
    { apply (cmpt_data_size main_cmpt). }
    iAssert (
       [[(cmpt_b_pcc main_cmpt),(cmpt_a_code main_cmpt)]]↦ₐ[[cmpt_imports main_cmpt]]
     )%I with "[Hmain_imports]" as "Hmain_imports"; first done.
    iAssert (
       [[(cmpt_b_cgp main_cmpt),(cmpt_e_cgp main_cmpt)]]↦ₐ[[cmpt_data main_cmpt]]
     )%I with "[Hmain_data]" as "Hmain_data"; first done.
    iAssert (
      codefrag (cmpt_a_code main_cmpt) (cmpt_code main_cmpt)
     )%I with "[Hmain_code]" as "Hmain_code".
    { rewrite /codefrag.
      replace (cmpt_a_code main_cmpt ^+ length (cmpt_code main_cmpt))%a
        with (cmpt_e_pcc main_cmpt).
      2: { pose proof (cmpt_code_size main_cmpt) as H ; solve_addr+H. }
      done.
    }
    rewrite main_imports main_code main_data.

    (* Compartment's stack *)
    rewrite /cmpt_switcher_stack_mregion.
    iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
    { apply (stack_size switcher_cmpt). }
    iAssert (
        [[(b_stack switcher_cmpt), (e_stack switcher_cmpt)]]↦ₐ[[(stack_content switcher_cmpt)]]
      )%I with "[Hstack]" as "Hstack"; first done.

    (* Extract registers *)
    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.

    iPoseProof (Spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ (fun _ => True)%I assertN switcherN
                 with "[ $Hassert $Hswitcher $Hna
                        $Hr_B $Hr_C $Hsts_B $Hsts_C
                        $HPC $Hcgp $Hcsp $Hreg
                        $Hmain_imports $Hmain_code $Hmain_data $Hstack
                        $Hinterp_B $Hinterp_C
                        ]") as "Hspec"; eauto.
    { rewrite !dom_delete_L.
      rewrite regmap_full_dom; first done.
      intros r.
      destruct (decide (r = PC)); simplify_eq.
      { eexists; eapply HPC. }
      destruct (decide (r = cgp)); simplify_eq.
      { eexists; eapply Hcgp. }
      destruct (decide (r = csp)); simplify_eq.
      { eexists; eapply Hcsp. }
      eexists (WInt 0).
      apply Hreg.
      clear -n n0 n1; set_solver.
    }
   { intros r Hdom.
     rewrite !dom_delete_L in Hdom.
     destruct (decide (r = PC)); simplify_eq.
     { set_solver+Hdom. }
     destruct (decide (r = cgp)); simplify_eq.
     { set_solver+Hdom. }
     destruct (decide (r = csp)); simplify_eq.
     { set_solver+Hdom. }
     rewrite !lookup_delete_ne //.
     apply Hreg.
     clear -n n0 n1; set_solver.
    }
    { rewrite /SubBounds.
      pose proof (cmpt_import_size main_cmpt) as Hmain_imports.
      pose proof (cmpt_code_size main_cmpt) as Hmain_code.
      rewrite -main_code.
      solve_addr+Hmain_imports Hmain_code.
    }
    { pose proof (cmpt_data_size main_cmpt) as Hmain_data.
      by rewrite -main_data.
    }
    { pose proof (cmpt_import_size main_cmpt) as Hmain_imports.
      by rewrite -Hmain_imports main_imports.
    }
    { subst Winit_B.
      intro Hcontra.
      apply elem_of_dom_std_multiple_update in Hcontra.
      destruct Hcontra as [Hcontra|Hcontra].
      - admit.
      - apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + admit.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * admit.
          * rewrite /std /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { subst Winit_C.
      intro Hcontra.
      apply elem_of_dom_std_multiple_update in Hcontra.
      destruct Hcontra as [Hcontra|Hcontra].
      - admit.
      - apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + admit.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * admit.
          * rewrite /std /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { clear.
      pose proof (stack_size switcher_cmpt) as Hstacksize.
      replace (e_stack switcher_cmpt) with ( (b_stack switcher_cmpt) ^+ length
                                               (stack_content switcher_cmpt))%a
      by (by apply finz_incr_eq).
      rewrite /finz.dist; solve_addr.
    }
    { iNext; iIntros "H". proofmode.wp_end; by iLeft. }

    iModIntro.
    iExists (fun σ _ _ => ( ((gen_heap_interp σ.1.1) ∗ (gen_heap_interp σ.1.2)) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.

    iIntros "[ [Hreg' Hsreg'] Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
  Admitted.
End Adequacy.
