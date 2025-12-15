From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import deep_locality deep_locality_spec.
From cap_machine Require Import switcher assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From cap_machine Require Import compartment_layout switcher_adequacy.
From cap_machine Require Import disjoint_regions_tactics.
From cap_machine Require Import switcher_preamble interp_switcher_call interp_switcher_return.

Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_layout : @switcherLayout MP;
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

Definition mk_initial_memory `{memory_layout} (mem: Mem) :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt C_cmpt.


Definition is_initial_registers `{memory_layout} (reg: Reg) :=
  reg !! PC = Some (WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_a_code main_cmpt)) ∧
  reg !! cgp = Some (WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt) (cmpt_b_cgp main_cmpt)) ∧
  reg !! csp = Some (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt)) ∧
  (∀ (r: RegName), r ∉ ({[ PC; cgp; csp ]} : gset RegName) → reg !! r = Some (WInt 0)).

Program Definition is_initial_sregisters `{@memory_layout MP} (sreg : SReg) :=
  sreg !! MTDC = Some (WCap RWL Local
                         (@b_trusted_stack MP switcher_layout)
                         (@e_trusted_stack MP switcher_layout)
                         (@b_trusted_stack MP switcher_layout)).

Definition is_initial_memory `{@memory_layout MP} (mem: Mem) :=
  let b_switcher := (@b_switcher MP switcher_layout) in
  let e_switcher := (@e_switcher MP switcher_layout) in
  let a_switcher_call := (@a_switcher_call MP switcher_layout) in
  let ot_switcher := (@ot_switcher MP switcher_layout) in
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

  mem = mk_initial_memory mem
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) =
    dle_main_imports
      b_switcher e_switcher
      a_switcher_call ot_switcher
      (b_assert assert_cmpt) (e_assert assert_cmpt)
      C_f
  ∧ (cmpt_code main_cmpt) = dle_main_code
  ∧ (cmpt_data main_cmpt) = dle_main_data
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
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [C]) }.

  Definition flagN : namespace := nroot .@ "cmdc" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "cmdc" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "cmdc" .@ "assert_flag".


  Lemma cmdc_adequacy' `{Layout: @memory_layout MP}
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

    set b_switcher := (@b_switcher MP switcher_layout).
    set e_switcher := (@e_switcher MP switcher_layout).
    set a_switcher_call := (@a_switcher_call MP switcher_layout).
    set ot_switcher := (@ot_switcher MP switcher_layout).
    set a_switcher_return := (@a_switcher_return MP switcher_layout).
    set b_trusted_stack := (@b_trusted_stack MP switcher_layout).
    set e_trusted_stack := (@e_trusted_stack MP switcher_layout).
    set switcher_size := (@switcher_size MP switcher_layout).
    set switcher_call_entry_point := (@switcher_call_entry_point MP switcher_layout).
    set switcher_return_entry_point := (@switcher_return_entry_point MP switcher_layout).

    pose proof Hm as Hm'.
    destruct Hm as (Hm
                    & main_imports & main_code & main_data & main_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                    & Hstack
                   ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (seal_store_init ({[ ot_switcher ]} : gset _)) as (seal_storeg) "Hseal_store".
    set (
        C_f :=
       (WCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
         (cmpt_exp_tbl_entries_start C_cmpt))
      ).

    iMod (
       entry_init (
           {[
               (seal_capability C_f ot_switcher) := 1;
               (borrow (seal_capability C_f ot_switcher)) := 1
           ]}

         )
      ) as (entry_g) "Hentries".
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cf Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Cf' Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    subst C_f; cbn.
    set (C_f := (SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_f' := (SCap RO Local (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).




    unshelve iMod (gen_sts_init 0) as (stsg) "Hsts"; eauto. (*XX*)
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (heap_init) as (heapg) "HRELS".

    iDestruct (big_sepS_elements with "Hsts") as "Hsts_C".
    iDestruct (big_sepS_elements with "HRELS") as "HRELS_C".
    rewrite HCNames.
    pose proof (NoDup_singleton C) as HCNoDup.
    setoid_rewrite elements_list_to_set; auto.
    rewrite !big_sepL_singleton.

    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    pose ceriseg := CeriseG Σ Hinv mem_heapg reg_heapg sreg_heapg entry_g.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose switcher_layout_g := (@switcher_layout MP Layout).

    pose proof (
        @dle_spec Σ ceriseg seal_storeg _ _ _ logrel_na_invs _ _  switcher_layout_g C
      ) as Spec.

    (* Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; eauto.

    (* Separate all compartments *)
    rewrite {2}Hm.
    rewrite /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_C]".
    { eapply mk_initial_cmpt_C_disjoint; eauto. }
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
    { eapply cmpt_switcher_code_stack_mregion_disjoint ; eauto.
      exact switcher_cmpt.
    }
    iEval (rewrite /mkregion) in "Hswitcher_sealing".
    rewrite finz_seq_between_singleton.
    2: { apply switcher_call_entry_point. }
    iEval (cbn) in "Hswitcher_sealing".
    iDestruct (big_sepM_insert with "Hswitcher_sealing") as "[Hswitcher_sealing _]"; first done.
    iDestruct (mkregion_prepare with "[Hswitcher]") as ">Hswitcher"; auto.
    { apply switcher_size. }
    rewrite /cmpt_switcher_trusted_stack_mregion.
    iDestruct (mkregion_prepare with "[Htrusted_stack]") as ">Htrusted_stack"; auto.
    { apply (trusted_stack_size switcher_cmpt). }
    rewrite  big_sepS_singleton.
    iMod (seal_store_update_alloc _ ( ot_switcher_propC ) with "Hseal_store") as "#Hsealed_pred_ot_switcher".
    iAssert ( switcher_preamble.switcher_inv )
      with "[Hswitcher Hswitcher_sealing Htrusted_stack Hcstk_full Hmtdc]" as "Hswitcher".
    {
      rewrite /switcher_preamble.switcher_inv /codefrag /region_pointsto.
      replace (a_switcher_call ^+ length switcher_instrs)%a
        with e_switcher.
      2: { pose proof switcher_size as H.
           subst a_switcher_call e_switcher.
           solve_addr+H.
      }
      iFrame "∗#".
      iExists (tl (trusted_stack_content switcher_cmpt)).
      iSplitR; first (iPureIntro; apply (ot_switcher_size switcher_cmpt)).
      pose proof (trusted_stack_content_base_zeroed switcher_cmpt) as Htstk_head.
      pose proof (trusted_stack_size switcher_cmpt) as Htstk_size.
      destruct (trusted_stack_content switcher_cmpt); cbn in Htstk_head; simplify_eq.
      rewrite finz_seq_between_cons; last solve_addr+Htstk_size.
      iDestruct "Htrusted_stack" as "[Hbase_stack Htrusted_stack]".
      iFrame.
      iSplitL; last (iPureIntro ; by rewrite finz_add_0).
      subst switcher_layout_g.
      iSplit; iPureIntro; solve_addr.
    }
    iMod (na_inv_alloc logrel.logrel_nais _ switcherN _ with "Hswitcher") as "#Hswitcher".

    (* CMPT C *)
    iEval (rewrite /mk_initial_cmpt) in "Hcmpt_C".
    iDestruct (big_sepM_union with "Hcmpt_C") as "[HC HC_etbl]".
    { eapply cmpt_exp_tbl_disjoint ; eauto. }
    iDestruct (big_sepM_union with "HC") as "[HC_code HC_data]".
    { eapply cmpt_cgp_disjoint ; eauto. }
    rewrite /cmpt_pcc_mregion.
    iDestruct (big_sepM_union with "HC_code") as "[HC_imports HC_code]".
    { eapply cmpt_code_disjoint ; eauto. }
    iEval (rewrite /mkregion) in "HC_imports".
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[HC_code]") as ">HC_code"; auto.
    { apply (cmpt_code_size C_cmpt). }
    iDestruct (mkregion_prepare with "[HC_data]") as ">HC_data"; auto.
    { apply (cmpt_data_size C_cmpt). }
    iDestruct (mkregion_prepare with "[HC_imports]") as ">HC_imports"; auto.
    { rewrite C_imports.
      pose proof (cmpt_import_size C_cmpt) as H ; cbn in *.
      by rewrite C_imports in H.
    }

    (* Initialises the world for C *)
    cbn.
    iAssert (region (∅, (∅, ∅)) C) with "[HRELS_C]" as "Hr_C".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }

    iMod (
       alloc_compartment_interp with "[$HC_imports] [$HC_code] [$HC_data] [] [$Hsts_C] [$Hr_C]"
      ) as "(Hsts_C & Hr_C & #HC_code & #HC_data)"; eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite C_imports.
      rewrite (finz_seq_between_singleton (cmpt_b_pcc C_cmpt)).
      2: { pose proof (cmpt_import_size C_cmpt) as HC_import_size.
           by rewrite C_imports /= in HC_import_size.
      }
      cbn.
      iSplit; last done.
      iSplit; [| iIntros (???) ; iModIntro ]
      ; iIntros "_"; iApply interp_switcher_call ; done.
    }
    rewrite (finz_seq_between_singleton (cmpt_b_pcc C_cmpt)).
    2: { pose proof (cmpt_import_size C_cmpt) as HC_import_size.
         by rewrite C_imports /= in HC_import_size.
    }

    assert (
        Forall
          (λ k : finz MemNum,
             (std_update_multiple
                (std_update_multiple
                   (std_update_multiple (∅, (∅, ∅))
                      (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt)) Permanent)
                   (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)) Permanent)
                [cmpt_b_pcc C_cmpt] Permanent).1
               !! k = None)
          (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
      ) as Hstack_disjoint.
    { apply Forall_forall; intros a Ha; cbn.
      pose proof (cmpt_import_size C_cmpt) as H.
      rewrite C_imports /= in H.
      pose proof (cmpt_code_size C_cmpt) as H'.
      pose proof switcher_cmpt_disjoints as (_ & Hc).
      rewrite lookup_insert_ne.
      2: { intro Hcontra.
           assert (a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
           { rewrite -Hcontra.
             apply elem_of_finz_seq_between; solve_addr+H H'.
           }
           apply (Hc a).
           + rewrite /cmpt_switcher_region.
             eapply elem_of_union;eauto.
           + eapply elem_of_union;eauto.
             left; eapply elem_of_union;eauto.
      }
      rewrite std_sta_update_multiple_lookup_same_i.
      2: { intro Hcontra.
           apply (Hc a); eauto.
           + eapply elem_of_union;eauto.
           + eapply elem_of_union;eauto.
             left;eapply elem_of_union;eauto.
      }
      rewrite std_sta_update_multiple_lookup_same_i; first done.
      intro Hcontra.
      apply (Hc a); eauto.
      + eapply elem_of_union;eauto.
      + eapply elem_of_union;eauto.
        left;eapply elem_of_union;eauto.
        left.
        rewrite !elem_of_finz_seq_between in Hcontra |- *.
        solve_addr+H H' Hcontra.
    }

    iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
    { apply (stack_size switcher_cmpt). }
    iMod ( extend_region_temp_sepL2 _ _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             (stack_content switcher_cmpt)
             RWL interpC
           with "Hsts_C Hr_C [Hstack]")
           as "(Hr_C & #Hrel_stk_C & Hsts_C)".
    { done. }
    { eapply Hstack_disjoint. }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "Hstack").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite /interpC /safeC fixpoint_interp1_eq /=.
      iSplit; eauto.
      iApply future_pub_mono_interp_z.
    }

    match goal with
    | H: _ |- context [  (sts_full_world ?W C) ] => set (Winit_C := W)
    end.


    iEval (rewrite /cmpt_exp_tbl_mregion) in "HC_etbl".
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl HC_etbl_entries]".
    { eapply cmpt_exp_tbl_entries_disjoint. }
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl_pcc HC_etbl_cgp]".
    { eapply cmpt_exp_tbl_pcc_cgp_disjoint. }
    iDestruct (mkregion_prepare with "[HC_etbl_entries]") as ">HC_etbl_entries"; auto.
    { apply cmpt_exp_tbl_entries_size. }
    iDestruct (mkregion_prepare with "[HC_etbl_pcc]") as ">HC_etbl_pcc"; auto.
    { cbn; apply cmpt_exp_tbl_pcc_size. }
    iDestruct (mkregion_prepare with "[HC_etbl_cgp]") as ">HC_etbl_cgp"; auto.
    { cbn; apply cmpt_exp_tbl_cgp_size. }
    iEval (rewrite C_exp_tbl) in "HC_etbl_entries".
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start C_cmpt)).
    2: {
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      by rewrite C_exp_tbl in H1; cbn in H1.
    }
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc C_cmpt))
    ; last (apply cmpt_exp_tbl_pcc_size).
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp C_cmpt))
    ; last (apply cmpt_exp_tbl_cgp_size).
    rewrite !big_sepL2_singleton.

    iMod (inv_alloc (switcher_preamble.export_table_PCCN (nroot .@ C)) ⊤ _
           with "HC_etbl_pcc")%I as "#HC_etbl_pcc".
    iMod (inv_alloc (switcher_preamble.export_table_CGPN (nroot .@ C)) ⊤ _
           with "HC_etbl_cgp")%I as "#HC_etbl_cgp".
    iMod (inv_alloc (switcher_preamble.export_table_entryN (nroot .@ C) (cmpt_exp_tbl_entries_start C_cmpt)) ⊤ _
           with "HC_etbl_entries")%I as "#HC_etbl_entries".

    iAssert (interp Winit_C C
               (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a)
            )%I as "#Hinterp_pcc_C".
    { iApply interp_monotone_nl; eauto.
      iPureIntro.
      rewrite /Winit_C.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }

    iAssert (interp Winit_C C
               (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a)
            )%I as "#Hinterp_cgp_C".
    { iApply interp_monotone_nl; eauto.
      iPureIntro.
      rewrite /Winit_C.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple.
      eapply Forall_impl; eauto.
      intros a Ha; cbn in *.
      by rewrite not_elem_of_dom.
    }

    iAssert (interp Winit_C C
               (WCap RWL Local (b_stack switcher_cmpt) (e_stack switcher_cmpt) (b_stack switcher_cmpt))
            )%I as "#Hinterp_stack_C".
    { iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      iExists RWL, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      rewrite (big_sepL_lookup _ (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
                 k a); eauto.
      iFrame "Hrel_stk_C".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      assert ((std Winit_C) !! a = Some Temporary).
      { subst Winit_C.
        apply elem_of_list_lookup_2 in Ha.
        rewrite std_sta_update_multiple_lookup_in_i; auto.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Temporary); done.
    }

    iAssert ( interp Winit_C C (WSealed ot_switcher C_f)) with
      "[HC_code Hr_C HC_data Hsts_C Hentry_Cf']" as "#Hinterp_C".
    { iApply (ot_switcher_interp_entry _ _ _ _ 1 1
               with "[$] [$] [$] [$] [$] [$] [$] [$]"); eauto; last lia.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
      rewrite C_exp_tbl in H2.
      solve_addr+H1 H2.
    }
    iClear "HC_etbl_pcc HC_etbl_cgp HC_etbl_entries HC_code HC_data Hinterp_pcc_C Hinterp_cgp_C".

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

    (* Extract registers *)
    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.

    iPoseProof (Spec _ _ _ _ _ _ _ _
                  _ _ _ _ _
                  [] [] assertN switcherN []
                 with "[ $Hassert $Hswitcher $Hna
                        $Hr_C $Hsts_C
                        $HPC $Hcgp $Hcsp $Hreg
                        $Hmain_imports $Hmain_code $Hmain_data
                        $Hinterp_C $Hcstk_frag
                        $Hentry_Cf
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
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
     exists (WInt 0).
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
    { subst Winit_C.
      intro Hcontra.
      assert ( (cmpt_b_cgp main_cmpt)%a ∈ finz.seq_between (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
             ) as Hb_cgp_in.
      { pose proof (cmpt_data_size main_cmpt) as H.
        rewrite elem_of_finz_seq_between.
        rewrite main_data in H; cbn.
        solve_addr+H.
      }
      apply elem_of_dom_std_multiple_update in Hcontra.
      clear -Hcontra Hb_cgp_in C_imports.
      destruct Hcontra as [Hcontra|Hcontra].
      - pose proof switcher_cmpt_disjoints as (Hdis&_). set_solver.
      - pose proof cmpts_disjoints as Hdis.
        apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + assert (cmpt_b_pcc C_cmpt ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
          { pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
            pose proof (cmpt_code_size C_cmpt).
            rewrite elem_of_finz_seq_between; solve_addr.
          }
          rewrite elem_of_list_singleton in Hcontra; rewrite {1}Hcontra in Hb_cgp_in.
          set_solver.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * set_solver.
          * apply elem_of_dom_std_multiple_update in Hcontra.
            destruct Hcontra as [Hcontra|Hcontra].
            ** assert ((cmpt_b_cgp main_cmpt)%a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt))
               ; last set_solver.
               rewrite !elem_of_finz_seq_between in Hcontra |- *.
               pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
               solve_addr.
            ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { subst Winit_C.
      intro Hcontra.
      assert ( (cmpt_b_cgp main_cmpt ^+1)%a ∈ finz.seq_between (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
             ) as Hb_cgp_in.
      { pose proof (cmpt_data_size main_cmpt) as H.
        rewrite elem_of_finz_seq_between.
        rewrite main_data in H; cbn.
        solve_addr+H.
      }
      apply elem_of_dom_std_multiple_update in Hcontra.
      clear -Hcontra Hb_cgp_in C_imports.
      destruct Hcontra as [Hcontra|Hcontra].
      - pose proof switcher_cmpt_disjoints as (Hdis&_); set_solver.
      - pose proof cmpts_disjoints as Hdis.
        apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + assert (cmpt_b_pcc C_cmpt ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
          { pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
            pose proof (cmpt_code_size C_cmpt).
            rewrite elem_of_finz_seq_between; solve_addr.
          }
          rewrite elem_of_list_singleton in Hcontra; rewrite {1}Hcontra in Hb_cgp_in.
          set_solver.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * set_solver.
          * apply elem_of_dom_std_multiple_update in Hcontra.
            destruct Hcontra as [Hcontra|Hcontra].
            ** assert ((cmpt_b_cgp main_cmpt ^+ 1)%a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt))
               ; last set_solver.
               rewrite !elem_of_finz_seq_between in Hcontra |- *.
               pose proof (cmpt_import_size C_cmpt) as Hsize ; rewrite C_imports in Hsize.
               solve_addr.
            ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { done. }

    iModIntro.
    iExists (fun σ _ _ => ( ((gen_heap_interp σ.1.1) ∗ (gen_heap_interp σ.1.2)) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.
    iSplitL "Hspec".
    { iApply (wp_mono with "Hspec"); iIntros (?) "?"; done. }

    iIntros "[ [Hreg' Hsreg'] Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
  Qed.
End Adequacy.

Inductive CmptNames_dle := | B .
Local Instance CmptNames_dle_eq_dec : EqDecision CmptNames_dle.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_dle_finite : finite.Finite CmptNames_dle.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_dle_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_dle; |}.

(** END-TO-END THEOREM *)
Theorem cmdc_adequacy `{Layout: memory_layout}
  (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
  (es: list cap_lang.expr):
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ?.
  set ( cnames := CmptNames_dle_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; heapPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
      ]).
  eapply (@cmdc_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
