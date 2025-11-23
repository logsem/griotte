From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import vae vae_helper vae_spec_closure vae_spec.
From cap_machine Require Import switcher assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From cap_machine Require Import compartment_layout switcher_adequacy.
From cap_machine Require Import disjoint_regions_tactics.
From cap_machine Require Import interp_switcher_call interp_switcher_return.

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
  vae_main_imports
    b_switcher e_switcher a_switcher_call ot_switcher
    (b_assert assert_cmpt) (e_assert assert_cmpt) C_f
  ∧ (cmpt_code main_cmpt) = (vae_main_code ot_switcher)
  ∧ (cmpt_data main_cmpt) = vae_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = vae_export_table_entries

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) =
  [switcher_entry
   ; WSealed ot_switcher (vae_entry_awkward_sb (cmpt_exp_tbl_pcc main_cmpt) (cmpt_exp_tbl_entries_end main_cmpt))]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data C_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (encode_entry_point 0 1)]

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

  Definition flagN : namespace := nroot .@ "vae" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "vae" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "vae" .@ "assert_flag".
  Definition vaeN : namespace := nroot .@ "vae" .@ "code".

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
    set (awk_f :=
          (WCap RO Global
             (cmpt_exp_tbl_pcc main_cmpt) (cmpt_exp_tbl_entries_end main_cmpt)
             (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)
        ).
    assert (C_f ≠ awk_f) as Hneq_entries.
    { intro H ; subst awk_f C_f ; simplify_eq.
      pose proof cmpts_disjoints as Hdisjoint.
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
      assert (
          cmpt_exp_tbl_region main_cmpt  ## cmpt_exp_tbl_region C_cmpt
        ) as Hdis by set_solver+Hdisjoint.
      rewrite /cmpt_exp_tbl_region in Hdis.
      apply stdpp_extra.list_to_set_disj in Hdis.
      rewrite H H0 in Hdis.
      assert (
          list_to_set
            (finz.seq_between (cmpt_exp_tbl_pcc main_cmpt) (cmpt_exp_tbl_entries_end main_cmpt))
            ≠ (∅ : gset Addr)
        ) as Hemp; [|set_solver+Hdis Hemp].
      pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hc''.
      rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
      set_solver+.
    }

    iMod (
       entry_init (
           {[
               (seal_capability C_f ot_switcher) := 0;
               (borrow (seal_capability C_f ot_switcher)) := 0;
               (seal_capability awk_f ot_switcher) := 1;
               (borrow (seal_capability awk_f ot_switcher)) := 1
           ]}

         )
      ) as (entry_g) "Hentries".
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cf Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst awk_f C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Cf' Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst awk_f C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_awkf Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst awk_f C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_awkf' _]"
    ; repeat (rewrite delete_insert_ne ; last (subst awk_f C_f ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    subst C_f awk_f; cbn.
    set (C_f := (SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_f' := (SCap RO Local (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    set (awk_f :=
          (SCap RO Global (cmpt_exp_tbl_pcc main_cmpt)
                       (cmpt_exp_tbl_entries_end main_cmpt) (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)
        ).
    set (awk_f' :=
          (SCap RO Local (cmpt_exp_tbl_pcc main_cmpt)
                        (cmpt_exp_tbl_entries_end main_cmpt) (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)
        ).

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
        @vae_init_spec Σ ceriseg seal_storeg _ _ _ logrel_na_invs _ _  switcher_layout_g C
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
    rewrite C_imports.
    iEval (rewrite /mkregion) in "HC_imports".
    rewrite /cmpt_cgp_mregion.
    iDestruct (mkregion_prepare with "[HC_code]") as ">HC_code"; auto.
    { apply (cmpt_code_size C_cmpt). }
    iDestruct (mkregion_prepare with "[HC_data]") as ">HC_data"; auto.
    { apply (cmpt_data_size C_cmpt). }
    iDestruct (mkregion_prepare with "[HC_imports]") as ">HC_imports"; auto.
    { pose proof (cmpt_import_size C_cmpt) as H ; cbn in *.
      by rewrite C_imports in H.
    }
    iDestruct (mkregion_prepare with "[Hstack]") as ">Hstack"; auto.
    { apply (stack_size switcher_cmpt). }

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
    rewrite /cmpt_exp_tbl_mregion.
    iDestruct (big_sepM_union with "Hmain_etbl") as "[Hmain_etbl Hmain_etbl_entries]".
    { eapply cmpt_exp_tbl_entries_disjoint ; eauto. }
    iDestruct (big_sepM_union with "Hmain_etbl") as "[Hmain_etbl_PCC Hmain_etbl_CGP]".
    { eapply cmpt_exp_tbl_pcc_cgp_disjoint ; eauto. }
    iDestruct (mkregion_prepare with "[Hmain_imports]") as ">Hmain_imports"; auto.
    { apply (cmpt_import_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_code]") as ">Hmain_code"; auto.
    { apply (cmpt_code_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_data]") as ">Hmain_data"; auto.
    { apply (cmpt_data_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_etbl_PCC]") as ">Hmain_etbl_PCC"; auto.
    { apply (cmpt_exp_tbl_pcc_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_etbl_CGP]") as ">Hmain_etbl_CGP"; auto.
    { apply (cmpt_exp_tbl_cgp_size main_cmpt). }
    iDestruct (mkregion_prepare with "[Hmain_etbl_entries]") as ">Hmain_etbl_entries"; auto.
    { apply (cmpt_exp_tbl_entries_size main_cmpt). }
    iAssert (
       [[(cmpt_b_pcc main_cmpt),(cmpt_a_code main_cmpt)]]↦ₐ[[cmpt_imports main_cmpt]]
     )%I with "[Hmain_imports]" as "Hmain_imports"; first done.
    iAssert (
       [[(cmpt_b_cgp main_cmpt),(cmpt_e_cgp main_cmpt)]]↦ₐ[[cmpt_data main_cmpt]]
     )%I with "[Hmain_data]" as "Hmain_data"; first done.
    iDestruct (region_pointsto_single with "Hmain_data") as "[%v [Hcgp_b %Hv] ]".
    { pose proof (cmpt_data_size main_cmpt) as H.
      rewrite main_data in H.
      solve_addr+H.
    }
    rewrite main_data /vae_main_data in Hv; simplify_eq.
    iAssert (
      codefrag (cmpt_a_code main_cmpt) (cmpt_code main_cmpt)
     )%I with "[Hmain_code]" as "Hmain_code".
    { rewrite /codefrag.
      replace (cmpt_a_code main_cmpt ^+ length (cmpt_code main_cmpt))%a
        with (cmpt_e_pcc main_cmpt).
      2: { pose proof (cmpt_code_size main_cmpt) as H ; solve_addr+H. }
      done.
    }
    rewrite main_imports main_code.
    rewrite main_exp_tbl.
    iAssert (
       (cmpt_exp_tbl_pcc main_cmpt) ↦ₐ
         WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt) (cmpt_b_pcc main_cmpt)
      )%I with "[Hmain_etbl_PCC]" as "Hmain_etbl_PCC".
    {
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc main_cmpt)).
      2: { apply (cmpt_exp_tbl_pcc_size main_cmpt). }
      by rewrite big_sepL2_singleton.
    }
    iAssert (
       (cmpt_exp_tbl_cgp main_cmpt) ↦ₐ
         WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt) (cmpt_b_cgp main_cmpt)
      )%I with "[Hmain_etbl_CGP]" as "Hmain_etbl_CGP".
    {
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp main_cmpt)).
      2: { apply (cmpt_exp_tbl_cgp_size main_cmpt). }
      by rewrite big_sepL2_singleton.
    }
    rewrite /vae_export_table_entries.
    iAssert (
       (cmpt_exp_tbl_entries_start main_cmpt) ↦ₐ
         WInt (encode_entry_point 1 (length (cmpt_imports main_cmpt ++ VAE_main_code_init)))
      )%I with "[Hmain_etbl_entries]" as "Hmain_etbl_entries".
    {
      rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start main_cmpt)).
      2: {
        pose proof (cmpt_exp_tbl_entries_size main_cmpt) as H.
        by rewrite main_exp_tbl /= in H.
      }
      rewrite main_imports.
      by rewrite big_sepL2_singleton.
    }
    iCombine "Hmain_imports Hmain_code" as "Hmain_code".
    iMod (na_inv_alloc logrel.logrel_nais _ vaeN _ with "Hmain_code") as "#Hmain_code".
    iMod (inv_alloc (export_table_PCCN vaeN) ⊤
            (cmpt_exp_tbl_pcc main_cmpt
               ↦ₐ WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt)
               (cmpt_b_pcc main_cmpt)
            )%I with "Hmain_etbl_PCC")%I
      as "#Hinv_etbl_PCC".
    iMod (inv_alloc (export_table_CGPN vaeN) ⊤
            (cmpt_exp_tbl_cgp main_cmpt
               ↦ₐ WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
               (cmpt_b_cgp main_cmpt)
            )%I with "Hmain_etbl_CGP")%I
      as "#Hinv_etbl_CGP".
    iMod (inv_alloc (export_table_entryN vaeN (cmpt_exp_tbl_entries_start main_cmpt)) ⊤
            (cmpt_exp_tbl_entries_start main_cmpt
               ↦ₐ WInt (encode_entry_point 1 (length (cmpt_imports main_cmpt ++ VAE_main_code_init)))
            )%I with "Hmain_etbl_entries")%I
      as "#Hinv_etbl_entry_awkward".

    (* Initialises the world for C *)
    set (W0 := (∅, (∅, ∅))).
    iAssert (region W0 C) with "[HRELS_C]" as "Hr_C".
    { rewrite region_eq /region_def. iExists ∅, ∅. iFrame.
      rewrite /= !dom_empty_L //. repeat iSplit; eauto.
      rewrite /region_map_def. by rewrite big_sepM_empty. }


    (* Allocate the custom invariant *)
    iDestruct (sts_alloc_loc _ C false awk_rel_pub awk_rel_priv with "Hsts_C")
      as ">(Hsts_C & %Hloc_fresh & %Hcus_fresh & Hst_i & #Hrel_i)".
    set (i := (fresh_cus_name W0)).
    set (W1 := (<l[i:=false,(awk_rel_pub, awk_rel_priv)]l>W0)).
    assert (related_sts_priv_world W0 W1) as Hpriv_W0_W1.
    { subst W1 i.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_world_fresh_loc; eauto.
    }

    iMod (update_region_revoked_update_loc with "Hsts_C Hr_C") as "[Hr_C Hsts_C]"; auto.
    { by intros Ha Ha'. }

    iDestruct (inv_alloc awkN _ (awk_inv C i _) with "[Hcgp_b Hst_i]") as ">#Hawk_inv".
    { iExists false; iFrame. }

    iAssert (
        interp W1 C
          (WSealed ot_switcher
             (SCap RO Global
                (cmpt_exp_tbl_pcc main_cmpt)
                (cmpt_exp_tbl_entries_end main_cmpt)
                (cmpt_exp_tbl_entries_start main_cmpt)%a))
      )%I as "#Hinterp_VAE".
    {
      iEval (rewrite main_imports) in "Hinv_etbl_entry_awkward".
      pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size main_cmpt) as H2.
      pose proof (cmpt_import_size main_cmpt) as H3.
      pose proof (cmpt_code_size main_cmpt) as H4.
      pose proof (cmpt_data_size main_cmpt) as H5.
      rewrite main_exp_tbl /= in H2.
      rewrite main_imports in H3.
      rewrite main_code in H4.
      rewrite main_data in H5.
      replace (cmpt_exp_tbl_entries_start main_cmpt)
        with ((cmpt_exp_tbl_pcc main_cmpt) ^+ 2)%a by solve_addr+H0 H1.
      replace (cmpt_exp_tbl_cgp main_cmpt)
        with (cmpt_exp_tbl_pcc main_cmpt ^+ 1)%a by solve_addr+H0.
      iApply (vae_awkward_safe
                _ _  _
                _ _
                _ _
                _ _
                _ _ W1 assertN switcherN vaeN vaeN
             ); try iFrame "#"; eauto.
      + solve_ndisj.
      + solve_ndisj.
      + solve_ndisj.
      + solve_addr+H0 H1 H2.
      + solve_addr+H3 H4.
    }

    iMod (extend_region_perm_sepL2 _ W1 C
            (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
            (cmpt_code C_cmpt)
            RX interpC
           with "Hsts_C Hr_C [HC_code]") as "(Hr_C & #HC_code & Hsts_C)".
    { done. }
    { apply Forall_true. intros.
      by rewrite lookup_empty.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HC_code]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ C_code Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite /interpC /safeC fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply future_priv_mono_interp_z.
      - iFrame.
    }
    set (W2 := std_update_multiple _ _ _).
    assert (related_sts_pub_world W1 W2) as Hrelated_pub_W1_W2.
    { apply related_sts_pub_update_multiple.
      apply Forall_forall.
      intros a Ha.
      pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size C_cmpt) as Hsize_data.
      pose proof (cmpt_code_size C_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
    }

    iMod (extend_region_perm_sepL2 _ _ C
            (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
            (cmpt_data C_cmpt)
            RW interpC
           with "Hsts_C Hr_C [HC_data]") as "(Hr_C & #HC_data & Hsts_C)".
    { done. }
    { apply Forall_forall. intros a Ha.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size C_cmpt) as Hsize_data.
      pose proof (cmpt_code_size C_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
      apply list_to_set_disj_2 in Hdisjoint.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint.
      intro Ha'.
      apply (Hdisjoint a); auto.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "HC_data").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ C_data Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite /interpC /safeC fixpoint_interp1_eq /=.
      iSplit; eauto.
      iApply future_priv_mono_interp_z.
    }
    set (W3 := std_update_multiple _ _ _).
    assert (related_sts_pub_world W2 W3) as Hrelated_pub_W2_W3.
    { apply related_sts_pub_update_multiple.
      apply Forall_forall.
      intros a Ha.
      subst W2.
      intro Ha'.
      apply elem_of_dom_std_multiple_update in Ha' as [Ha' | Ha']; last set_solver.
      pose proof (cmpt_cgp_disjoint C_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size C_cmpt) as Hsize_data.
      pose proof (cmpt_code_size C_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
      apply list_to_set_disj_2 in Hdisjoint.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint.
      apply (Hdisjoint a); auto.
    }

    iMod (extend_region_perm_sepL2 _ _ C
            [cmpt_b_pcc C_cmpt;((cmpt_b_pcc C_cmpt)^+1)%a]
            (cmpt_imports C_cmpt)
            RX interpC
           with "Hsts_C Hr_C [HC_imports]") as "(Hr_C & (#HC_imports_0 & #HC_imports_1 & _) & Hsts_C)".
    { done. }
    { apply Forall_forall.
      intros a Ha.
      rewrite elem_of_cons elem_of_list_singleton in Ha.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      + rewrite std_sta_update_multiple_lookup_same_i; auto.
        pose proof (cmpt_import_size C_cmpt) as HC.
        apply not_elem_of_finz_seq_between.
        rewrite C_imports in HC.
        destruct Ha; simplify_eq; left; solve_addr+HC.
      + pose proof (cmpt_disjointness C_cmpt) as HC.
        apply disjoint_regions_tactics.disjoint_list_cons in HC
        ; destruct HC as [HC _].
        rewrite union_list_cons in HC.
        cbn in HC.
        assert (
            finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
              ## finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)
          ) as HC' by set_solver+HC
        ; clear HC.
        intro Hcontra ; eapply HC'; eauto.
        pose proof (cmpt_import_size C_cmpt) as H.
        rewrite C_imports /= in H.
        pose proof (cmpt_code_size C_cmpt) as H'.
        destruct Ha; simplify_eq; apply elem_of_finz_seq_between; solve_addr+H H'.
    }
    {
      rewrite C_imports; cbn; iFrame.
      replace (finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_a_code C_cmpt))
        with [(cmpt_b_pcc C_cmpt); ((cmpt_b_pcc C_cmpt)^+1)%a]; cycle 1.
      { pose proof (cmpt_import_size C_cmpt) as H.
        rewrite C_imports /= in H.
        rewrite finz_seq_between_cons; last solve_addr+H.
        rewrite finz_seq_between_cons; last solve_addr+H.
        rewrite finz_seq_between_empty; last solve_addr+H.
        done.
      }
      rewrite big_sepL2_cons big_sepL2_singleton.
      iDestruct "HC_imports" as "[Hswitcher_C Hawkward_C]".
      iSplitL "Hswitcher_C".
      + iFrame.
        rewrite /interpC /safeC /=.
        iSplit; first iApply interp_switcher_call; eauto.
        iModIntro.
        iIntros (???) "?"; iApply interp_switcher_call; eauto.
      + iFrame.
        rewrite /interpC /safeC /=.
        iSplit.
        * pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as H0.
          pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as H1.
          replace (cmpt_exp_tbl_entries_start main_cmpt)
            with ((cmpt_exp_tbl_pcc main_cmpt) ^+ 2)%a by solve_addr+H0 H1.
          iApply interp_monotone_sd; auto.
          iPureIntro.
          apply related_sts_pub_priv_world.
          eapply related_sts_pub_trans_world; eauto.
        * iIntros (??) "!> % ?".
          rewrite /vae_exp_tbl_entry_awkward.
          cbn.
          iApply interp_monotone_sd; auto.
    }

    iMod ( extend_region_temp_sepL2 _ _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             (stack_content switcher_cmpt)
             RWL interpC
           with "Hsts_C Hr_C [Hstack]")
           as "(Hr_C & #Hrel_stk_C & Hsts_C)".
    { done. }
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
        rewrite elem_of_finz_seq_between in Hcontra.
        apply elem_of_finz_seq_between; solve_addr+H H' Hcontra.
    }
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


    iAssert (interp Winit_C C
               (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a)
            )%I as "#Hinterp_pcc_C".
    { iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      rewrite finz_seq_between_cons in Ha.
      2: {
        pose proof (cmpt_import_size C_cmpt) as H1.
        pose proof (cmpt_code_size C_cmpt) as H2.
        rewrite C_imports /= in H1.
        solve_addr.
      }
      rewrite finz_seq_between_cons in Ha.
      2: {
        pose proof (cmpt_import_size C_cmpt) as H1.
        pose proof (cmpt_code_size C_cmpt) as H2.
        rewrite C_imports /= in H1.
        solve_addr.
      }
      pose proof (cmpt_import_size C_cmpt) as Himport_C.
      rewrite C_imports /= in Himport_C.
      replace ((cmpt_b_pcc C_cmpt ^+ 1) ^+1 )%a with
        (cmpt_a_code C_cmpt) in Ha by solve_addr+Himport_C.
      iExists RX, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit.
      { destruct k; cbn in Ha ; simplify_eq; first iFrame "HC_imports_0".
        destruct k; cbn in Ha ; simplify_eq; first iFrame "HC_imports_1".
        rewrite (big_sepL_lookup _ _ _ a); eauto.
      }
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first done.
      assert ((std Winit_C) !! a = Some Permanent).
      {
        subst Winit_C.
        apply elem_of_list_lookup_2 in Ha.
        rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
        { pose proof switcher_cmpt_disjoints as ( _ & Hdis_switcher_cmptC).
          rewrite /switcher_cmpt_disjoint /cmpt_switcher_region /cmpt_region in Hdis_switcher_cmptC.
          assert
            (cmpt_switcher_stack_region switcher_cmpt ## cmpt_pcc_region C_cmpt)
              as Hdis
              by (set_solver+Hdis_switcher_cmptC).
          rewrite /cmpt_pcc_region /cmpt_switcher_stack_region in Hdis.
          intro Hcontra.
          replace (cmpt_a_code C_cmpt) with ((cmpt_b_pcc C_cmpt ^+ 1) ^+ 1)%a in Ha by solve_addr+Himport_C.
          pose proof (cmpt_import_size C_cmpt) as H1.
          pose proof (cmpt_code_size C_cmpt) as H2.
          rewrite C_imports /= in H1.
          rewrite -!finz_seq_between_cons in Ha; first (apply (Hdis a); auto); solve_addr+H1 H2.
        }
        rewrite elem_of_cons in Ha.
        destruct Ha as [ Ha | Ha ]; simplify_eq.
        + rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
        + rewrite elem_of_cons in Ha.
          destruct Ha as [ Ha | Ha ]; simplify_eq.
          ++ rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
          ++ rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
             { intro Hcontra.
               rewrite !elem_of_cons elem_of_empty in Hcontra.
               destruct Hcontra as [ -> | [ -> | ] ]; last done.
               all: apply elem_of_finz_seq_between in Ha.
               all: solve_addr+Himport_C Ha.
             }
          rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
          { intro Hcontra.
            assert (
                (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt))
                  ##
                  (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
              ) as Hdis; last set_solver+Ha Hcontra Hdis.
              clear.
              pose proof (cmpt_cgp_disjoint C_cmpt) as Hdis.
              rewrite /cmpt_pcc_mregion /cmpt_cgp_mregion in Hdis.
              rewrite -/(cmpt_pcc_mregion C_cmpt) -/(cmpt_cgp_mregion C_cmpt) in Hdis.
              rewrite map_disjoint_dom in Hdis.
              rewrite dom_cmpt_pcc_mregion dom_cmpt_cgp_mregion /cmpt_pcc_region /cmpt_cgp_region in Hdis.
              rewrite -list_to_set_disj in Hdis.
              assert (
                  finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt) ⊆ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)
                ); last set_solver.
              intros a Ha.
              rewrite !elem_of_finz_seq_between in Ha |- *.
              pose proof (cmpt_import_size C_cmpt).
              solve_addr.
          }
          rewrite std_sta_update_multiple_lookup_in_i; auto; set_solver+.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
    }

    iAssert (interp Winit_C C
               (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a)
            )%I as "#Hinterp_cgp_C".
    { iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      rewrite (big_sepL_lookup _ (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt))
                 k a); eauto.
      iFrame "HC_data".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      assert ((std Winit_C) !! a = Some Permanent).
     { subst Winit_C.
        apply elem_of_list_lookup_2 in Ha.
        assert (a ∉ finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt)).
        { intro Hcontra.
          clear -Ha Hcontra.
          pose proof switcher_cmpt_disjoints as (_&Hdis).
          set_solver.
        }
        assert (a ∉ [cmpt_b_pcc C_cmpt; (cmpt_b_pcc C_cmpt ^+1)%a]).
        { intro Hcontra.
          clear -Ha Hcontra C_imports.
          pose proof (cmpt_disjointness C_cmpt) as Hdis.
          apply disjoint_list_cons in Hdis as [Hdis _].
          rewrite union_list_cons disjoint_union_r in Hdis.
          destruct Hdis as [Hdis _].
          rewrite !elem_of_cons elem_of_empty in Hcontra.
          assert ( cmpt_b_pcc C_cmpt ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
          {
            apply elem_of_finz_seq_between.
            pose proof (cmpt_import_size C_cmpt) as Hsize; rewrite C_imports in Hsize.
            pose proof (cmpt_code_size C_cmpt).
            solve_addr.
          }
          assert ( (cmpt_b_pcc C_cmpt ^+1)%a ∈ finz.seq_between (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt)).
          {
            apply elem_of_finz_seq_between.
            pose proof (cmpt_import_size C_cmpt) as Hsize; rewrite C_imports in Hsize.
            pose proof (cmpt_code_size C_cmpt).
            solve_addr.
          }
          destruct Hcontra as [ -> | [ -> | ] ]; set_solver.
        }
        repeat (rewrite std_sta_update_multiple_lookup_same_i; last done).
        rewrite std_sta_update_multiple_lookup_in_i; auto.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Permanent); done.
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
    { iApply (ot_switcher_interp_entry _ _ _ _ 0 1 _ _ (nroot.@C)
               with "[$] [$] [$] [$] [$] [$] [$] [$]"); eauto; last lia.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
      rewrite C_exp_tbl in H2.
      solve_addr+H1 H2.
    }
    iClear "HC_etbl_pcc HC_etbl_cgp HC_etbl_entries HC_code HC_data Hinterp_pcc_C Hinterp_cgp_C".


    (* Extract registers *)
    destruct Hreg as (HPC & Hcgp & Hcsp & Hreg).
    iDestruct (big_sepM_delete _ _ PC with "Hreg") as "[HPC Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ cgp with "Hreg") as "[Hcgp Hreg]"; first by simplify_map_eq.
    iDestruct (big_sepM_delete _ _ csp with "Hreg") as "[Hcsp Hreg]"; first by simplify_map_eq.

    replace (cmpt_exp_tbl_entries_start main_cmpt) with
      (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a.
    2: { pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as Hsize_pcc.
         pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as Hsize_cgp.
         pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hsize_entries.
         rewrite main_exp_tbl /= in Hsize_entries.
         solve_addr+Hsize_pcc Hsize_cgp Hsize_entries.
    }
    replace (cmpt_exp_tbl_cgp main_cmpt) with ((cmpt_exp_tbl_pcc main_cmpt) ^+ 1)%a.
    2: { pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as Hsize_pcc.
         pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as Hsize_cgp.
         solve_addr+Hsize_pcc Hsize_cgp.
    }
    rewrite main_imports.

    iPoseProof (Spec _ _ _ _ _ _ _ _
                  _ (cmpt_exp_tbl_entries_end main_cmpt) _ _ _
                  _ _ [] [] assertN switcherN vaeN
                 with "[ $Hassert $Hswitcher $Hmain_code
                         $Hinv_etbl_PCC $Hinv_etbl_CGP $Hinv_etbl_entry_awkward
                         $Hna
                         $Hr_C $Hsts_C
                         $HPC $Hcgp $Hcsp $Hreg
                         $Hinterp_C $Hcstk_frag
                         $Hentry_Cf $Hentry_awkf $Hentry_awkf'
                         $Hsealed_pred_ot_switcher
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
    { solve_ndisj. }
    { solve_ndisj. }
    { pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as Hsize_pcc.
      pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as Hsize_cgp.
      pose proof (cmpt_exp_tbl_entries_size main_cmpt) as Hsize_entries.
      rewrite main_exp_tbl /= in Hsize_entries.
      solve_addr+Hsize_pcc Hsize_cgp Hsize_entries.
    }
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
    { subst Winit_C W1.
      rewrite !std_update_multiple_loc_sta.
      by simplify_map_eq.
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
  set ( cnames := CmptNames_vae_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; heapPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
      ]).
  eapply (@cmdc_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
