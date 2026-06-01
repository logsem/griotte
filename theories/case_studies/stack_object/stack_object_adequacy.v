From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import stack_object stack_object_spec_closure stack_object_spec.
From cap_machine Require Import switcher assert_spec logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import
  region_invariants_revocation region_invariants_allocation world_interp_allocation_compartments.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From cap_machine Require Import disjoint_regions_tactics.
From cap_machine Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From cap_machine Require Import compartment_layout switcher_adequacy adequacy_helpers.

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
                         (b_trusted_stack switcher_cmpt)
                         (e_trusted_stack switcher_cmpt)
                         (b_trusted_stack switcher_cmpt)).

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

  mem = mk_initial_memory mem
  (* instantiating main *)
  ∧ (cmpt_imports main_cmpt) = so_main_imports C_f
  ∧ (cmpt_code main_cmpt) = so_main_code
  ∧ (cmpt_data main_cmpt) = so_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = so_export_table_entries

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) =
  [switcher_entry
   ; WSealed ot_switcher (so_entry_f_sb (cmpt_exp_tbl_pcc main_cmpt)
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
  Context {sts_preg: STS_preG Addr region_type OType Word Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {relpreg: relGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [C]) }.

  Definition flagN : namespace := nroot .@ "so" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "so" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "so" .@ "assert_flag".
  Definition soN : namespace := nroot .@ "so" .@ "code".

  Local Notation ot_switcher := (ot_switcher switcher_cmpt).
  Lemma so_adequacy' `{Layout: @memory_layout MP}
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
                    & C_imports & C_code & C_data & C_exp_tbl
                    & Hstack
                   ).
    set (C_f :=
       (WCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
         (cmpt_exp_tbl_entries_start C_cmpt))
      ).
    set (C_g :=
       (WCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
         ((cmpt_exp_tbl_entries_start C_cmpt) ^+1)%a)
      ).
    set (SO_f :=
          (WCap RO Global
             (cmpt_exp_tbl_pcc main_cmpt) (cmpt_exp_tbl_entries_end main_cmpt)
             (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)
        ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (
       entry_init (
           {[
               (seal_capability C_f ot_switcher) := 0;
               (borrow (seal_capability C_f ot_switcher)) := 0;
               (seal_capability C_g ot_switcher) := 0;
               (borrow (seal_capability C_g ot_switcher)) := 0;
               (seal_capability SO_f ot_switcher) := 2;
               (borrow (seal_capability SO_f ot_switcher)) := 2
           ]}

         )
      ) as (entry_g) "Hentries".

    iMod (@na_alloc Σ na_invg) as (cerise_nais) "Hna".
    pose cerise_na_invs := Build_cerise_na_invs _ na_invg cerise_nais.
    pose ceriseg := CeriseG Σ Hinv cerise_na_invs mem_heapg reg_heapg sreg_heapg entry_g.

    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (world_interp_init ({[ ot_switcher ]} : gset _))
      as (relg stsg seal_storeg) "[Hworld_interp Hseal_store]".

    iDestruct (big_sepS_elements with "Hworld_interp") as "Hworld_C".
    rewrite HCNames.
    pose proof (NoDup_singleton C) as HCNoDup.
    setoid_rewrite elements_list_to_set; auto.
    rewrite !big_sepL_singleton.
    set (W0 := (∅, (∅, ∅), ∅)).

    pose proof (
        @so_init_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _ _ C
      ) as Spec.

    (* Obtain entry resources *)
    assert (C_f ≠ SO_f) as Hneq_Cf_awkf.
    { symmetry.
      pose proof cmpts_disjoints as Hdisjoint.
      apply exported_entry_point_disjoint.
      done.
    }
    assert (C_g ≠ SO_f) as Hneq_Cg_awkf.
    { symmetry.
      pose proof cmpts_disjoints as Hdisjoint.
      apply exported_entry_point_disjoint.
      done.
    }
    assert (C_f ≠ C_g) as Hneq_Cf_Cg.
    { intro H ; subst C_f C_g ; simplify_eq.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      rewrite C_exp_tbl in H1.
      solve_addr+H H1.
    }

    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cf Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cf' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cg Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cg' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_awkf Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_awkf' _]".

    subst C_f C_g SO_f; cbn.
    set (C_f := (SCap RO Global _ _ (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_f' := (SCap RO Local _ _ (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_g := (SCap RO Global _ _ ((cmpt_exp_tbl_entries_start C_cmpt) ^+1)%a)).
    set (C_g' := (SCap RO Local _ _ ((cmpt_exp_tbl_entries_start C_cmpt) ^+1)%a)).
    set (SO_f := (SCap RO Global _ _ (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)).
    set (SO_f' := (SCap RO Local _ _ (cmpt_exp_tbl_pcc main_cmpt ^+ 2)%a)).
    clear Hneq_Cf_Cg Hneq_Cg_awkf Hneq_Cf_awkf.

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
    iMod ( initialise_assert_compartment (Σ := Σ) _ assertN flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* Switcher *)
    rewrite big_sepS_singleton.
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack)".

    (* CMPT C *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ C with "Hcmpt_C")
      as "(HC_imports & HC_code & HC_data & #HC_etbl_pcc & #HC_etbl_cgp & #HC_etbl_entries)".
    iEval (rewrite C_exp_tbl) in "HC_etbl_entries".
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start C_cmpt)).
    2: {
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      rewrite C_exp_tbl in H1; solve_addr+H1.
    }
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start C_cmpt ^+ 1)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      rewrite C_exp_tbl in H1; solve_addr+H1.
    }
    iDestruct "HC_etbl_entries" as "/= [HC_etbl_C_f [HC_etbl_C_g _ ]]".

    (* CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data & Hmain_etbl_PCC & Hmain_etbl_CGP & Hmain_etbl_entries)".
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
    rewrite /so_export_table_entries.
    iAssert (
       (cmpt_exp_tbl_entries_start main_cmpt) ↦ₐ
         WInt (encode_entry_point 2 (length (cmpt_imports main_cmpt ++ SO_main_code_run)))
      )%I with "[Hmain_etbl_entries]" as "Hmain_etbl_entries".
    {
      rewrite /region_pointsto (finz_seq_between_singleton (cmpt_exp_tbl_entries_start main_cmpt)).
      2: {
        pose proof (cmpt_exp_tbl_entries_size main_cmpt) as H.
        by rewrite main_exp_tbl /= in H.
      }
      rewrite main_imports.
      by rewrite big_sepL2_singleton.
    }
    iCombine "Hmain_imports Hmain_code" as "Hmain_code".
    iMod (na_inv_alloc cerise_nais _ soN _ with "Hmain_code") as "#Hmain_code".
    iMod (inv_alloc (export_table_PCCN soN) ⊤
            (cmpt_exp_tbl_pcc main_cmpt
               ↦ₐ WCap RX Global (cmpt_b_pcc main_cmpt) (cmpt_e_pcc main_cmpt)
               (cmpt_b_pcc main_cmpt)
            )%I with "Hmain_etbl_PCC")%I
      as "#Hinv_etbl_PCC".
    iMod (inv_alloc (export_table_CGPN soN) ⊤
            (cmpt_exp_tbl_cgp main_cmpt
               ↦ₐ WCap RW Global (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
               (cmpt_b_cgp main_cmpt)
            )%I with "Hmain_etbl_CGP")%I
      as "#Hinv_etbl_CGP".
    iMod (inv_alloc (export_table_entryN soN (cmpt_exp_tbl_entries_start main_cmpt)) ⊤
            (cmpt_exp_tbl_entries_start main_cmpt
               ↦ₐ WInt (encode_entry_point 2 (length (cmpt_imports main_cmpt ++ SO_main_code_run)))
            )%I with "Hmain_etbl_entries")%I
      as "#Hinv_etbl_entry_awkward".

    (* Initialises the world for C *)
    set (SO'_f := (SCap RO Global
                (cmpt_exp_tbl_pcc main_cmpt)
                (cmpt_exp_tbl_entries_end main_cmpt)
                (cmpt_exp_tbl_entries_start main_cmpt)%a)
        ).
    set (SO'_f' := borrow (WSealable SO'_f)).
    set (W0' := <o[ ot_switcher := {[ WSealable SO_f; WSealable SO_f' ]}]o> W0).

    iAssert (ot_switcher_prop W0' C (WSealable SO_f)) as "#ot_switcher_SO_f".
    {
      subst SO_f.
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

      iApply (stack_object_f_spec _ _ _ _ _ _ _ _ C_f W0' assertN switcherN soN soN)
      ; last iFrame "#"; auto.
      + solve_ndisj.
      + solve_ndisj.
      + solve_ndisj.
      + solve_addr+H0 H1 H2.
      + solve_addr+H3 H4.
    }

    assert (ot_switcher ∉ dom (seal_std W0)) as Hot_notin_W0.
    { by subst W0. }
    iMod
      (world_interp_salloc W0 C ot_switcher_propC ot_switcher {[WSealable SO_f; WSealable SO_f' ]}
        with "[$Hsealed_pred_ot_switcher] [ ] [ ] [$Hworld_C]")
      as "(Hworld_C & Hseal_SO_f)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { subst W0'.
      rewrite normalise_sealed_words_borrow.
      rewrite big_sepS_singleton; iFrame "ot_switcher_SO_f".
    }
    subst W0'; set (W0' := <o[ ot_switcher := {[ WSealable SO_f; WSealable SO_f' ]}]o> W0).

    iAssert ( interp W0' C (WSealed ot_switcher SO_f)) as "#Hinterp_SO".
    { by iEval (rewrite fixpoint_interp1_eq). }

    assert ( (exported_entries_sealable C_cmpt) ≡ₚ [C_f; C_g; C_f'; C_g']) as Hexported_entries_sealable.
    { rewrite /exported_entries_sealable /C_f /C_f' /C_g /C_g'.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1; rewrite C_exp_tbl /= in H1.
      rewrite finz_seq_between_cons; last solve_addr+H1.
      rewrite finz_seq_between_singleton; last solve_addr+H1.
      done.
    }
    assert ( (exported_entries_words C_cmpt) =
             {[WSealable C_f ; borrow (WSealable C_f) ]}
               ∪ {[ WSealable C_g ; borrow (WSealable C_g)]}
           ) as Hexported_entries_words.
    { rewrite /exported_entries_words Hexported_entries_sealable.
      cbn; subst C_f' C_g'; set_solver+.
    }
    assert ( (exported_entries_sealed C_cmpt) =
             {[WSealed ot_switcher C_f
               ; WSealed ot_switcher C_f'
               ; WSealed ot_switcher C_g
               ; WSealed ot_switcher C_g'
             ]}
           ) as Hexported_entries_sealed.
    { rewrite /exported_entries_sealed Hexported_entries_sealable.
      cbn; subst C_f' C_g'; set_solver+.
    }


    iMod (
       alloc_compartment_interp with "[$HC_imports] [$HC_code] [$HC_data] [] [$Hworld_C]"
      ) as "(Hworld_C & #HC_code & #HC_data & _ & #HC_exports)"; eauto.
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { apply Forall_true; intros; done. }
    { rewrite C_imports.

      iIntros "(#HC_code & #HC_data & Hworld_C)".
      match goal with
      | H: _ |- context [  (world_interp_open ?W C) ] => set (Wpre := W)
      end.
      set ( Winter := (std_update_compartment W0' C_cmpt) ).

      iAssert (ot_switcher_prop Winter C (WSealable C_f)) as "#ot_switcher_C_f".
      {
        iApply (ot_switcher_interp _ _ _ _ _ 0 offset_adv_f); eauto; last lia.
        pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
        pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
        rewrite C_exp_tbl in H2.
        solve_addr+H1 H2.
      }
      iAssert (ot_switcher_prop Winter C (WSealable C_g)) as "#ot_switcher_C_g".
      {
        iApply (ot_switcher_interp _ _ _ _ _ 0 offset_adv_g); eauto; last lia.
        pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
        pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
        rewrite C_exp_tbl in H2.
        solve_addr+H1 H2.
      }

      assert ( Winter = <o[ot_switcher:=exported_entries_words C_cmpt]o>Wpre ) as HWinter.
      { rewrite /Winter /Wpre /std_update_compartment Hexported_entries_words; done. }

      iMod
        (world_interp_open_sealing_update' Wpre C _ ot_switcher_propC ot_switcher (exported_entries_words C_cmpt)
          with "[$Hsealed_pred_ot_switcher] [ ] [ ] [$Hworld_C]")
        as "(Hworld_C & #Hseal_switcher)".
      { iIntros (w); iApply mono_priv_ot_switcher. }
      { rewrite -HWinter Hexported_entries_words.
        rewrite normalise_sealed_words_union !normalise_sealed_words_borrow.
        iEval (rewrite union_comm_L); iApply big_sepS_insert_2; first (iFrame "ot_switcher_C_g").
        iApply big_sepS_singleton; iFrame "ot_switcher_C_f".
      }
      rewrite -HWinter.
      iFrame.
      iModIntro.
      rewrite Hexported_entries_sealed Hexported_entries_words.
      rewrite /so_entry_f_sb /SO_f.
      subst C_g; set (C_g := (SCap RO Global _ _ ((cmpt_exp_tbl_entries_start C_cmpt) ^+1)%a)).
      iAssert (interp Winter C (WSealed switcher.ot_switcher C_g)) as "#Hinterp_C_g".
      { iEval (rewrite fixpoint_interp1_eq /= /interp_sb).
        iApply (sts_seals_std_weaken with "Hseal_switcher"); set_solver+.
      }

      iSplitR "Hseal_switcher".
      (* Interp of imports *)
      - (* Switcher cross-compartment *)
        iApply big_sepL_cons; iSplitL.
        { iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done. }

        (* SO.f *)
        iApply big_sepL_cons; iSplitL.
        { iSplit.
          * pose proof (cmpt_exp_tbl_pcc_size main_cmpt) as H0.
            pose proof (cmpt_exp_tbl_cgp_size main_cmpt) as H1.
            replace (cmpt_exp_tbl_entries_start main_cmpt)
              with ((cmpt_exp_tbl_pcc main_cmpt) ^+ 2)%a by solve_addr+H0 H1.
            iApply (interp_monotone_sd W0' Winter); auto.
            iPureIntro.
            apply related_sts_pub_priv_world.
            subst Winter.
            eapply std_update_compartment_pub; eauto
            ; apply Forall_true; intros; done.
          * iIntros (??) "!> % ?".
            rewrite /so_exp_tbl_entry_f.
            iApply interp_monotone_sd; auto.
        }

        (* C_g *)
        iApply big_sepL_cons; iSplitL; last done.
        iSplit; first done.
        iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto.

      (* Interp of exports *)
      - iEval (rewrite union_comm_L)
        ; iApply big_sepS_insert_2
        ; first (iEval (rewrite fixpoint_interp1_eq /= /interp_sb)
              ; iApply (sts_seals_std_weaken with "Hseal_switcher"); set_solver+).
        iEval (rewrite union_comm_L)
        ; iApply big_sepS_insert_2
        ; first (iEval (rewrite fixpoint_interp1_eq /= /interp_sb)
              ; iApply (sts_seals_std_weaken with "Hseal_switcher"); set_solver+).
        iEval (rewrite union_comm_L)
        ; iApply big_sepS_insert_2
        ; first (iEval (rewrite fixpoint_interp1_eq /= /interp_sb)
              ; iApply (sts_seals_std_weaken with "Hseal_switcher"); set_solver+).
        iApply big_sepS_singleton
        ; iEval (rewrite fixpoint_interp1_eq /= /interp_sb)
        ; iApply (sts_seals_std_weaken with "Hseal_switcher"); set_solver+.
    }

    match goal with
    | H: _ |- context [  (world_interp ?W C) ] => set (W1 := W)
    end.

    assert (Forall (fun a => a ∉ dom (std W1))
              (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))) as Hswitcher_W4.
    { apply Forall_forall; intros a Ha; cbn.
      pose proof switcher_cmpt_disjoints as (_ & Hc).
      rewrite not_elem_of_dom.
      unshelve eapply switcher_cmpt_disjoint_std_update_compartment; eauto.
    }
    iMod ( world_interp_extend_temp_sepL2 _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             (stack_content switcher_cmpt)
             RWL interpC
           with "Hworld_C [Hstack]")
           as "(Hworld_C & #Hrel_stk_C)".
    { done. }
    { eapply Forall_impl; eauto.
      intros a Ha.
      by rewrite -not_elem_of_dom.
    }
    { iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "Hstack").
      intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
      pose proof (Forall_lookup_1 _ _ _ _ Hstack Hv2) as Hncap.
      destruct v2; [| by inversion Hncap..].
      rewrite fixpoint_interp1_eq /=.
      iSplit; eauto.
      iSplit; eauto.
      rewrite mono_temporary_eq; cbn; iApply future_pub_mono_interp_z.
    }

    match goal with
    | H: _ |- context [  (world_interp ?W C) ] => set (Winit_C := W)
    end.
    assert (related_sts_priv_world W1 Winit_C) as Hrelated_pub_W1_Winit_C.
    { apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple; auto.
    }

    iAssert (interp Winit_C C
               (WCap RX Global (cmpt_b_pcc C_cmpt) (cmpt_e_pcc C_cmpt) (cmpt_b_pcc C_cmpt)%a)
            )%I as "#Hinterp_pcc_C".
    { iApply interp_monotone_nl; eauto. }

    iAssert (interp Winit_C C
               (WCap RW Global (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt) (cmpt_b_cgp C_cmpt)%a)
            )%I as "#Hinterp_cgp_C".
    { iApply interp_monotone_nl; eauto. }

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
        apply list_elem_of_lookup_2 in Ha.
        rewrite std_sta_update_multiple_lookup_in_i; auto.
      }
      iSplit; last done.
      iApply (monoReq_interp _ _ _ _ Temporary); done.
    }

    iAssert
      ( interp Winit_C C (WSealed ot_switcher C_f) )%I as "Hinterp_C_f".
    { rewrite Hexported_entries_sealed.
      iDestruct (big_sepS_elem_of_acc _ _ (WSealed ot_switcher C_f) with "HC_exports") as "[Hinterp_C_f _]"
      ; first set_solver+.
      iApply interp_monotone_sd; eauto.
    }

    iClear "HC_etbl_pcc HC_etbl_cgp HC_etbl_C_f HC_etbl_C_g HC_code HC_data".

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
                  _ (cmpt_exp_tbl_entries_end main_cmpt)
                  _ _ [] [] assertN switcherN soN
                 with "[ $Hassert $Hswitcher $Hmain_code
                         $Hinv_etbl_PCC $Hinv_etbl_CGP $Hinv_etbl_entry_awkward
                         $Hna
                         $Hworld_C
                         $HPC $Hcgp $Hcsp $Hreg
                         $Hcstk_frag $Hinterp_stack_C
                         $Hinterp_C_f $Hentry_Cf $Hentry_awkf $Hentry_awkf'
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

Inductive CmptNames_so := | B .
Local Instance CmptNames_so_eq_dec : EqDecision CmptNames_so.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_so_finite : finite.Finite CmptNames_so.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_so_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_so; |}.

(** END-TO-END THEOREM *)
Theorem so_adequacy `{Layout: memory_layout}
  (reg reg': Reg) (sreg sreg': SReg) (m m': Mem)
  (es: list cap_lang.expr)
  :
  is_initial_registers reg →
  is_initial_sregisters sreg →
  is_initial_memory m →
  rtc erased_step ([Seq (Instr Executable)], (reg, sreg, m)) (es, (reg', sreg', m')) →
  m' !! (flag_assert assert_cmpt) = Some (WInt 0%Z).
Proof.
  intros ? ? ? ?.
  set ( cnames := CmptNames_so_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type OType Word ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * Word)
      ]).
  eapply (@so_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
