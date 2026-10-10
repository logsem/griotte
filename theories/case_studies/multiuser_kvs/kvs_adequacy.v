From iris.proofmode Require Import proofmode.
From griotte Require Import logrel interp_weakening monotone.
From griotte Require Import
  kvs kvs_main kvs_preamble kvs_main_spec kvs_spec_addOrUpdate_safe kvs_spec_read_safe kvs_spec_erase_safe.
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

    (* kvs compartment *)
    kvs_cmpt : cmpt ;

    ot_kvs : OType;
    ot_kvs_size : (ot_kvs < ot_kvs ^+ 1)%ot;
    ot_kvs_disjoint : ot_kvs ≠ (ot_switcher switcher_cmpt) ;

    kvs_user_key_K : user_key_t;
    kvs_user_key_B : user_key_t;
    kvs_user_key_disjoints : kvs_user_key_K ≠ kvs_user_key_B;

    (* adv compartments B *)
    B_cmpt : cmpt ;
    offset_adv_f : nat;
    offset_adv_f_valid :
      is_Some (cmpt_b_pcc B_cmpt + offset_adv_f%nat)%a;

    (* disjointness *)
    cmpts_disjoints :
    main_cmpt ## B_cmpt ∧
    main_cmpt ## kvs_cmpt ∧
    kvs_cmpt ## B_cmpt ;

    switcher_cmpt_disjoints :
    switcher_cmpt_disjoint main_cmpt switcher_cmpt ∧
    switcher_cmpt_disjoint kvs_cmpt switcher_cmpt ∧
    switcher_cmpt_disjoint B_cmpt switcher_cmpt ;

    assert_cmpt_disjoints :
    assert_cmpt_disjoint main_cmpt assert_cmpt ∧
    assert_cmpt_disjoint kvs_cmpt assert_cmpt ∧
    assert_cmpt_disjoint B_cmpt assert_cmpt ;

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
    mk_initial_cmpt kvs_cmpt ∪
    mk_initial_cmpt B_cmpt.

(** We describe the initial register file. *)
Definition is_initial_registers `{memory_layout} := is_initial_registers_of switcher_cmpt main_cmpt.

(** We describe the initial sregister file, ie., mtdc,
    which contains the trusted stack capability. *)
Definition is_initial_sregisters `{memory_layout} := is_initial_sregisters_of switcher_cmpt.

Local Instance memory_layout_kvs_layout `{memory_layout} : kvsLayout.
Proof.
  refine (@mkKvsLayout ot_kvs
            (cmpt_b_pcc kvs_cmpt) (cmpt_a_code kvs_cmpt) (cmpt_e_pcc kvs_cmpt)
            (cmpt_b_cgp kvs_cmpt) (cmpt_e_cgp kvs_cmpt)
            (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)).
Defined.

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
  let kvs_user_key_K_addr := cmpt_b_static_sealed main_cmpt in
  let kvs_user_key_B_addr := cmpt_b_static_sealed B_cmpt in

  mem = mk_initial_memory ∧
  (* instantiating main *)
  (cmpt_imports main_cmpt) =
  (kvs_main_imports
    kvs_user_key_K_addr
    b_switcher e_switcher
    a_switcher_call ot_switcher
    (b_assert assert_cmpt) (e_assert assert_cmpt)
    B_f) ∧
  (cmpt_code main_cmpt) = kvs_main_code ∧
  (cmpt_data main_cmpt) = (kvs_main_data) ∧
  (cmpt_static_sealed main_cmpt) = (kvs_main_static_sealed kvs_user_key_K) ∧
  (cmpt_exp_tbl_entries main_cmpt) = [] ∧

  (* instantiating kvs *)
  (cmpt_imports kvs_cmpt) = kvs_imports b_switcher e_switcher a_switcher_call ot_switcher ∧
  (cmpt_code kvs_cmpt) = kvs_service_instrs ∧
  (cmpt_data kvs_cmpt) = kvs_data ∧
  (cmpt_static_sealed kvs_cmpt) = [] ∧
  (cmpt_exp_tbl_entries kvs_cmpt) = kvs_export_table_entries ∧

  (* instantiating B *)
  (cmpt_imports B_cmpt) = [
      switcher_entry;
      WSealed ot_switcher (KVS_addOrUpdate Global);
      WSealed ot_switcher (KVS_read Global);
      WSealed ot_switcher (KVS_erase Global);
      kvs_user_seal_key Global kvs_user_key_B_addr
    ] ∧
  Forall is_z (cmpt_code B_cmpt) ∧ (* only instructions *)
  Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt) ∧
  (cmpt_static_sealed B_cmpt) = [WInt kvs_user_key_B] ∧
  (cmpt_exp_tbl_entries B_cmpt) = [WInt (encode_entry_point 0 offset_adv_f)] ∧

  (* initial stack *)
  Forall is_z (stack_content switcher_cmpt)
.

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

Lemma mk_initial_cmpt_kvs_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt
    ##ₘ mk_initial_cmpt kvs_cmpt.
Proof.
  pose proof cmpts_disjoints as (_ & Hmain_kvs & _).
  pose proof switcher_cmpt_disjoints as (_ & Hswitcker_kvs & _).
  pose proof assert_cmpt_disjoints as ( _ & Hassert_kvs & _).
  do 2 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Lemma mk_initial_cmpt_B_disjoint `{Layout: @memory_layout MP} (m : Mem) :
  mk_initial_switcher switcher_cmpt ∪ mk_initial_assert assert_cmpt ∪ mk_initial_cmpt main_cmpt ∪ mk_initial_cmpt kvs_cmpt
    ##ₘ mk_initial_cmpt B_cmpt.
Proof.
  pose proof cmpts_disjoints as (Hmain_B & _ & Hmain_kvs).
  pose proof switcher_cmpt_disjoints as (_ & _ & HswitcherB).
  pose proof assert_cmpt_disjoints as ( _ & _ & HassertB).
  do 3 rewrite map_disjoint_union_l.
  repeat split.
  - symmetry; apply disjoint_switcher_cmpts_mkinitial; done.
  - symmetry; apply disjoint_assert_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
  - apply disjoint_cmpts_mkinitial; done.
Qed.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {cname : CmptNameG}.
  Context {B : CmptName}.
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
  Context { HCNames : CNames = (list_to_set [B]) }.

  Context {Layout: memory_layout}.

  Local Notation kvs_user_key_K_a := (0 ^+ kvs_user_key_K)%a.
  Local Notation kvs_user_key_B_a := (0 ^+ kvs_user_key_B)%a.

  Context {kvs_alloc_preg: gen_heapGpreS user_key_t kvs_user_map Σ}.
  Context {kvs_physical_user_preg : ghost_varG Σ kvs_physical_map }.
  Context {kvs_logical_user_preg : ghost_mapG Σ user_key_t (option Word) }.

  Definition flagN : namespace := nroot .@ "kvs" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "kvs" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "kvs" .@ "assert_flag".
  Definition kvsN : namespace := nroot .@ "kvs" .@ "code".

  Local Notation ot_switcher := (ot_switcher switcher_cmpt).
  Lemma kvs_adequacy'
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
                    & main_imports & main_code & main_data & main_static_sealed & main_exp_tbl
                    & kvs_imports & kvs_code & kvs_data & kvs_static_sealed & kvs_exp_tbl
                    & B_imports & B_code & B_data & B_static_sealed & B_exp_tbl
                    & Hstack
                   ).
    pose proof cmpts_disjoints as (Hmain_B & Hmain_kvs & Hkvs_B).

    (* 1 - We give a name to the exported entry points for which we want
       to know the number of arguments. *)
    set (B_f := cmpt_export B_cmpt (cmpt_exp_tbl_entries_start B_cmpt)).
    set (kvs_addOrUpdate :=
           cmpt_export kvs_cmpt (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a).
    set (kvs_read := cmpt_export kvs_cmpt (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a).
    set (kvs_erase := cmpt_export kvs_cmpt (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a).

    (* 2 - We use the Iris adequacy theorem, which initialises the program
       logic resources: registers, memory, entry points and NA invariants. *)
    eapply (cerise_flag_adequacy Σ ot_switcher
              [(B_f, 0); (kvs_addOrUpdate, kvs_addOrUpdate_nargs);
               (kvs_read, kvs_read_nargs); (kvs_erase, kvs_erase_nargs)]
              flagN (flag_assert assert_cmpt));
      [| by repeat constructor | | exact Hstep].
    { pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl /kvs_export_table_entries /= in H1.
      assert (B_f ≠ kvs_addOrUpdate) by apply not_eq_sym, cmpt_export_disjoint, Hkvs_B.
      assert (B_f ≠ kvs_read) by apply not_eq_sym, cmpt_export_disjoint, Hkvs_B.
      assert (B_f ≠ kvs_erase) by apply not_eq_sym, cmpt_export_disjoint, Hkvs_B.
      assert (kvs_addOrUpdate ≠ kvs_read).
      { rewrite /kvs_addOrUpdate /kvs_read /cmpt_export
          /kvs_addOrUpdate_exp_tbl_off /kvs_read_exp_tbl_off.
        intros Heq; simplify_eq; solve_addr+Heq H1 Hc Hc'. }
      assert (kvs_addOrUpdate ≠ kvs_erase).
      { rewrite /kvs_addOrUpdate /kvs_erase /cmpt_export
          /kvs_addOrUpdate_exp_tbl_off /kvs_erase_exp_tbl_off.
        intros Heq; simplify_eq; solve_addr+Heq H1 Hc Hc'. }
      assert (kvs_read ≠ kvs_erase).
      { rewrite /kvs_read /kvs_erase /cmpt_export
          /kvs_read_exp_tbl_off /kvs_erase_exp_tbl_off.
        intros Heq; simplify_eq; solve_addr+Heq H1 Hc Hc'. }
      cbn; repeat (apply NoDup_cons; split); try apply NoDup_nil; set_solver.
    }
    iIntros (ceriseg) "Hreg Hsreg Hmem Hna
                       ([#Hentry_Bf #Hentry_Bf'] & [#Hentry_kvs_addOrUpdate #Hentry_kvs_addOrUpdate']
                       & [#Hentry_kvs_read #Hentry_kvs_read'] & [#Hentry_kvs_erase #Hentry_kvs_erase'] & _)".
    (* Use the non-atomic invariant pool of [ceriseg] *)
    clear na_invg.

    (* 3 - We initialise the seal store, the call stack and the world
       interpretation of B *)
    iMod (initialise_world [B] {[ ot_switcher ; ot_kvs ]})
      as (seal_storeg relg stsg cstackg) "(Hseal_store & Hcstk_full & Hcstk_frag & [Hworld_B _])";
      [done | apply NoDup_singleton |].
    rewrite big_sepS_insert; last (pose proof ot_kvs_disjoint as Hdis; set_solver+Hdis).
    rewrite big_sepS_singleton.
    iDestruct "Hseal_store" as "[Hseal_store_switcher Hseal_store_kvs]".
    set (W0 := (∅, (∅, ∅), ∅) : WORLD).

    assert kvs_namespaces as kvs_namespacesg.
    {
      refine (Build_kvs_namespaces
                (kvsN .@ "Nkvs")
                (kvsN .@ "Nkvs_otype")
                (kvsN .@ "Nkvs_exp_tbl")
                _).
      split;try solve_ndisj.
    }
    assert kvsLayoutWf as kvsLayoutWfg.
    { refine (mkKvsLayoutWf _ _ _ _ _ _); cbn.
      - apply ot_kvs_size.
      - pose proof (cmpt_import_size kvs_cmpt) as H.
        by rewrite kvs_imports in H.
      - pose proof (cmpt_code_size kvs_cmpt) as H.
        by rewrite kvs_code in H.
      - pose proof (cmpt_data_size kvs_cmpt) as H.
        by rewrite kvs_data in H.
      - pose proof ( cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
        pose proof ( cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
        pose proof ( cmpt_exp_tbl_entries_size kvs_cmpt) as H3.
        rewrite kvs_exp_tbl /kvs_export_table_entries in H3.
        rewrite /length_kvs_exports_tbl /kvs_nb_exports.
        cbn in *.
        solve_addr+H1 H2 H3.
    }

    (* 4 - Get initial sregister mtdc *)
    iDestruct (big_sepM_lookup with "Hsreg") as "Hmtdc"; first exact Hsreg.

    (* 5 - Separate all compartments *)
    rewrite Hm /mk_initial_memory.
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_B]".
    { eapply mk_initial_cmpt_B_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_kvs]".
    { eapply mk_initial_cmpt_kvs_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hmem Hcmpt_main]".
    { eapply mk_initial_cmpt_main_disjoint; eauto. }
    iDestruct (big_sepM_union with "Hmem") as "[Hcmpt_switcher Hcmpt_assert]".
    { pose proof assert_switcher_disjoints; symmetry; eapply disjoint_assert_switcher_mkinitial ; eauto. }

    (* 5.1 KVS compartment: initialise the KVS resources *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_kvs")
      as "(Hkvs_imports & Hkvs_code & Hkvs_data & _ & Hkvs_etbl_pcc & Hkvs_etbl_cgp & Hkvs_etbl_entries)".
    iEval (rewrite cmpt_code_codefrag) in "Hkvs_code".
    rewrite kvs_imports kvs_code.
    rewrite /kvs_inv kvs_data /kvs_data.

    iMod (user_kvs_init {[ kvs_user_key_K ; kvs_user_key_B ]}
           with "[$Hkvs_imports $Hkvs_code $Hkvs_data]")
      as (γpkvs kvs_logical_heapg γf) "(#Hkvs & #Hkvs_logical & Hlukvs)".
    pose kvsphysicalg := Build_KvsPhysicalG Σ kvs_physical_user_preg γpkvs.
    pose kvslogicalg := Build_KvsLogicalG Σ kvs_logical_heapg.
    pose kvsuserg := Build_KvsUserG Σ kvs_logical_user_preg γf.
    pose kvsg := KvsG Σ kvsphysicalg kvslogicalg kvsuserg.

    assert ( kvs_user_key_K ≠ kvs_user_key_B ) as Huser_keys_disjoint.
    { pose proof kvs_user_key_disjoints; solve_addr. }
    iDestruct (big_sepS_delete _ _ kvs_user_key_K with "Hlukvs")
      as "[ [Hkvs_logical_user_K HK_lukvs_frag] Hlukvs]"; first by set_solver+.
    iDestruct (big_sepS_delete _ _ kvs_user_key_B with "Hlukvs")
      as "[ [Hkvs_logical_user_B HB_lukvs_frag] _]"; first by set_solver+Huser_keys_disjoint.

    pose proof (
        @kvs_main_spec Σ ceriseg seal_storeg _ _ _ _ _ _ _
          kvsg _ _ _ B
      ) as Spec.

    (* 5.2 Assert compartment *)
    iMod ( initialise_assert_compartment (Σ := Σ) _ assertN flagN with "Hcmpt_assert" )
      as "[#Hassert_flag #Hassert]".

    (* 5.3 Switcher compartment *)
    iMod ( initialise_switcher_compartment (Σ := Σ) _ switcherN with "Hcmpt_switcher Hseal_store_switcher Hcstk_full Hmtdc" )
      as "(#Hsealed_pred_ot_switcher & #Hswitcher & Hstack)".

    (* 5.4 CMPT B *)
    iMod (initialise_adversary_compartment (Σ := Σ) _ B with "Hcmpt_B")
      as "(HB_imports & HB_code & HB_data & HB_static_sealed & #HB_etbl_pcc & #HB_etbl_cgp & #HB_etbl_entries)".
    iEval (rewrite B_static_sealed) in "HB_static_sealed".
    iDestruct ( region_pointsto_single with "HB_static_sealed" ) as "(%&Ha_user_key_B&%)"; simplify_eq.
    {
      pose proof (cmpt_static_sealed_size B_cmpt) as H1.
      rewrite B_static_sealed in H1; solve_addr+H1.
    }
    set ( user_key_addr_B := cmpt_b_static_sealed B_cmpt ).

    (* 5.5 CMPT MAIN *)
    iMod (initialise_compartment (Σ := Σ) with "Hcmpt_main")
      as "(Hmain_imports & Hmain_code & Hmain_data & Hmain_static_sealed & _ & _ & _)".
    iEval (rewrite cmpt_code_codefrag) in "Hmain_code".
    rewrite main_imports main_code main_data main_static_sealed.

    (* 5.6 Export table of the KVS *)
    rewrite kvs_exp_tbl.
    iEval (rewrite /region_pointsto /kvs_export_table_entries) in "Hkvs_etbl_entries".
    rewrite (finz_seq_between_cons (cmpt_exp_tbl_entries_start kvs_cmpt)).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite (finz_seq_between_cons ((cmpt_exp_tbl_entries_start kvs_cmpt) ^+ _)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite (finz_seq_between_cons (((cmpt_exp_tbl_entries_start kvs_cmpt) ^+ _) ^+ _)%a).
    2: {
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl in H1; solve_addr+H1.
    }
    rewrite big_sepL2_cons.
    rewrite big_sepL2_cons.
    rewrite big_sepL2_cons.
    iDestruct "Hkvs_etbl_entries"
      as "(Hkvs_etbl_entries_addOrUpdate & Hkvs_etbl_entries_read
          & Hkvs_etbl_entries_erase & _)".

    iMod (seal_store_update_alloc _ ( kvs_otype_propC ) with "Hseal_store_kvs") as "#Hsealed_pred_ot_kvs".

    iMod (inv_alloc (switcher_preamble.export_table_PCCN Nkvs_exp_tbl) ⊤ _
           with "Hkvs_etbl_pcc")%I as "#Hkvs_etbl_pcc".
    iMod (inv_alloc (switcher_preamble.export_table_CGPN Nkvs_exp_tbl) ⊤ _
           with "Hkvs_etbl_cgp")%I as "#Hkvs_etbl_cgp".
    iMod (inv_alloc (switcher_preamble.export_table_entryN Nkvs_exp_tbl kvs_addOrUpdate_exp_tbl_addr) ⊤ _
           with "Hkvs_etbl_entries_addOrUpdate")%I as "#Hkvs_etbl_entries_addOrUpdate".
    iMod (inv_alloc (switcher_preamble.export_table_entryN Nkvs_exp_tbl kvs_read_exp_tbl_addr) ⊤ _
           with "Hkvs_etbl_entries_read")%I as "#Hkvs_etbl_entries_read".
    iMod (inv_alloc (switcher_preamble.export_table_entryN Nkvs_exp_tbl kvs_erase_exp_tbl_addr) ⊤ _
           with "Hkvs_etbl_entries_erase")%I as "#Hkvs_etbl_entries_erase".

    replace (cmpt_exp_tbl_entries_start kvs_cmpt ^+ 1)%a with kvs_read_exp_tbl_addr; cycle 1.
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H3; rewrite kvs_exp_tbl /kvs_export_table_entries in H3.
      rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off.
      cbn in *.
      solve_addr+H1 H2 H3.
    }
    replace (kvs_read_exp_tbl_addr ^+ 1)%a with kvs_erase_exp_tbl_addr; cycle 1.
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H3; rewrite kvs_exp_tbl /kvs_export_table_entries in H3.
      rewrite /kvs_read_exp_tbl_addr /kvs_read_exp_tbl_off.
      rewrite /kvs_erase_exp_tbl_addr /kvs_erase_exp_tbl_off.
      cbn in *.
      solve_addr+H1 H2 H3.
    }
    replace (cmpt_exp_tbl_entries_start kvs_cmpt) with kvs_addOrUpdate_exp_tbl_addr; cycle 1.
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H2.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H3; rewrite kvs_exp_tbl /kvs_export_table_entries in H3.
      rewrite /kvs_addOrUpdate_exp_tbl_addr /kvs_addOrUpdate_exp_tbl_off.
      cbn in *.
      solve_addr+H1 H2 H3.
    }

    (* 6 - Seal the exported entries of the KVS with [ot_switcher] in the
       world of B *)
    subst B_f kvs_addOrUpdate kvs_read kvs_erase; rewrite /cmpt_export; cbn.
    set (B_f := (SCap true RO Global _ _ (cmpt_exp_tbl_entries_start B_cmpt))).
    set (kvs_addOrUpdate := (SCap true RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a)).
    set (kvs_addOrUpdate' := (SCap true RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a)).
    set (kvs_read := (SCap true RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a)).
    set (kvs_read' := (SCap true RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a)).
    set (kvs_erase := (SCap true RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a)).
    set (kvs_erase' := (SCap true RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a)).

    set ( adversary_imports :=
            ({[ WSealable kvs_addOrUpdate ; WSealable kvs_addOrUpdate']}
              ∪
            {[ WSealable kvs_read ; WSealable kvs_read']}
              ∪
            {[ WSealable kvs_erase ; WSealable kvs_erase']} : gset Word)
        ).

    set (W1 := <o[ ot_switcher := adversary_imports]o> W0).

    iAssert (ot_switcher_prop W1 B (WSealable kvs_addOrUpdate)) as "#ot_switcher_kvs_addOrUpdate".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H2.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_addOrUpdate_entry_point_spec; try iFrame "#"; eauto.
    }

    iAssert (ot_switcher_prop W1 B (WSealable kvs_read)) as "#ot_switcher_kvs_read".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H2.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_read_entry_point_spec; try iFrame "#"; eauto.
    }

    iAssert (ot_switcher_prop W1 B (WSealable kvs_erase)) as "#ot_switcher_kvs_erase".
    {
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H0.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H2.
      replace (cmpt_exp_tbl_cgp kvs_cmpt)
        with (cmpt_exp_tbl_pcc kvs_cmpt ^+ 1)%a by solve_addr+H0.
      iApply kvs_erase_entry_point_spec; try iFrame "#"; eauto.
    }

    assert (ot_switcher ∉ dom (seal_std W0)) as Hot_notin_W0.
    { by subst W0. }
    iMod
      (world_interp_salloc W0 B ot_switcher_propC ot_switcher adversary_imports
        with "[$Hsealed_pred_ot_switcher] [ ] [ ] [$Hworld_B]")
      as "(Hworld_B & Hseal_kvs_f)"; first done.
    { iIntros (w); iApply mono_priv_ot_switcher. }
    { rewrite {2}/adversary_imports.
      rewrite 2!normalise_sealed_words_union.
      rewrite !normalise_sealed_words_borrow.
      iEval (rewrite union_comm_L); iApply big_sepS_insert_2; first (iFrame "ot_switcher_kvs_erase").
      iEval (rewrite union_comm_L); iApply big_sepS_insert_2; first (iFrame "ot_switcher_kvs_read").
      rewrite big_sepS_singleton; iFrame "ot_switcher_kvs_addOrUpdate".
    }
    subst W1; set (W1 := <o[ ot_switcher := adversary_imports]o> W0).

    iAssert ( interp W1 B (WSealed ot_switcher kvs_addOrUpdate)) as "#Hinterp_kvs_addOrUpdate".
    { iEval (rewrite fixpoint_interp1_eq); iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+. }
    iAssert ( interp W1 B (WSealed ot_switcher kvs_read)) as "#Hinterp_kvs_read".
    { iEval (rewrite fixpoint_interp1_eq); iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+. }
    iAssert ( interp W1 B (WSealed ot_switcher kvs_erase)) as "#Hinterp_kvs_erase".
    { iEval (rewrite fixpoint_interp1_eq); iApply (sts_seals_std_weaken with "Hseal_kvs_f") ; last set_solver+. }

    (* 7 - Seal the user key of B with [ot_kvs] in the world of B *)
    set ( kvs_user_key_B_sb := (kvs_user_seal_key_scap Global user_key_addr_B)).
    set ( kvs_user_key_B_sb' := borrow_sb kvs_user_key_B_sb).
    set ( adversary_kvs_keys := ( {[ WSealable kvs_user_key_B_sb ; WSealable kvs_user_key_B_sb']} : gset Word)).
    set (W1' := <o[ ot_kvs := adversary_kvs_keys ]o> W1).

    iAssert (kvs_otype_prop W1' B (WSealable kvs_user_key_B_sb))
      with "[$Hkvs_logical_user_B $Ha_user_key_B HB_lukvs_frag]" as "ot_kvs_user_key_B".
    {
      repeat iSplit.
      - iPureIntro; auto.
      - iPureIntro.
        subst user_key_addr_B.
        pose proof (cmpt_static_sealed_size B_cmpt) as H.
        rewrite B_static_sealed in H.
        solve_addr+H.
      - iApply (big_sepS_impl with "HB_lukvs_frag").
        iModIntro; iIntros (mk Hmk) "$".
    }

    assert (ot_kvs ∉ dom (seal_std W1)) as Hot_notin_W1.
    { pose proof ot_kvs_disjoint as H.
      subst W0 W1; rewrite dom_insert_L dom_empty_L; set_solver+H.
    }
    iMod
      (world_interp_salloc W1 B kvs_otype_propC ot_kvs adversary_kvs_keys
        with "[$Hsealed_pred_ot_kvs] [ ] [ ot_kvs_user_key_B ] [$Hworld_B]")
      as "(Hworld_B & Hseal_kvs_ku)"; first done.
    { iIntros (w); iApply mono_priv_ot_kvs. }
    { rewrite normalise_sealed_words_borrow.
      rewrite big_sepS_singleton; iFrame "ot_kvs_user_key_B".
    }
    subst W1' ; set (W1' := <o[ ot_kvs := adversary_kvs_keys ]o> W1).

    iAssert ( interp W1' B (WSealed ot_kvs kvs_user_key_B_sb)) as "#Hinterp_kvs_user_key_B".
    { iEval (rewrite fixpoint_interp1_eq); iApply (sts_seals_std_weaken with "Hseal_kvs_ku") ; last set_solver+. }

    (* 8 - Initialise the world of B: its compartment becomes permanent,
       and the stack temporary. *)
    pose proof switcher_cmpt_disjoints as (_ & _ & Hsw_B).
    iMod (initialise_adversary_world W1' switcher_cmpt _ B
           with "Hsealed_pred_ot_switcher HB_imports HB_code HB_data Hstack [] [] Hworld_B")
      as "(Hworld_B & #Hinterp_pcc_B & #Hinterp_cgp_B & #Hinterp_stack_B & #HB_exports)";
      [auto..| | |].
    { (* The exported entry B.f satisfies the sealing predicate of the switcher *)
      iApply (adversary_exports_prop _ _ _ _ [(0, offset_adv_f)]
               with "Hswitcher HB_etbl_pcc HB_etbl_cgp HB_etbl_entries");
        [by rewrite B_exp_tbl | by repeat constructor |
         by apply Forall_singleton, offset_adv_f_valid |].
      rewrite /= finz_add_0_default; iFrame "Hentry_Bf Hentry_Bf'".
    }
    { rewrite B_imports.
      iIntros "_".
      set ( Winter := (std_update_compartment W1' B_cmpt) ).
      assert (related_sts_priv_world W1' Winter) as Hrelated_W1'_Winter.
      {
        apply related_sts_pub_priv_world.
        subst Winter.
        eapply std_update_compartment_pub; eauto ; apply Forall_true; intros; done.
      }
      assert (related_sts_priv_world W1 Winter) as Hrelated_W1_Winter.
      {
        eapply related_sts_priv_trans_world; eauto.
        apply related_sts_pub_priv_world.
        subst W1'.
        apply related_sts_pub_world_update_ot.
      }
      (* Switcher cross-compartment *)
      iApply big_sepL_cons; iSplitL.
      { iSplit; [| iIntros (???) "!> _" ] ; iApply interp_switcher_call ; done. }
      (* KVS.addOrUpdate *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply (interp_monotone_sd W1 Winter); auto.
        * iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto.
      }
      (* KVS.read *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply (interp_monotone_sd W1 Winter); auto.
        * iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto.
      }
      (* KVS.erase *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply (interp_monotone_sd W1 Winter); auto.
        * iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto.
      }
      (* KVS sealed user key *)
      iApply big_sepL_cons; iSplitL.
      { iSplit.
        * iApply (interp_monotone_sd W1' Winter); auto.
        * iIntros (??) "!> % ?"; iApply interp_monotone_sd; auto.
      }
      done.
    }

    (* 9 - The exported entry point of B is safe to share *)
    iAssert (interp (adv_world W1' switcher_cmpt B_cmpt) B (WSealed ot_switcher B_f))
      as "#Hinterp_B_f".
    { iApply (adversary_export_interp _ _ _ 0 with "HB_exports").
      - solve_addr.
      - rewrite B_exp_tbl /=; lia.
    }

    iDestruct (big_sepS_elem_of _ _ 1%Z with "HK_lukvs_frag") as "HK_lukvs_1".
    { eapply is_uint16_in_kvs_all_map_keys; split; rewrite /UINT16_MIN /UINT16_MAX; lia. }

    (* 10 - Extract registers *)
    iDestruct (initial_registers_split with "Hreg")
      as (rmap) "(HPC & Hcgp & Hcsp & Hrmap & %Hrmap_dom & %Hrmap_zero)"; first exact Hreg.
    pose proof (main_spec_size_obligations _ _ _ _ main_imports main_code main_data)
      as (Hmain_bounds & Hmain_data_size & Hmain_imports_size).

    replace (cmpt_exp_tbl_cgp kvs_cmpt) with (b_kvs_exp_tbl ^+ 1)%a
                                             by (pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as H; cbn; solve_addr+H).

    (* 11 - We can apply the specification! *)
    iPoseProof (Spec _ _ _ _ _ _ _ _ _ _
                  _ _ _ _ _ _
                  [] [] [] assertN switcherN
                 with "[ $Hassert $Hswitcher $Hkvs $Hkvs_logical_user_K
                        $Hkvs_etbl_pcc $Hkvs_etbl_cgp $Hkvs_etbl_entries_addOrUpdate $Hkvs_etbl_entries_read
                        $Hna $HPC $Hcgp $Hcsp $Hrmap
                        $Hmain_imports $Hmain_code $Hmain_data $Hmain_static_sealed
                        $HK_lukvs_1
                        $Hworld_B $Hcstk_frag
                        $Hinterp_B_f $Hentry_Bf $Hinterp_stack_B
                        ]") as "Hspec"; eauto.
    { solve_ndisj. }
    { pose proof (cmpt_static_sealed_size main_cmpt) as Hmain_static_sealed.
      by rewrite main_static_sealed in Hmain_static_sealed.
    }
    { done. }

    iModIntro; iFrame "Hassert_flag".
    iApply (wp_mono with "Hspec"); auto.
  Qed.

End Adequacy.

Inductive CmptNames_kvs := | B .
Local Instance CmptNames_kvs_eq_dec : EqDecision CmptNames_kvs.
Proof. intros C C'; destruct C,C'; solve_decision. Qed.
Local Instance CmptNames_kvs_finite : finite.Finite CmptNames_kvs.
Proof.
  refine {| finite.enum := [B] |}.
  + apply NoDup_singleton.
  + intros []; left.
Defined.

Local Program Instance CmptNames_kvs_CmptNameG : CmptNameG :=
  {| CmptName := CmptNames_kvs; |}.

(** END-TO-END THEOREM *)
Theorem kvs_adequacy `{Layout: memory_layout}
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
  set ( cnames := CmptNames_kvs_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type OType Word ; relPreΣ
              ; savedPredΣ (WorldT * CmptName * Word)
              ; gen_heapΣ user_key_t kvs_user_map
              ; ghost_mapΣ user_key_t (option Word)
              ; ghost_varΣ kvs_physical_map
      ]).
  eapply (@kvs_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
