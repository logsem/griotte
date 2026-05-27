From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import
  kvs kvs_main kvs_preamble kvs_main_spec kvs_spec_addOrUpdate_safe kvs_spec_read_safe.
From cap_machine Require Import switcher assert_spec logrel.
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

    (* kvs compartment *)
    kvs_cmpt : cmpt ;

    (* adv compartments B *)
    B_cmpt : cmpt ;
    offset_adv_f : nat;

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

    ot_kvs : OType;
    ot_kvs_size : (ot_kvs < ot_kvs ^+ 1)%ot;
    ot_kvs_disjoint : ot_kvs ≠ ot_switcher ;
  }.

Definition mk_initial_memory `{memory_layout} (mem: Mem) :=
  mk_initial_switcher switcher_cmpt ∪
    mk_initial_assert assert_cmpt ∪
    mk_initial_cmpt main_cmpt ∪
    mk_initial_cmpt kvs_cmpt ∪
    mk_initial_cmpt B_cmpt.

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

Local Instance memory_layout_kvs_layout `{memory_layout} : kvsLayout.
Proof.
  refine (@mkCmptKvs MP ot_kvs ot_kvs_size
            (cmpt_b_pcc kvs_cmpt) (cmpt_a_code kvs_cmpt) (cmpt_e_pcc kvs_cmpt) _ _
            (cmpt_b_cgp kvs_cmpt) (cmpt_e_cgp kvs_cmpt) _
            (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt) _).
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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
  let B_f :=
    SCap RO Global
      (cmpt_exp_tbl_pcc B_cmpt)
      (cmpt_exp_tbl_entries_end B_cmpt)
      (cmpt_exp_tbl_entries_start B_cmpt)
  in

  mem = mk_initial_memory mem ∧
  (* instantiating main *)
  (cmpt_imports main_cmpt) =
  (kvs_main_imports
    b_switcher e_switcher
    a_switcher_call ot_switcher
    (b_assert assert_cmpt) (e_assert assert_cmpt)
    B_f) ∧
  (cmpt_code main_cmpt) = kvs_main_code ∧
  (cmpt_data main_cmpt) = kvs_main_data ∧
  (cmpt_exp_tbl_entries main_cmpt) = [] ∧

  (* instantiating kvs *)
  (cmpt_imports kvs_cmpt) = kvs_imports b_switcher e_switcher a_switcher_call ot_switcher ∧
  (cmpt_code kvs_cmpt) = kvs_service_instrs ∧
  (cmpt_data kvs_cmpt) = kvs_data ∧
  (cmpt_exp_tbl_entries kvs_cmpt) = kvs_export_table_entries ∧

  (* instantiating B *)
  (cmpt_imports B_cmpt) = [
      switcher_entry;
      WSealed ot_switcher (KVS_addOrUpdate Global);
      WSealed ot_switcher (KVS_read Global)
    ] ∧
  Forall is_z (cmpt_code B_cmpt) ∧ (* only instructions *)
  Forall (is_initial_data_word B_cmpt) (cmpt_data B_cmpt) ∧
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
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context { HCNames : CNames = (list_to_set [B]) }.

  Context {kvs_preg: gen_heapGpreS nat kvs_entry Σ}.
  Context {kvs_alloc_preg: gen_heapGpreS Z (gset Z) Σ}.
  Context {KVS_users: kvs_users}.

  Definition flagN : namespace := nroot .@ "kvs" .@ "fail_flag".
  Definition switcherN : namespace := nroot .@ "kvs" .@ "switcher_flag".
  Definition assertN : namespace := nroot .@ "kvs" .@ "assert_flag".
  Definition kvsN : namespace := nroot .@ "kvs" .@ "code".

  Local Instance choice_kvs_namespaces : kvs_namespaces.
  Proof.
    refine (Build_kvs_namespaces
              (kvsN .@ "Nkvs")
              (kvsN .@ "Nkvs_otype")
              (kvsN .@ "Nkvs_exp_tbl")
              _
           ).
    repeat (split;try solve_ndisj).
  Qed.

  Lemma kvs_adequacy' `{Layout: @memory_layout MP}
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
                    & kvs_imports & kvs_code & kvs_data & kvs_exp_tbl
                    & B_imports & B_code & B_data & B_exp_tbl
                    & Hstack
                   ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (seal_store_init ({[ ot_switcher ; ot_kvs ]} : gset _)) as (seal_storeg) "Hseal_store".
    rewrite big_sepS_insert; last (pose proof ot_kvs_disjoint as Hdis; set_solver+Hdis).
    rewrite big_sepS_singleton.
    iDestruct "Hseal_store" as "[Hseal_store_switcher Hseal_store_kvs]".

    set (
        B_f :=
       (WCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
         (cmpt_exp_tbl_entries_start B_cmpt))
      ).
    set (kvs_addOrUpdate :=
          (WCap RO Global
             (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)
             (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a)
        ).
    set (kvs_read :=
          (WCap RO Global
             (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)
             (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a)
        ).
    set (kvs_erase :=
          (WCap RO Global
             (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt)
             (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a)
        ).

    assert (B_f ≠ kvs_addOrUpdate) as Hneq_Bf_kvs_addOrUpdate.
    { intro H ; subst kvs_addOrUpdate B_f ; simplify_eq.
      pose proof cmpts_disjoints as Hdisjoint.
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
      assert (
          cmpt_exp_tbl_region kvs_cmpt  ## cmpt_exp_tbl_region B_cmpt
        ) as Hdis by set_solver+Hdisjoint.
      rewrite /cmpt_exp_tbl_region in Hdis.
      apply stdpp_extra.list_to_set_disj in Hdis.
      rewrite H H0 in Hdis.
      assert (
          list_to_set
            (finz.seq_between (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt))
            ≠ (∅ : gset Addr)
        ) as Hemp; [|set_solver+Hdis Hemp].
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as Hc''.
      rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
      set_solver+.
    }
    assert (B_f ≠ kvs_read) as Hneq_Bf_kvs_read.
    { intro H ; subst kvs_addOrUpdate B_f ; simplify_eq.
      pose proof cmpts_disjoints as Hdisjoint.
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
      assert (
          cmpt_exp_tbl_region kvs_cmpt  ## cmpt_exp_tbl_region B_cmpt
        ) as Hdis by set_solver+Hdisjoint.
      rewrite /cmpt_exp_tbl_region in Hdis.
      apply stdpp_extra.list_to_set_disj in Hdis.
      rewrite H H0 in Hdis.
      assert (
          list_to_set
            (finz.seq_between (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt))
            ≠ (∅ : gset Addr)
        ) as Hemp; [|set_solver+Hdis Hemp].
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as Hc''.
      rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
      set_solver+.
    }
    assert (B_f ≠ kvs_erase) as Hneq_Bf_kvs_erase.
    { intro H ; subst kvs_addOrUpdate B_f ; simplify_eq.
      pose proof cmpts_disjoints as Hdisjoint.
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
      assert (
          cmpt_exp_tbl_region kvs_cmpt  ## cmpt_exp_tbl_region B_cmpt
        ) as Hdis by set_solver+Hdisjoint.
      rewrite /cmpt_exp_tbl_region in Hdis.
      apply stdpp_extra.list_to_set_disj in Hdis.
      rewrite H H0 in Hdis.
      assert (
          list_to_set
            (finz.seq_between (cmpt_exp_tbl_pcc kvs_cmpt) (cmpt_exp_tbl_entries_end kvs_cmpt))
            ≠ (∅ : gset Addr)
        ) as Hemp; [|set_solver+Hdis Hemp].
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as Hc''.
      rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
      set_solver+.
    }
    assert (kvs_addOrUpdate ≠ kvs_read) as Hneq_kvs_addOrUpdate_kvs_read.
    { subst kvs_addOrUpdate kvs_read
      ; rewrite /kvs_addOrUpdate_exp_tbl_off /kvs_read_exp_tbl_off
      ; intro
      ; simplify_eq.
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl /kvs_export_table_entries /= in H1.
      solve_addr+H H1 Hc Hc'.
    }
    assert (kvs_addOrUpdate ≠ kvs_erase) as Hneq_kvs_addOrUpdate_kvs_erase.
    { subst kvs_addOrUpdate kvs_erase
      ; rewrite /kvs_addOrUpdate_exp_tbl_off /kvs_erase_exp_tbl_off
      ; intro
      ; simplify_eq.
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl /kvs_export_table_entries /= in H1.
      solve_addr+H H1 Hc Hc'.
    }
    assert (kvs_read ≠ kvs_erase) as Hneq_kvs_read_kvs_erase.
    { subst kvs_read kvs_erase
      ; rewrite /kvs_read_exp_tbl_off /kvs_erase_exp_tbl_off
      ; intro
      ; simplify_eq.
      pose proof (cmpt_exp_tbl_pcc_size kvs_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size kvs_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size kvs_cmpt) as H1.
      rewrite kvs_exp_tbl /kvs_export_table_entries /= in H1.
      solve_addr+H H1 Hc Hc'.
    }


    iMod (
       entry_init (
           {[
               (seal_capability B_f ot_switcher) := 0;
               (borrow (seal_capability B_f ot_switcher)) := 0;
               (seal_capability kvs_addOrUpdate ot_switcher) := kvs_addOrUpdate_nargs;
               (borrow (seal_capability kvs_addOrUpdate ot_switcher)) := kvs_addOrUpdate_nargs;
               (seal_capability kvs_read ot_switcher) := kvs_read_nargs;
               (borrow (seal_capability kvs_read ot_switcher)) := kvs_read_nargs;
               (seal_capability kvs_erase ot_switcher) := kvs_erase_nargs;
               (borrow (seal_capability kvs_erase ot_switcher)) := kvs_erase_nargs
           ]}

         )
      ) as (entry_g) "Hentries".
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Bf Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Bf' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_addOrUpdate Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_addOrUpdate' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_read Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_read' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_erase Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_kvs_erase' Hentries]".
    rewrite delete_id
    ; last (repeat ( rewrite lookup_insert_ne ; [| entry_point_inj] ) ; done ).
    subst B_f kvs_addOrUpdate kvs_read kvs_erase; cbn.
    set (B_f := (SCap RO Global _ _ (cmpt_exp_tbl_entries_start B_cmpt))).
    set (B_f' := (SCap RO Local _ _ (cmpt_exp_tbl_entries_start B_cmpt))).
    set (kvs_addOrUpdate := (SCap RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a)).
    set (kvs_addOrUpdate' := (SCap RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_addOrUpdate_exp_tbl_off)%a)).
    set (kvs_read := (SCap RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a)).
    set (kvs_read' := (SCap RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_read_exp_tbl_off)%a)).
    set (kvs_erase := (SCap RO Global _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a)).
    set (kvs_erase' := (SCap RO Local _ _ (cmpt_exp_tbl_pcc kvs_cmpt ^+ kvs_erase_exp_tbl_off)%a)).
    clear Hneq_Bf_kvs_addOrUpdate Hneq_Bf_kvs_read Hneq_Bf_kvs_erase
      Hneq_kvs_addOrUpdate_kvs_read Hneq_kvs_addOrUpdate_kvs_erase Hneq_kvs_read_kvs_erase.

    unshelve iMod (gen_sts_init 0) as (stsg) "Hsts"; eauto. (*XX*)
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
    iMod (heap_init) as (heapg) "HRELS".

    iDestruct (big_sepS_elements with "Hsts") as "Hsts_B".
    iDestruct (big_sepS_elements with "HRELS") as "HRELS_B".
    rewrite HCNames.
    pose proof (NoDup_singleton B) as HCNoDup.
    setoid_rewrite elements_list_to_set; auto.
    rewrite !big_sepL_singleton.

    iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".

    set ( kvs_alloc_init := ({[ 0%Z := ∅ ; 1%Z := ∅ ]} : kvs_alloc)).
    iMod (gen_heap_init (∅:kvs_map)) as (kvs_heapg) "(Hkvs_auth & _ & _)".
    iMod (gen_heap_init (kvs_alloc_init:kvs_alloc)) as (kvs_alloc_heapg) "(Hkvs_alloc_auth & Hkvs_alloc_frag & _)".
    subst kvs_alloc_init.
    rewrite big_sepM_insert; last by simplify_map_eq.
    rewrite big_sepM_insert; last by simplify_map_eq.
    iDestruct "Hkvs_alloc_frag" as "(Halloc_0 & Halloc_1 & _)".

    pose ceriseg := CeriseG Σ Hinv mem_heapg reg_heapg sreg_heapg entry_g.
    pose kvsg := KvsG Σ kvs_heapg kvs_alloc_heapg.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose switcher_layout_g := (@switcher_layout MP Layout).

    pose proof (
        @kvs_main_spec Σ ceriseg seal_storeg _ _ _ logrel_na_invs _ _  switcher_layout_g
          kvsg _ _ _ B
      ) as Spec.

    Admitted.

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

Local Instance choice_kvs_users_seals : kvs_users.
Proof.
  refine (Build_kvs_users CmptNames_kvs_CmptNameG {[B := 1%Z]} _ _ _).
  - intros C.
    rewrite dom_singleton_L.
    apply elem_of_singleton.
    pose proof (finite.elem_of_enum C).
    cbn in *.
    by apply list_elem_of_singleton.
  - rewrite map_to_list_singleton list_fmap_singleton /=.
    apply NoDup_singleton.
  - intros C ku HC.
    destruct (decide (C = B)); simplify_map_eq.
    compute; done.
Qed.

(** END-TO-END THEOREM *)
Theorem kvs_adequacy `{Layout: memory_layout}
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
  set ( cnames := CmptNames_kvs_CmptNameG ).
  set (Σ := #[invΣ
              ; gen_heapΣ Addr Word; gen_heapΣ RegName Word; gen_heapΣ SRegName Word
              ; entryPreΣ ; CSTACK_preΣ
              ; na_invΣ; sealStorePreΣ
              ; STS_preΣ Addr region_type ; heapPreΣ
              ; savedPredΣ (((STS_std_states Addr region_type) * (STS_states * STS_rels)) * CmptName * Word)
              ;  gen_heapΣ nat kvs_entry ; gen_heapΣ Z (gset Z)
      ]).
  eapply (@kvs_adequacy' Σ cnames B); eauto; try typeclasses eauto.
Qed.
