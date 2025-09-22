From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import cmdc cmdc_spec.
From cap_machine Require Import switcher assert logrel.
From cap_machine Require Import mkregion_helpers.
From cap_machine Require Import region_invariants_revocation region_invariants_allocation.
From iris.program_logic Require Import adequacy.
From iris.base_logic Require Import invariants.
From cap_machine Require Import compartment_layout.
From cap_machine Require Import disjoint_regions_tactics.

Class memory_layout `{MP: MachineParameters} := {

    (* switcher *)
    switcher_layout : @switcherLayout MP;
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
      b_switcher e_switcher
      a_switcher_call ot_switcher
      (b_assert assert_cmpt) (e_assert assert_cmpt)
      B_f C_g
  ∧ (cmpt_code main_cmpt) = cmdc_main_code
  ∧ (cmpt_data main_cmpt) = cmdc_main_data
  ∧ (cmpt_exp_tbl_entries main_cmpt) = []

  (* instantiating B *)
  ∧ (cmpt_imports B_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code B_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data B_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries B_cmpt) = [WInt (bitblast.encode_entry_point 1 1)]

  (* instantiating C *)
  ∧ (cmpt_imports C_cmpt) = [switcher_entry]
  ∧ Forall is_z (cmpt_code C_cmpt) (* only instructions *)
  ∧ Forall is_z (cmpt_data C_cmpt) (* TODO generalise: either z or in_region *)
  ∧ (cmpt_exp_tbl_entries C_cmpt) = [WInt (bitblast.encode_entry_point 1 1)]
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

Section helpers_cmdc_adequacy.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).

  Lemma ot_switcher_interp
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (g_etbl : Locality) (a_etbl: Addr)
    (args off : nat) (ot : OType) (Nswitcher : namespace) :
    let b_etbl := (cmpt_exp_tbl_pcc C_cmpt) in
    let b_etbl1 := (cmpt_exp_tbl_cgp C_cmpt) in
    let e_etbl := (cmpt_exp_tbl_entries_end C_cmpt) in
    let entries_etbl := (cmpt_exp_tbl_entries_start C_cmpt) in
    let b_pcc := (cmpt_b_pcc C_cmpt) in
    let e_pcc := (cmpt_e_pcc C_cmpt) in
    let b_cgp := (cmpt_b_cgp C_cmpt) in
    let e_cgp := (cmpt_e_cgp C_cmpt) in
    (entries_etbl <= a_etbl < e_etbl)%a
    → 0 <= args < 7
    → na_inv logrel_nais Nswitcher switcher_inv
    ⊢ inv (export_table_PCCN C) (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN C) (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN C a_etbl) (a_etbl ↦ₐ WInt (encode_entry_point args off))
    -∗ interp W C (WCap RX Global b_pcc e_pcc b_pcc)
    -∗ interp W C (WCap RW Global b_cgp e_cgp b_cgp)
    -∗ WSealed ot_switcher (SCap RO g_etbl b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ ot_switcher_prop W C (WCap RO g_etbl b_etbl e_etbl a_etbl).
  Proof.
    intros b_etbl b_etbl1 e_etbl entries_etbl b_pcc e_pcc b_cgp e_cgp Ha_etbl Hargs.
    iIntros "#Hinv_switcher #Hinv_pcc #Hinv_cgp #Hinv_entry #Hinterp_pcc #Hinterp_cgp #Hentry".
    iEval (cbn).
    iExists _,_,_,_, b_pcc, e_pcc, b_cgp, e_cgp, args, off.
    iFrame "#".
    iSplit ; first (by iPureIntro).
    iSplit.
    { iPureIntro. subst b_etbl e_etbl entries_etbl.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_cgp_size C_cmpt) as H2.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as H3.
      split ; try solve_addr.
    }
    iSplit.
    { iPureIntro. subst b_etbl.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as Hsize.
      solve_addr+Hsize.
    }
    iSplit.
    { iPureIntro. subst b_etbl e_etbl entries_etbl.
      pose proof (cmpt_exp_tbl_cgp_size C_cmpt) as H2.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as H3.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      solve_addr.
    }
    iSplit; first (iPureIntro ; lia).
    iSplit.
    { subst b_etbl1 b_etbl.
      replace (cmpt_exp_tbl_cgp C_cmpt ) with (cmpt_exp_tbl_pcc C_cmpt ^+ 1)%a; auto.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
      solve_addr.
    }

    iIntros (regs cstk Ws Cs W' Hrelated).
    iDestruct (interp_monotone_nl with "[] [] [$Hinterp_pcc]")
      as "Hinterp_pcc'"; eauto.
    iDestruct (interp_monotone_nl with "[] [] [$Hinterp_cgp]")
      as "Hinterp_cgp'"; eauto.
    iDestruct (interp_weakeningEO W' C
                 RX RX Global Global b_pcc b_pcc e_pcc e_pcc b_pcc (b_pcc ^+ off%nat)%a
                with "Hinterp_pcc'") as "Hinterp_PCC"; eauto; try solve_addr.
    iModIntro;iNext.

    iIntros (??)
      "( Hcont & %Hfreq & ( %Hfullmap & %Hregs_pc & %Hregs_cgp & %Hregs_cra
                     & %Hregs_csp & Hinterp_csp & Hregs_interp)
                     & Hrmap & Hregion & Hworld & %Hcsp_sync & Htframe & Hna)".
    pose proof (Hfullmap csp) as [wcsp Hwcsp].
    iDestruct (fundamental.fundamental with "[$] Hinterp_PCC") as "H_jmp".
    iSpecialize ("H_jmp" $! regs).
    iEval (rewrite /interp_expression /interp_expr /=) in "H_jmp".
    iApply "H_jmp".
    rewrite insert_id ; last done.
    iFrame "∗%#".
    iIntros (r v Hrpc Hr).
    destruct (decide (r = cgp)) as [-> | Hrcgp].
    { rewrite Hregs_cgp in Hr ; simplify_eq.
      iApply interp_monotone_nl; eauto.
    }
    destruct (decide (r = cra)) as [-> | Hrcra].
    { rewrite Hregs_cra in Hr ; simplify_eq.
      iApply switcher_return_interp.
    }
    destruct (decide (r = csp)) as [-> | Hrcsp].
    { by rewrite Hregs_csp in Hr ; simplify_eq. }
    assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)) as Hrr.
    { set_solver+Hrpc Hrcgp Hrcsp Hrcra. }
    by iSpecialize ("Hregs_interp" $! r _ Hrr Hr).
  Qed.

  Lemma mono_priv_ot_switcher (C : CmptName) (w : Word) :
    ⊢ future_priv_mono C ot_switcher_propC w.
  Proof.
    iIntros (W W' Hrelated_W_W').
    iModIntro.
    iIntros "Hot_switcher".
    iEval (cbn) in "Hot_switcher".
    iEval (cbn).
    iDestruct "Hot_switcher" as
      (g_tbl b_tbl e_tbl a_tbl bpcc epcc bcgp ecgp nargs off ->
       Hatbl Hbtbl Hbtbl1 Hnargs) "(Hinvpcc & Hinvcgp & Hinventry & #Hentry & #Hcont)".
    iFrame "Hinvpcc Hinvcgp Hinventry Hentry".
    iExists _,_.
    repeat (iSplit ; first done).
    iModIntro.
    iIntros (regs cstk Ws Cs W'' Hrelated_W'_W'').
    iSpecialize ("Hcont" $! regs cstk Ws Cs W'').
    iApply "Hcont".
    iPureIntro.
    by eapply related_sts_priv_trans_world.
  Qed.

  Lemma ot_switcher_interp_entry
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (a_etbl: Addr)
    (args off : nat) (ot : OType) (Nswitcher : namespace) :
    let b_etbl := (cmpt_exp_tbl_pcc C_cmpt) in
    let b_etbl1 := (cmpt_exp_tbl_cgp C_cmpt) in
    let e_etbl := (cmpt_exp_tbl_entries_end C_cmpt) in
    let entries_etbl := (cmpt_exp_tbl_entries_start C_cmpt) in
    let b_pcc := (cmpt_b_pcc C_cmpt) in
    let e_pcc := (cmpt_e_pcc C_cmpt) in
    let b_cgp := (cmpt_b_cgp C_cmpt) in
    let e_cgp := (cmpt_e_cgp C_cmpt) in
    (entries_etbl <= a_etbl < e_etbl)%a
    → 0 <= args < 7
    → na_inv logrel_nais Nswitcher switcher_inv
    ⊢ inv (export_table_PCCN C) (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN C) (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN C a_etbl) (a_etbl ↦ₐ WInt (encode_entry_point args off))
    -∗ seal_pred ot ot_switcher_propC
    -∗ interp W C (WCap RX Global b_pcc e_pcc b_pcc)
    -∗ interp W C (WCap RW Global b_cgp e_cgp b_cgp)
    -∗ WSealed ot_switcher (SCap RO Global b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ WSealed ot_switcher (SCap RO Local b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ interp W C (WSealed ot (SCap RO Global b_etbl e_etbl a_etbl)).
  Proof.
    intros b_etbl b_etbl1 e_etbl entries_etbl b_pcc e_pcc b_cgp e_cgp Ha_etbl Hargs.
    iIntros "#Hinv_switcher #Hinv_pcc #Hinv_cgp #Hinv_entry
    #Hsealed_pred_ot_switcher #Hinterp_pcc #Hinterp_cgp #Hentry #Hentry'".

    iEval (rewrite fixpoint_interp1_eq); iEval (cbn).
    rewrite /interp_sb.
    iFrame "Hsealed_pred_ot_switcher".
    iSplit; first (iPureIntro ; apply persistent_cond_ot_switcher).
    iSplit; first (iIntros (w) ; iApply mono_priv_ot_switcher).
    iSplit; iApply (ot_switcher_interp with "[$] [$] [$] [$] [$] [$]"); eauto.
  Qed.

End helpers_cmdc_adequacy.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {mem_preg: gen_heapGpreS Addr Word Σ}.
  Context {reg_preg: gen_heapGpreS RegName Word Σ}.
  Context {sreg_preg: gen_heapGpreS SRegName Word Σ}.
  Context {entry_preg : entryGpreS Σ}.
  Context {seal_store_preg: sealStorePreG Σ}.
  Context {na_invg: na_invG Σ}.
  Context {sts_preg: STS_preG Addr region_type Σ}.
  Context {cstack_preg: CSTACK_preG Σ }.
  Context {cname : CmptNameG}.
  Context {heappreg: heapGpreS Σ}.
  Context `{MP: MachineParameters}.
  Context {B C : CmptName}.
  Context { HCNames : CNames = (list_to_set [B;C]) }.
  Context { HCNamesNoDup : NoDup [B;C] }.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).

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
                    & B_imports & B_code & B_data & B_exp_tbl
                    & C_imports & C_code & C_data & C_exp_tbl
                   ).
    iMod (gen_heap_init (reg:Reg)) as (reg_heapg) "(Hreg_ctx & Hreg & _)".
    iMod (gen_heap_init (sreg:SReg)) as (sreg_heapg) "(Hsreg_ctx & Hsreg & _)".
    iMod (gen_heap_init (m:Mem)) as (mem_heapg) "(Hmem_ctx & Hmem & _)".
    iMod (seal_store_init ({[ ot_switcher ]} : gset _)) as (seal_storeg) "Hseal_store".
    set (
        B_f :=
       (WCap RO Global (cmpt_exp_tbl_pcc B_cmpt)
                         (cmpt_exp_tbl_entries_end B_cmpt) (cmpt_exp_tbl_entries_start B_cmpt))
      ).
    set (
        C_g :=
       (WCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
         (cmpt_exp_tbl_entries_start C_cmpt))
      ).
    assert (B_f ≠ C_g) as Hneq_entries.
    { intro H ; subst B_f C_g ; simplify_eq.
      pose proof cmpts_disjoints as (_&_&Hdisjoint).
      rewrite /disjoint /Cmpt_Disjoint /disjoint_cmpt /cmpt_region in Hdisjoint.
      assert (
          cmpt_exp_tbl_region B_cmpt  ## cmpt_exp_tbl_region C_cmpt
        ) as Hdis by set_solver+Hdisjoint.
      rewrite /cmpt_exp_tbl_region in Hdis.
      apply stdpp_extra.list_to_set_disj in Hdis.
      rewrite H H0 in Hdis.
      assert (
          list_to_set
            (finz.seq_between (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt))
            ≠ (∅ : gset Addr)
        ) as Hemp; [|set_solver+Hdis Hemp].
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as Hc.
      pose proof (cmpt_exp_tbl_cgp_size C_cmpt) as Hc'.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as Hc''.
      rewrite finz_seq_between_cons ; last (solve_addr+ Hc Hc' Hc'').
      set_solver+.
    }

    iMod (
       entry_init (
           {[
               (seal_capability B_f ot_switcher) := 1;
               (borrow (seal_capability B_f ot_switcher)) := 1;
               (seal_capability C_g ot_switcher) := 1;
               (borrow (seal_capability C_g ot_switcher)) := 1
           ]}

         )
      ) as (entry_g) "Hentries".
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Bf Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Bf' Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[#Hentry_Cg Hentries]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    iDestruct (big_sepM_insert_delete with "Hentries") as "[Hentry_Cg' _]"
    ; repeat (rewrite delete_insert_ne ; last (subst B_f C_g ; intro ; simplify_eq; by rewrite H H0 H1 in Hneq_entries)).
    subst B_f C_g; cbn.
    set (B_f := (SCap RO Global (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                   (cmpt_exp_tbl_entries_start B_cmpt))).
    set (B_f' := (SCap RO Local (cmpt_exp_tbl_pcc B_cmpt) (cmpt_exp_tbl_entries_end B_cmpt)
                   (cmpt_exp_tbl_entries_start B_cmpt))).
    set (C_g := (SCap RO Global (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).
    set (C_g' := (SCap RO Local (cmpt_exp_tbl_pcc C_cmpt) (cmpt_exp_tbl_entries_end C_cmpt)
                   (cmpt_exp_tbl_entries_start C_cmpt))).




    unshelve iMod (gen_sts_init 0) as (stsg) "Hsts"; eauto. (*XX*)
    iMod (gen_cstack_init []) as (cstackg) "[Hcstk_full Hcstk_frag]".
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

    pose ceriseg := CeriseG Σ Hinv mem_heapg reg_heapg sreg_heapg entry_g.
    pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
    pose switcher_layout_g := (@switcher_layout MP Layout).

    pose proof (
        @cmdc_spec_full Σ ceriseg seal_storeg _ _ _ logrel_na_invs _ _  switcher_layout_g B C
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

    (* CMPT B *)
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
           with "Hsts_B Hr_B [HB_code]") as "(Hr_B & #HB_code & Hsts_B)".
    { done. }
    { apply Forall_true. intros.
      by rewrite lookup_empty.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HB_code]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ B_code Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite /interpC /safeC fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (extend_region_perm_sepL2 _ _ B
            (finz.seq_between (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt))
            (cmpt_data B_cmpt)
            RW interpC
           with "Hsts_B Hr_B [HB_data]") as "(Hr_B & #HB_data & Hsts_B)".
    { done. }
    { apply Forall_forall. intros a Ha.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      pose proof (cmpt_cgp_disjoint B_cmpt) as Hdisjoint.
      apply map_disjoint_dom_1 in Hdisjoint.
      rewrite /cmpt_pcc_mregion dom_union_L in Hdisjoint.
      rewrite disjoint_union_l in Hdisjoint.
      destruct Hdisjoint as [_ Hdisjoint].
      pose proof (cmpt_data_size B_cmpt) as Hsize_data.
      pose proof (cmpt_code_size B_cmpt) as Hsize_code.
      rewrite !dom_mkregion_eq in Hdisjoint; auto.
      apply list_to_set_disj_2 in Hdisjoint.
      rewrite /disjoint /set_disjoint_instance in Hdisjoint.
      intro Ha'.
      apply (Hdisjoint a); auto.
    }
    {
      iApply (big_sepL2_mono ((fun (_ : nat) (k : finz.finz MemNum) (v : Word) =>
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HB_data]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ B_data Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite /interpC /safeC fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (extend_region_perm_sepL2 _ _ B
            [cmpt_b_pcc B_cmpt]
            (cmpt_imports B_cmpt)
            RX interpC
           with "Hsts_B Hr_B [HB_imports]") as "(Hr_B & [#HB_imports _] & Hsts_B)".
    { done. }
    { apply Forall_forall.
      intros a Ha.
      apply elem_of_list_singleton in Ha; simplify_eq.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      + rewrite std_sta_update_multiple_lookup_same_i; auto.
        pose proof (cmpt_import_size B_cmpt) as HB.
        apply not_elem_of_finz_seq_between.
        rewrite B_imports in HB.
        left; solve_addr+HB.
      + pose proof (cmpt_disjointness B_cmpt) as HB.
        apply disjoint_regions_tactics.disjoint_list_cons in HB
        ; destruct HB as [HB _].
        rewrite union_list_cons in HB.
        cbn in HB.
        assert (
            finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt)
              ## finz.seq_between (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt)
          ) as HB' by set_solver+HB
        ; clear HB.
        intro Hcontra ; eapply HB'; eauto.
        pose proof (cmpt_import_size B_cmpt) as H.
        rewrite B_imports /= in H.
        pose proof (cmpt_code_size B_cmpt) as H'.
        apply elem_of_finz_seq_between; solve_addr+H H'.
    }
    {
      rewrite B_imports; cbn; iFrame.
      rewrite /interpC /safeC /=.
      iSplit; first iApply switcher_call_interp.
      (* TODO make lemma *)
      iModIntro.
      iIntros (???) "?"; iApply switcher_call_interp.
    }

    iMod ( extend_region_revoked_sepL2 _ _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             RWL interpC
           with "[$Hsts_B] [$Hr_B]")
           as "(Hr_B & Hrel_stk_B & Hsts_B)".
    { apply Forall_forall; intros a Ha; cbn.
      pose proof (cmpt_import_size B_cmpt) as H.
      rewrite B_imports /= in H.
      pose proof (cmpt_code_size B_cmpt) as H'.
      pose proof switcher_cmpt_disjoints as (_ & Hb & _).

      rewrite lookup_insert_ne.
      2: { intro Hcontra.
           assert (a ∈ finz.seq_between (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt)).
           { rewrite -Hcontra.
             apply elem_of_finz_seq_between; solve_addr+H H'.
           }
           apply (Hb a).
           + rewrite /cmpt_switcher_region.
             eapply elem_of_union;eauto.
           + eapply elem_of_union;eauto.
             left; eapply elem_of_union;eauto.
      }
      rewrite std_sta_update_multiple_lookup_same_i.
      2: { intro Hcontra.
           apply (Hb a); eauto.
           + eapply elem_of_union;eauto.
           + eapply elem_of_union;eauto.
             left;eapply elem_of_union;eauto.
      }
      rewrite std_sta_update_multiple_lookup_same_i; first done.
      intro Hcontra.
      apply (Hb a); eauto.
      + eapply elem_of_union;eauto.
      + eapply elem_of_union;eauto.
        left;eapply elem_of_union;eauto.
        left.
        rewrite elem_of_finz_seq_between in Hcontra.
        apply elem_of_finz_seq_between; solve_addr+H H' Hcontra.
    }

    match goal with
    | H: _ |- context [  (sts_full_world ?W B) ] => set (Winit_B := W)
    end.


    iEval (rewrite /cmpt_exp_tbl_mregion) in "HB_etbl".
    iDestruct (big_sepM_union with "HB_etbl") as "[HB_etbl HB_etbl_entries]".
    { admit. }
    iDestruct (big_sepM_union with "HB_etbl") as "[HB_etbl_pcc HB_etbl_cgp]".
    { admit. }
    iDestruct (mkregion_prepare with "[HB_etbl_entries]") as ">HB_etbl_entries"; auto.
    { apply cmpt_exp_tbl_entries_size. }
    iDestruct (mkregion_prepare with "[HB_etbl_pcc]") as ">HB_etbl_pcc"; auto.
    { cbn; apply cmpt_exp_tbl_pcc_size. }
    iDestruct (mkregion_prepare with "[HB_etbl_cgp]") as ">HB_etbl_cgp"; auto.
    { cbn; apply cmpt_exp_tbl_cgp_size. }
    iEval (rewrite B_exp_tbl) in "HB_etbl_entries".
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_entries_start B_cmpt)).
    2: {
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      by rewrite B_exp_tbl in H1; cbn in H1.
    }
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_pcc B_cmpt))
    ; last (apply cmpt_exp_tbl_pcc_size).
    rewrite (finz_seq_between_singleton (cmpt_exp_tbl_cgp B_cmpt))
    ; last (apply cmpt_exp_tbl_cgp_size).
    rewrite !big_sepL2_singleton.

    iMod (inv_alloc (switcher_preamble.export_table_PCCN B) ⊤ _
           with "HB_etbl_pcc")%I as "#HB_etbl_pcc".
    iMod (inv_alloc (switcher_preamble.export_table_CGPN B) ⊤ _
           with "HB_etbl_cgp")%I as "#HB_etbl_cgp".
    iMod (inv_alloc (switcher_preamble.export_table_entryN B (cmpt_exp_tbl_entries_start B_cmpt)) ⊤ _
           with "HB_etbl_entries")%I as "#HB_etbl_entries".

    iAssert (interp Winit_B B
               (WCap RX Global (cmpt_b_pcc B_cmpt) (cmpt_e_pcc B_cmpt) (cmpt_b_pcc B_cmpt)%a)
            )%I as "#Hinterp_pcc_B".
    { rewrite fixpoint_interp1_eq /=.
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      rewrite finz_seq_between_cons in Ha.
      2: {
        pose proof (cmpt_import_size B_cmpt) as H1.
        pose proof (cmpt_code_size B_cmpt) as H2.
        rewrite B_imports /= in H1.
        solve_addr.
      }
      pose proof (cmpt_import_size B_cmpt) as Himport_B.
      rewrite B_imports /= in Himport_B.
      replace (cmpt_b_pcc B_cmpt ^+ 1)%a with
        (cmpt_a_code B_cmpt) in Ha by solve_addr+Himport_B.
      iExists RX, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit.
      { destruct k; cbn in Ha ; simplify_eq.
        iFrame "HB_imports".
        rewrite (big_sepL_lookup _ _ _ a); eauto.
      }
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first done.
      subst Winit_B.
      iSplit.
      + iApply (monoReq_interp _ _ _ _ Permanent); last done.
        admit. (* TODO easy but tedious *)
      + iPureIntro.
        admit. (* TODO easy but tedious *)
    }

    iAssert (interp Winit_B B
               (WCap RW Global (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt) (cmpt_b_cgp B_cmpt)%a)
            )%I as "#Hinterp_cgp_B".
    { iEval (rewrite fixpoint_interp1_eq /=).
      iApply big_sepL_intro; iModIntro.
      iIntros (k a Ha).
      iExists RW, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      rewrite (big_sepL_lookup _ (finz.seq_between (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt))
                 k a); eauto.
      iFrame "HB_data".
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first (iNext ; by iApply wcond_interp).
      subst Winit_B.
      iSplit.
      + iApply (monoReq_interp _ _ _ _ Permanent); last done.
        admit. (* TODO easy but tedious *)
      + iPureIntro.
        admit. (* TODO easy but tedious *)
    }

    iAssert ( interp Winit_B B (WSealed ot_switcher B_f)) with
      "[HB_code Hr_B HB_data Hsts_B Hentry_Bf']" as "#Hinterp_B".
    { iApply (ot_switcher_interp_entry _ _ _ _ 1 1
               with "[$] [$] [$] [$] [$] [$] [$] [$]"); eauto; last lia.
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size B_cmpt) as H2.
      rewrite B_exp_tbl in H2.
      solve_addr+H1 H2.
    }
    iClear "HB_etbl_pcc HB_etbl_cgp HB_etbl_entries HB_code HB_data Hinterp_pcc_B Hinterp_cgp_B".

    iAssert ([∗ list] a ∈ finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ,
               rel B a RWL interpC ∗ ⌜ std Winit_B !! a = Some Revoked ⌝ )%I with "[Hrel_stk_B]"
    as "Hrel_stk_B".
    { rewrite big_sepL_sep; iFrame.
      iPureIntro.
      intros k a Ha ; cbn.
      subst Winit_B ; clear -Ha.
      apply std_sta_update_multiple_lookup_in_i.
      rewrite elem_of_list_lookup; naive_solver.
    }


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
    rewrite (finz_seq_between_singleton (cmpt_b_pcc C_cmpt)).
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
                                 pointsto k (DfracOwn (pos_to_Qp 1)) v)) with "[HC_data]").
      - intros k v1 v2 Hv1 Hv2. cbn. iIntros; iFrame.
        pose proof (Forall_lookup_1 _ _ _ _ C_data Hv2) as Hncap.
        destruct v2; [| by inversion Hncap..].
        rewrite /interpC /safeC fixpoint_interp1_eq /=.
        iSplit; eauto.
        iApply future_priv_mono_interp_z.
      - iFrame.
    }

    iMod (extend_region_perm_sepL2 _ _ C
            [cmpt_b_pcc C_cmpt]
            (cmpt_imports C_cmpt)
            RX interpC
           with "Hsts_C Hr_C [HC_imports]") as "(Hr_C & [#HC_imports _] & Hsts_C)".
    { done. }
    { apply Forall_forall.
      intros a Ha.
      apply elem_of_list_singleton in Ha; simplify_eq.
      rewrite std_sta_update_multiple_lookup_same_i; auto.
      + rewrite std_sta_update_multiple_lookup_same_i; auto.
        pose proof (cmpt_import_size C_cmpt) as HC.
        apply not_elem_of_finz_seq_between.
        rewrite C_imports in HC.
        left; solve_addr+HC.
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
        apply elem_of_finz_seq_between; solve_addr+H H'.
    }
    {
      rewrite C_imports; cbn; iFrame.
      rewrite /interpC /safeC /=.
      iSplit; first iApply switcher_call_interp.
      (* TODO make lemma *)
      iModIntro.
      iIntros (???) "?"; iApply switcher_call_interp.
    }

    iMod ( extend_region_revoked_sepL2 _ _ _
             (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt))
             RWL interpC
           with "[$Hsts_C] [$Hr_C]")
           as "(Hr_C & Hrel_stk_C & Hsts_C)".
    { apply Forall_forall; intros a Ha; cbn.
      pose proof (cmpt_import_size C_cmpt) as H.
      rewrite C_imports /= in H.
      pose proof (cmpt_code_size C_cmpt) as H'.
      pose proof switcher_cmpt_disjoints as (_ & _ & Hc).

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
    match goal with
    | H: _ |- context [  (sts_full_world ?W C) ] => set (Winit_C := W)
    end.


    iEval (rewrite /cmpt_exp_tbl_mregion) in "HC_etbl".
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl HC_etbl_entries]".
    { admit. }
    iDestruct (big_sepM_union with "HC_etbl") as "[HC_etbl_pcc HC_etbl_cgp]".
    { admit. }
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

    iMod (inv_alloc (switcher_preamble.export_table_PCCN C) ⊤ _
           with "HC_etbl_pcc")%I as "#HC_etbl_pcc".
    iMod (inv_alloc (switcher_preamble.export_table_CGPN C) ⊤ _
           with "HC_etbl_cgp")%I as "#HC_etbl_cgp".
    iMod (inv_alloc (switcher_preamble.export_table_entryN C (cmpt_exp_tbl_entries_start C_cmpt)) ⊤ _
           with "HC_etbl_entries")%I as "#HC_etbl_entries".

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
      pose proof (cmpt_import_size C_cmpt) as Himport_C.
      rewrite C_imports /= in Himport_C.
      replace (cmpt_b_pcc C_cmpt ^+ 1)%a with
        (cmpt_a_code C_cmpt) in Ha by solve_addr+Himport_C.
      iExists RX, interp.
      iEval (cbn).
      iSplit; first done.
      iSplit; first (iPureIntro ; by apply persistent_cond_interp).
      iSplit.
      { destruct k; cbn in Ha ; simplify_eq.
        iFrame "HC_imports".
        rewrite (big_sepL_lookup _ _ _ a); eauto.
      }
      iSplit; first (iNext ; by iApply zcond_interp).
      iSplit; first (iNext ; by iApply rcond_interp).
      iSplit; first done.
      subst Winit_C.
      iSplit.
      + iApply (monoReq_interp _ _ _ _ Permanent); last done.
        admit. (* TODO easy but tedious *)
      + iPureIntro.
        admit. (* TODO easy but tedious *)
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
      subst Winit_C.
      iSplit.
      + iApply (monoReq_interp _ _ _ _ Permanent); last done.
        admit. (* TODO easy but tedious *)
      + iPureIntro.
        admit. (* TODO easy but tedious *)
    }

    iAssert ( interp Winit_C C (WSealed ot_switcher C_g)) with
      "[HC_code Hr_C HC_data Hsts_C Hentry_Cg']" as "#Hinterp_C".
    { iApply (ot_switcher_interp_entry _ _ _ _ 1 1
               with "[$] [$] [$] [$] [$] [$] [$] [$]"); eauto; last lia.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H2.
      rewrite C_exp_tbl in H2.
      solve_addr+H1 H2.
    }
    iClear "HC_etbl_pcc HC_etbl_cgp HC_etbl_entries HC_code HC_data Hinterp_pcc_C Hinterp_cgp_C".

    iAssert ([∗ list] a ∈ finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt) ,
               rel C a RWL interpC ∗ ⌜ std Winit_C !! a = Some Revoked ⌝ )%I with "[Hrel_stk_C]"
    as "Hrel_stk_C".
    { rewrite big_sepL_sep; iFrame.
      iPureIntro.
      intros k a Ha ; cbn.
      subst Winit_C ; clear -Ha.
      apply std_sta_update_multiple_lookup_in_i.
      rewrite elem_of_list_lookup; naive_solver.
    }

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

    iPoseProof (Spec _ _ _ _ _ _ _
                  _ _ _ _ _ _ _ _
                  [] [] _ (fun _ => True)%I assertN switcherN []
                 with "[ $Hassert $Hswitcher $Hna
                        $Hr_B $Hr_C $Hsts_B $Hsts_C
                        $HPC $Hcgp $Hcsp $Hreg
                        $Hmain_imports $Hmain_code $Hmain_data $Hstack
                        $Hinterp_B $Hinterp_C $Hcstk_frag $Hrel_stk_B $Hrel_stk_C
                        $Hentry_Bf $Hentry_Cg
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
      - assert ( cmpt_b_cgp main_cmpt ∈ finz.seq_between (cmpt_b_cgp main_cmpt)
                   (cmpt_e_cgp main_cmpt)).
        { pose proof (cmpt_data_size main_cmpt) as H.
          rewrite elem_of_finz_seq_between.
          rewrite main_data in H; cbn.
          solve_addr+H.
        }
        assert (
            finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt)
              ##
              finz.seq_between (cmpt_b_cgp main_cmpt) (cmpt_e_cgp main_cmpt)
          ) as H'; last set_solver+H H' Hcontra.
        admit.
      - apply elem_of_dom_std_multiple_update in Hcontra.
        destruct Hcontra as [Hcontra|Hcontra].
        + admit.
        + apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          * admit.
          * apply elem_of_dom_std_multiple_update in Hcontra.
            destruct Hcontra as [Hcontra|Hcontra].
            ** admit.
            ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
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
          * apply elem_of_dom_std_multiple_update in Hcontra.
          destruct Hcontra as [Hcontra|Hcontra].
          ** admit.
          ** rewrite /= dom_empty_L in Hcontra; set_solver+Hcontra.
    }
    { rewrite /revoke_condition.
      intros a.
      subst Winit_B.
      clear.
      destruct (decide ( a ∈ (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ [cmpt_b_pcc B_cmpt])).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ (finz.seq_between (cmpt_b_cgp B_cmpt) (cmpt_e_cgp B_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ (finz.seq_between (cmpt_a_code B_cmpt) (cmpt_e_pcc B_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
    }
    { rewrite /revoke_condition.
      intros a.
      subst Winit_C.
      clear.
      destruct (decide ( a ∈ (finz.seq_between (b_stack switcher_cmpt) (e_stack switcher_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ [cmpt_b_pcc C_cmpt])).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ (finz.seq_between (cmpt_b_cgp C_cmpt) (cmpt_e_cgp C_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
      destruct (decide ( a ∈ (finz.seq_between (cmpt_a_code C_cmpt) (cmpt_e_pcc C_cmpt)))).
      { rewrite std_sta_update_multiple_lookup_in_i //. }
      rewrite std_sta_update_multiple_lookup_same_i //.
    }
    { iNext; iIntros "H". proofmode.wp_end; by iIntros. }

    iModIntro.
    iExists (fun σ _ _ => ( ((gen_heap_interp σ.1.1) ∗ (gen_heap_interp σ.1.2)) ∗ (gen_heap_interp σ.2)))%I.
    iExists (fun _ => True)%I. cbn. iFrame.

    iIntros "[ [Hreg' Hsreg'] Hmem']". iExists (⊤ ∖ ↑flagN).
    iInv flagN as ">Hflag" "Hclose".
    iDestruct (gen_heap_valid with "Hmem' Hflag") as %Hm'_flag.
    iModIntro. iPureIntro. rewrite /state_is_good //=.
  Admitted.
End Adequacy.
