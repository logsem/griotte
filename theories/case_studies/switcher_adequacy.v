From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel interp_weakening monotone.
From cap_machine Require Import switcher logrel.
From iris.base_logic Require Import invariants.
From cap_machine Require Import compartment_layout.
From cap_machine Require Import interp_switcher_call interp_switcher_return.

Section helpers_switcher_adequacy.
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

  Lemma ot_switcher_interp
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (g_etbl : Locality) (a_etbl: Addr)
    (args off : nat) (ot : OType) (Nswitcher CNAME : namespace) :
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
    ⊢ inv (export_table_PCCN CNAME) (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN CNAME) (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN CNAME a_etbl) (a_etbl ↦ₐ WInt (encode_entry_point args off))
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
                     & %Hregs_csp & Hinterp_csp & Hregs_interp & Hregs_zeros)
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
      iApply (interp_switcher_return with "Hinv_switcher").
    }
    destruct (decide (r = csp)) as [-> | Hrcsp].
    { by rewrite Hregs_csp in Hr ; simplify_eq. }
    assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)) as Hrr.
    { set_solver+Hrpc Hrcgp Hrcsp Hrcra. }
    destruct (decide ( r ∈ dom_arg_rmap args)) as [Hr_arg | Hr_arg].
    + iApply "Hregs_interp"; eauto.
    + assert (r ∉ {[PC; cra; cgp; csp]} ∪ dom_arg_rmap args) as Hrrr by set_solver+Hrr Hr_arg.
      iSpecialize ("Hregs_zeros" $! r _ Hrrr Hr); iDestruct "Hregs_zeros" as "->".
      iApply interp_int.
  Qed.

  Lemma ot_switcher_interp_entry
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (a_etbl: Addr)
    (args off : nat) (ot : OType) (Nswitcher CNAME : namespace) :
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
    ⊢ inv (export_table_PCCN CNAME) (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN CNAME) (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN CNAME a_etbl) (a_etbl ↦ₐ WInt (encode_entry_point args off))
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

End helpers_switcher_adequacy.
