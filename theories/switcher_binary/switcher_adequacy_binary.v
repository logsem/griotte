From iris.proofmode Require Import proofmode.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary fundamental_binary interp_weakening_binary monotone_binary.
From iris.base_logic Require Import invariants.
From griotte Require Import compartment_layout.
From griotte Require Import switcher_preamble_binary interp_switcher_call_binary interp_switcher_return_binary.

(** * Entry points of compartments in the binary model

    Helper lemmas for the adequacy proofs of the binary model: the entry
    points of a compartment whose code and data capabilities are safe to
    share (in both runs) satisfy the sealing predicate of the switcher's
    otype. *)

Section helpers_switcher_adequacy.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma fundamental_execute_entry_point
    (W : WORLD) (C : CmptName) ( b_pcc e_pcc b_cgp e_cgp : Addr )
    (args off : nat) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp W C (WCap RX Global b_pcc e_pcc b_pcc, WCap RX Global b_pcc e_pcc b_pcc) -∗
    interp W C (WCap RW Global b_cgp e_cgp b_cgp, WCap RW Global b_cgp e_cgp b_cgp) -∗
    □ ∀ (W' : WORLD),
    ⌜related_sts_priv_world W W'⌝
    → ▷ execute_entry_point
          (WCap RX Global b_pcc e_pcc (b_pcc ^+ off)%a, WCap RX Global b_pcc e_pcc (b_pcc ^+ off)%a)
          (WCap RW Global b_cgp e_cgp b_cgp, WCap RW Global b_cgp e_cgp b_cgp)
          args W' C.
  Proof.
    iIntros "#Hinv_switcher #Hinterp_pcc #Hinterp_cgp".
    iIntros (W' Hrelated).
    iDestruct (interp_monotone_nl with "[] [] [$Hinterp_pcc]")
      as "Hinterp_pcc'"; eauto.
    iDestruct (interp_monotone_nl with "[] [] [$Hinterp_cgp]")
      as "Hinterp_cgp'"; eauto.
    iDestruct (interp_weakeningEO W' C
                 RX RX Global Global b_pcc b_pcc e_pcc e_pcc b_pcc (b_pcc ^+ off%nat)%a
                with "Hinterp_pcc'") as "Hinterp_PCC"; eauto; try solve_addr.
    iModIntro;iNext.

    iIntros (stk Ws Cs regs1 regs2 ??)
      "(#Hspec & Hcont & %Hfreq & ( %Hfullmap1 & %Hfullmap2 & %Hregs_pc1 & %Hregs_pc2
                     & %Hregs_cgp1 & %Hregs_cgp2 & %Hregs_cra1 & %Hregs_cra2
                     & %Hregs_csp1 & %Hregs_csp2 & Hinterp_csp & Hregs_interp
                     & Hregs_zeros1 & Hregs_zeros2)
                     & Hrmap & Hsmap & Hj & Hworld_interp & %Hcsp_sync & Htframe & Htframe_spec & Hna)".
    cbn in Hfullmap1, Hfullmap2, Hregs_pc1, Hregs_pc2, Hregs_cgp1, Hregs_cgp2,
      Hregs_cra1, Hregs_cra2, Hregs_csp1, Hregs_csp2.
    iDestruct (fundamental with "Hinterp_PCC") as "H_jmp".
    iSpecialize ("H_jmp" $! stk Ws Cs regs1 regs2).
    iEval (rewrite /interp_expression /interp_expr /=) in "H_jmp".
    iApply "H_jmp".
    rewrite /registers_pointsto /spec_registers_pointsto.
    rewrite !insert_id ; [|done|done].
    iFrame "∗%#".
    iIntros (r v1 v2 Hrpc Hr1 Hr2); cbn in Hr1, Hr2.
    destruct (decide (r = cgp)) as [-> | Hrcgp].
    { rewrite Hregs_cgp1 in Hr1; rewrite Hregs_cgp2 in Hr2; simplify_eq.
      iApply interp_monotone_nl; eauto.
    }
    destruct (decide (r = cra)) as [-> | Hrcra].
    { rewrite Hregs_cra1 in Hr1; rewrite Hregs_cra2 in Hr2; simplify_eq.
      iApply (interp_switcher_return with "Hinv_switcher").
    }
    destruct (decide (r = csp)) as [-> | Hrcsp].
    { by rewrite Hregs_csp1 in Hr1; rewrite Hregs_csp2 in Hr2; simplify_eq. }
    assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)) as Hrr.
    { set_solver+Hrpc Hrcgp Hrcsp Hrcra. }
    destruct (decide ( r ∈ dom_arg_rmap args)) as [Hr_arg | Hr_arg].
    + iApply "Hregs_interp"; eauto.
    + assert (r ∉ {[PC; cra; cgp; csp]} ∪ dom_arg_rmap args) as Hrrr by set_solver+Hrr Hr_arg.
      iDestruct ("Hregs_zeros1" $! r _ Hrrr Hr1) as "->".
      iDestruct ("Hregs_zeros2" $! r _ Hrrr Hr2) as "->".
      iApply interp_int.
  Qed.

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
    → na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ inv (export_table_PCCN CNAME)
        (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc ∗ b_etbl ↣ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN CNAME)
        (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp ∗ b_etbl1 ↣ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN CNAME a_etbl)
        (a_etbl ↦ₐ WInt (encode_entry_point args off) ∗ a_etbl ↣ₐ WInt (encode_entry_point args off))
    -∗ interp W C (WCap RX Global b_pcc e_pcc b_pcc, WCap RX Global b_pcc e_pcc b_pcc)
    -∗ interp W C (WCap RW Global b_cgp e_cgp b_cgp, WCap RW Global b_cgp e_cgp b_cgp)
    -∗ WSealed ot_switcher (SCap RO g_etbl b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ ot_switcher_prop W C (WCap RO g_etbl b_etbl e_etbl a_etbl, WCap RO g_etbl b_etbl e_etbl a_etbl).
  Proof.
    intros b_etbl b_etbl1 e_etbl entries_etbl b_pcc e_pcc b_cgp e_cgp Ha_etbl Hargs.
    iIntros "#Hinv_switcher #Hinv_pcc #Hinv_cgp #Hinv_entry #Hinterp_pcc #Hinterp_cgp #Hentry".
    iExists _,_,_,_, b_pcc, e_pcc, b_cgp, e_cgp, args, off.
    iFrame "#".
    iSplit ; first (by iPureIntro).
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
    iApply fundamental_execute_entry_point; eauto.
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
    → na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ inv (export_table_PCCN CNAME)
        (b_etbl ↦ₐ WCap RX Global b_pcc e_pcc b_pcc ∗ b_etbl ↣ₐ WCap RX Global b_pcc e_pcc b_pcc)
    -∗ inv (export_table_CGPN CNAME)
        (b_etbl1 ↦ₐ WCap RW Global b_cgp e_cgp b_cgp ∗ b_etbl1 ↣ₐ WCap RW Global b_cgp e_cgp b_cgp)
    -∗ inv (export_table_entryN CNAME a_etbl)
        (a_etbl ↦ₐ WInt (encode_entry_point args off) ∗ a_etbl ↣ₐ WInt (encode_entry_point args off))
    -∗ seal_pred ot ot_switcher_propC
    -∗ interp W C (WCap RX Global b_pcc e_pcc b_pcc, WCap RX Global b_pcc e_pcc b_pcc)
    -∗ interp W C (WCap RW Global b_cgp e_cgp b_cgp, WCap RW Global b_cgp e_cgp b_cgp)
    -∗ WSealed ot_switcher (SCap RO Global b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ WSealed ot_switcher (SCap RO Local b_etbl e_etbl a_etbl) ↦□ₑ args
    -∗ interp W C (WSealed ot (SCap RO Global b_etbl e_etbl a_etbl),
                   WSealed ot (SCap RO Global b_etbl e_etbl a_etbl)).
  Proof.
    intros b_etbl b_etbl1 e_etbl entries_etbl b_pcc e_pcc b_cgp e_cgp Ha_etbl Hargs.
    iIntros "#Hinv_switcher #Hinv_pcc #Hinv_cgp #Hinv_entry
    #Hsealed_pred_ot_switcher #Hinterp_pcc #Hinterp_cgp #Hentry #Hentry'".

    rewrite interp_sealed_inv.
    iSplit; first done.
    rewrite /interp_sb.
    iExists ot_switcher_prop.
    iFrame "Hsealed_pred_ot_switcher".
    iSplit; first (iPureIntro ; apply persistent_cond_ot_switcher).
    iSplit; first (iIntros (w) ; iApply mono_priv_ot_switcher).
    iSplit; first done.
    iSplit; iNext; iApply (ot_switcher_interp with "[$] [$] [$] [$] [$] [$]"); eauto.
  Qed.

End helpers_switcher_adequacy.
