From iris.proofmode Require Import proofmode.
From griotte Require Import logrel fundamental.
From iris.base_logic Require Import invariants.
From griotte Require Import compartment_layout.
From griotte Require Import switcher_preamble interp_switcher_call interp_switcher_return.
From griotte Require Import switcher_exception_stub.

Section helpers_switcher_adequacy.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {relg : relGS Σ}
    {cstackg : CSTACKG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutWf : switcherLayoutWf}
  .

  Lemma fundamental_execute_entry_point
    (W : WORLD) (C : CmptName) ( b_pcc e_pcc b_cgp e_cgp : Addr )
    (args minstk off : nat) (Nswitcher : namespace) :
    disjoint_from_heap b_cgp e_cgp ->
    na_inv cerise_nais Nswitcher switcher_inv
    ⊢ switcher_static -∗
    interp W C (WCap true RX Global b_pcc e_pcc b_pcc) -∗
    interp W C (WCap true RW Global b_cgp e_cgp b_cgp) -∗
    □ ∀ (W' : WORLD),
    ⌜related_sts_priv_world W W'⌝
    → ▷ execute_entry_point (WCap true RX Global b_pcc e_pcc (b_pcc ^+ off)%a) (WCap true RW Global b_cgp e_cgp b_cgp)
        args minstk W' C.
  Proof.
    intros Hcgp_heap.
    iIntros "#Hinv_switcher #Hswitcher_static #Hinterp_pcc #Hinterp_cgp".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hinv_switcher $Hswitcher_static]") as "#Htrap".
    iIntros (W' Hrelated).
    iDestruct (interp_cap_disjoint with "Hinterp_pcc") as %[_ Hpcc_heap]; first done.
    iDestruct (interp_monotone_nl_cap_nonheap W W' C true RX Global
                 b_pcc e_pcc b_pcc Hpcc_heap Hrelated eq_refl
                 with "Hinterp_pcc") as "Hinterp_pcc'".
    iDestruct (interp_monotone_nl_cap_nonheap W W' C true RW Global
                 b_cgp e_cgp b_cgp Hcgp_heap Hrelated eq_refl
                 with "Hinterp_cgp") as "Hinterp_cgp'".
    iDestruct (interp_lea with "Hinterp_pcc'") as "Hinterp_PCC"; first done.
    iModIntro;iNext.

    iIntros (cstk Ws Cs ???)
      "( Hcont & %Hfreq & HPC & ( %Hfullmap & %Hregs_cgp & %Hregs_cra
                     & %Hregs_csp & Hinterp_csp & Hregs_interp & Hregs_zeros)
                     & Hrmap & Hworld_interp & %Hcsp_sync & _ & Htframe & Hna)".
    pose proof (Hfullmap csp) as [wcsp Hwcsp].
    iDestruct (fundamental with "Htrap Hinterp_PCC") as "H_jmp".
    iSpecialize ("H_jmp" $! cstk Ws Cs regs).
    iEval (rewrite /interp_expression /interp_expr /=) in "H_jmp".
    iApply "H_jmp".
    iFrame "∗%#".
    iIntros (r v Hr). iApply interp_filter_heap.
    destruct (decide (r = cgp)) as [-> | Hrcgp].
    { rewrite Hregs_cgp in Hr ; simplify_eq.
      iExact "Hinterp_cgp'".
    }
    destruct (decide (r = cra)) as [-> | Hrcra].
    { destruct Hregs_cra as [mie Hregs_cra].
      rewrite Hregs_cra in Hr ; simplify_eq.
      iApply (interp_switcher_return with "[$Hinv_switcher $Hswitcher_static]").
    }
    destruct (decide (r = csp)) as [-> | Hrcsp].
    { by rewrite Hregs_csp in Hr ; simplify_eq. }
    assert (r ∉ ({[cra; cgp; csp]} : gset RegName)) as Hrr.
    { set_solver+Hrcgp Hrcsp Hrcra. }
    destruct (decide ( r ∈ dom_arg_rmap args)) as [Hr_arg | Hr_arg].
    + iApply "Hregs_interp"; eauto.
    + assert (r ∉ {[cra; cgp; csp]} ∪ dom_arg_rmap args) as Hrrr by set_solver+Hrr Hr_arg.
      iSpecialize ("Hregs_zeros" $! r _ Hrrr Hr); iDestruct "Hregs_zeros" as "->".
      iApply interp_int.
  Qed.

  Lemma ot_switcher_interp
    (W : WORLD) (C : CmptName) (C_cmpt : cmpt)
    (g_etbl : Locality) (a_etbl: Addr)
    (posture : InterruptStatus) (args minstk off : nat) (eh ehs : Z) (Nswitcher : namespace) :
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
    → is_Some (b_pcc + off%nat)%a
    → na_inv cerise_nais Nswitcher switcher_inv
    ⊢ switcher_static
    -∗ b_etbl ↦ₐ□ WCap true RX Global b_pcc e_pcc b_pcc
    -∗ b_etbl1 ↦ₐ□ WCap true RW Global b_cgp e_cgp b_cgp
    -∗ b_etbl ↦ₕ□{stackful} eh
    -∗ b_etbl ↦ₕ□{stackless} ehs
    -∗ a_etbl ↦ₐ□ WInt (encode_entry_point posture args minstk off)
    -∗ interp W C (WCap true RX Global b_pcc e_pcc b_pcc)
    -∗ interp W C (WCap true RW Global b_cgp e_cgp b_cgp)
    -∗ ot_switcher_prop W C (WCap true RO g_etbl b_etbl e_etbl a_etbl).
  Proof.
    intros b_etbl b_etbl1 e_etbl entries_etbl b_pcc e_pcc b_cgp e_cgp
      Ha_etbl Hargs Hentry.
    iIntros "#Hinv_switcher #Hswitcher_static #Hetbl_pcc #Hetbl_cgp #Hetbl_eh #Hetbl_ehs #Hetbl_entry #Hinterp_pcc #Hinterp_cgp".
    (* Only the low byte of the minimum stack size is encoded *)
    set (minstk8 := Z.to_nat (Z.of_nat minstk `mod` 256)).
    assert (Z.land (Z.of_nat minstk) 255 = Z.of_nat minstk8) as Hminstk8.
    { subst minstk8. change 255%Z with (Z.ones 8).
      rewrite Z.land_ones // Z2Nat.id //. apply Z.mod_pos_bound; lia. }
    assert (Z.of_nat minstk8 < 256)%Z as Hminstk8_lt.
    { subst minstk8. rewrite Z2Nat.id; [apply Z.mod_pos_bound; lia|]. apply Z.mod_pos_bound; lia. }
    iEval (rewrite encode_entry_point_minstk_land Hminstk8) in "Hetbl_entry".
    iExists _,_,_,_, b_pcc, e_pcc, b_cgp, e_cgp, args, minstk8, off, posture, eh, ehs.
    iFrame "#".
    iSplit ; first (by iPureIntro).
    iSplit.
    { iPureIntro. subst b_etbl e_etbl entries_etbl.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      pose proof (cmpt_exp_tbl_header_size C_cmpt) as H2.
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
      pose proof (cmpt_exp_tbl_header_size C_cmpt) as H2.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as H3.
      pose proof (cmpt_exp_tbl_entries_size C_cmpt) as H1.
      solve_addr.
    }
    iSplit; first (iPureIntro ; lia).
    iSplit; first (iPureIntro ; lia).
    iSplit; first (iPureIntro; exact Hentry).
    pose proof (cmpt_exp_tbl_pcc_size C_cmpt) as Htbl_pcc.
    pose proof (cmpt_exp_tbl_header_size C_cmpt) as Htbl_cgp.
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact (cmpt_exp_tbl_disjoint_from_shadow C_cmpt).
      - apply withinBounds_true_iff. subst entries_etbl e_etbl. solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact (cmpt_exp_tbl_disjoint_from_shadow C_cmpt).
      - apply withinBounds_true_iff. subst b_etbl entries_etbl e_etbl. solve_addr. }
    iSplit.
    { iPureIntro. eapply disjoint_from_shadow_not_in.
      - exact (cmpt_exp_tbl_disjoint_from_shadow C_cmpt).
      - apply withinBounds_true_iff. subst b_etbl entries_etbl e_etbl. solve_addr. }
    iSplit; first (iPureIntro; exact (cmpt_pcc_base_not_heap C_cmpt)).
    iSplit; first (iPureIntro; exact (cmpt_cgp_base_not_heap C_cmpt)).
    iSplit.
    { subst b_etbl1 b_etbl.
      replace (cmpt_exp_tbl_cgp C_cmpt ) with (cmpt_exp_tbl_pcc C_cmpt ^+ ExportTable_offset_cgp)%a; auto.
      pose proof (cmpt_exp_tbl_pcc_size C_cmpt).
      solve_addr.
    }
    iApply (fundamental_execute_entry_point
              with "Hinv_switcher Hswitcher_static Hinterp_pcc Hinterp_cgp").
    exact (cmpt_cgp_disjoint_from_heap C_cmpt).
  Qed.

End helpers_switcher_adequacy.
