From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Import switcher switcher_spec.

Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {heapg : heapGS Σ}
    {tframeg : TFRAMEG Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}.

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation TFRAME := (leibnizO nat).
  Notation WORLD := ( prodO (prodO STS_STD STS) TFRAME) .
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Lemma interp_has_rel (W : WORLD) (C : CmptName) (p : Perm) (g : Locality) (b e a a' : Addr) :
  (b <= a' < e)%a ->
  writeAllowed p = true →
  interp W C (WCap p g b e a) -∗
  (∃ p' φ', rel C a' p' (safeC φ')
            ∗ (▷ wcond φ' C interp)
            ∗ ⌜persistent_cond φ'⌝
            ∗ ⌜PermFlowsTo p p'⌝
  )%I.
  Proof.
    iIntros (Ha' Hp) "Hinterp".
    rewrite fixpoint_interp1_eq interp1_eq.
    pose proof (writeAllowed_nonO p Hp) as HpO.
    rewrite HpO.
    destruct (has_sreg_access p); first done.
    iDestruct "Hinterp" as "[Hinterp %Hg]".
    iDestruct (big_sepL_elem_of _ _ a' with "Hinterp") as "Hinterp".
    { by rewrite elem_of_finz_seq_between. }
    iDestruct "Hinterp" as (p' P') "(% & % & Hrel & _ & Hra & Hwa & _ & _)".
    eapply writeAllowed_flowsto in Hp; eauto.
    rewrite Hp.
    iExists _,_; iFrame "∗%".
  Qed.

  Lemma switcher_interp_expr (W : WORLD) (C : CmptName) (N : namespace) (rmap : Reg)
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher) -∗
    interp_expr interp rmap W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
    iIntros "#Hinv_switcher".
    iIntros "(#[%Hfull_rmap Hrmap_interp] & Hrmap & Hregion & Hworld & Htframe_frag & Hna)".
    rewrite /registers_pointsto /interp_conf.

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk d tstk_next)
           "(>Hmtdc & >%Hbounds & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Htframe_full & >%H_tstk_frame & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region; clear H0.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    (* --- Extract scratch registers ct2 ctp --- *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    rewrite delete_insert_delete.
    cbn in Hfull_rmap.
    assert (exists wcgp, rmap !! cgp = Some wcgp) as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wcra, rmap !! cra = Some wcra) as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap !! csp = Some wcsp) as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap !! ct1 = Some wct1) as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap !! cs0 = Some wcs0) as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap !! cs1 = Some wcs1) as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wct2, rmap !! ct2 = Some wct2) as [wct2 Hwct2] by (by specialize (Hfull_rmap ct2)).
    iDestruct (big_sepM_delete _ _ ct2 with "Hrmap") as "[Hct2 Hrmap]"; first by simplify_map_eq.

    Set Nested Proofs Allowed.



    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)
    iAssert (interp W C wcsp) as "#Hinterp_wcsp".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcs0) as "#Hinterp_wcs0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcs1) as "#Hinterp_wcs1".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcra) as "#Hinterp_wcra".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wcgp) as "#Hinterp_wcgp".
    { iApply "Hrmap_interp"; eauto; done. }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* ---- store csp cs0 ---- *)
    destruct (is_cap wcsp) eqn:His_cap_csp ; cycle 1.
    { (* if csp is not a stack, it fails *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg_not_cap with "[HPC Hi Hcsp Hcs0]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    destruct wcsp as [ | [ p_stk g_stk b_stk e_stk a_stk |] | |]; cbn in His_cap_csp; try congruence.
    clear His_cap_csp.

    destruct (decide (b_stk <= a_stk))%a as [Hstk_ba|Hstk_ba]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[HPC Hi Hcsp Hcs0]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    destruct (decide (canStore p_stk wcs0 = true))%a as [Hstk_store_cs0|Hstk_store_cs0]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hcsp Hcs0]")
      ; try iFrame
      ; try solve_pure.
      { by destruct ( canStore p_stk wcs0 ); auto. }
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    pose proof ( canStore_writeAllowed p_stk wcs0 Hstk_store_cs0 ) as Hp_stk_wa.
    destruct (decide ((a_stk) < e_stk))%a as [Hstk_a|Hstk_a]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[HPC Hi Hcsp Hcs0]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }


  iDestruct (writeAllowed_valid_cap with "Hinterp_wcsp") as "%Hstk_in_region"; auto.
  assert ( ∃ ρ_a_stk, std W !! a_stk = Some ρ_a_stk ∧ ρ_a_stk ≠ Revoked) as ( ρ_a_stk & Hρ_a_stk & Hρ_a_stk_not_revoked).
  {
    rewrite Forall_lookup in Hstk_in_region.
    assert ( a_stk ∈ finz.seq_between b_stk e_stk) as H_a_stk.
    { apply elem_of_finz_seq_between; solve_addr. }
    rewrite elem_of_list_lookup in H_a_stk.
    destruct H_a_stk as [ka Hka].
    apply Hstk_in_region in Hka.
    done.
  }

  iDestruct (interp_has_rel _ _ _ _ _ _ _ a_stk with "Hinterp_wcsp")
    as (p_a_stk φ_a_stk) "#(Hrel_a_stk & Hφ_a_stk_wcond & %Hpers_φ_a_stk & %Hflow_p_a_stk)".
  { solve_addr. }
  { done. }
  iDestruct (region_open _ _ _ _ _ ρ_a_stk with "[$Hrel_a_stk $Hworld $Hregion]")
    as (wastk) "(Hregion & Hworld & Hsts_std_a_stk & Ha_stk & _ & #Hmono_φ_a_stk & Hφ_a_stk)"; eauto.
  { destruct ρ_a_stk; naive_solver. }

  iInstr_lookup "Hcode" as "Hi" "Hcode".
  wp_instr.
  iApply (wp_store_success_reg _ _ _ _ _ _ _ _ csp cs0 with "[$HPC Hi Hcs0 Hcsp Ha_stk]")
  ; try iFrame
  ; try solve_pure.
  { rewrite /withinBounds; solve_addr. }
  iNext; iIntros "(HPC & Hi & Hcso0 & Hcsp & Ha_stk)".
  iDestruct ("Hcode" with "Hi") as "Hcode".
  wp_pure.
  iDestruct (region_close
              with "[$Hsts_std_a_stk $Hregion $Ha_stk Hmono_φ_a_stk $Hrel_a_stk]")
    as "Hregion".
  { intros.
    rewrite /persistent_cond in Hpers_φ_a_stk.
    specialize (Hpers_φ_a_stk Wv); apply _.
  }
  { destruct ρ_a_stk; naive_solver. }
  { iSplit.
    + iPureIntro; by eapply writeAllowed_nonO, writeAllowed_flowsto.
    + admit. (* TODO see how it's done in the FTLR *)
  }

  (* ---- lea csp 1 ---- *)
  iInstr "Hcode".
  { transitivity (Some (a_stk ^+ 1%Z)%a); auto;solve_addr. }



  (* ---- store csp cs1 ---- *)
  destruct (decide (canStore p_stk wcs1 = true))%a as [Hstk_store_cs1|Hstk_store_cs1]; cycle 1.
  {
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_fail_reg_perm with "[HPC Hi Hcsp Hcs1]")
    ; try iFrame
    ; try solve_pure.
    { by destruct ( canStore p_stk wcs1 ); auto. }
    iNext; iIntros "_".
    wp_pure; wp_end ; by iIntros (?).
  }
  pose proof ( canStore_writeAllowed p_stk wcs1 Hstk_store_cs1 ) as Hp_stk_wa1.
  destruct (decide ((a_stk ^+1)%a < e_stk))%a as [Hstk_a1|Hstk_a1]; cycle 1.
  {
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_fail_reg with "[HPC Hi Hcsp Hcs1]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "_".
    wp_pure; wp_end ; by iIntros (?).
  }
  set (a_stk1 := (a_stk ^+ 1)%a).
  assert ( ∃ ρ_a_stk1, std W !! a_stk1 = Some ρ_a_stk1 ∧ ρ_a_stk1 ≠ Revoked) as ( ρ_a_stk1 & Hρ_a_stk1 & Hρ_a_stk1_not_revoked).
  {
    rewrite Forall_lookup in Hstk_in_region.
    assert ( a_stk1 ∈ finz.seq_between b_stk e_stk) as H_a_stk1.
    { apply elem_of_finz_seq_between; subst a_stk1 ; solve_addr. }
    rewrite elem_of_list_lookup in H_a_stk1.
    destruct H_a_stk1 as [ka Hka].
    apply Hstk_in_region in Hka.
    done.
  }

  iDestruct (interp_has_rel _ _ _ _ _ _ _ (a_stk ^+ 1)%a with "Hinterp_wcsp")
    as (p_a_stk1 φ_a_stk1)
         "#(Hrel_a_stk1 & Hφ_a_stk_wcond0 & %Hpers_φ_a_stk1 & %Hflow_p_a_stk1)".
  { solve_addr. }
  { done. }
  iDestruct (region_open _ _ _ _ _ ρ_a_stk1 with "[$Hrel_a_stk1 $Hworld $Hregion]")
    as (wastk1) "(Hregion & Hworld & Hsts_std_a_stk1 & Ha_stk1 & _ & #Hmono_φ_a_stk1 & Hφ_a_stk1)"; eauto.
  { destruct ρ_a_stk1; naive_solver. }

  iInstr_lookup "Hcode" as "Hi" "Hcode".
  wp_instr.
  iApply (wp_store_success_reg _ _ _ _ _ _ _ _ csp cs1 with "[$HPC Hi Hcs1 Hcsp Ha_stk1]")
  ; try iFrame
  ; try solve_pure.
  { rewrite /withinBounds; solve_addr. }
  iNext; iIntros "(HPC & Hi & Hcs0 & Hcsp & Ha_stk1)".
  iDestruct ("Hcode" with "Hi") as "Hcode".
  wp_pure.
  iDestruct (region_close
              with "[$Hsts_std_a_stk1 $Hregion $Ha_stk1 Hmono_φ_a_stk1 $Hrel_a_stk1]")
    as "Hregion".
  { intros.
    rewrite /persistent_cond in Hpers_φ_a_stk1.
    specialize (Hpers_φ_a_stk1 Wv); apply _.
  }
  { destruct ρ_a_stk1; naive_solver. }
  { iSplit.
    + iPureIntro; by eapply writeAllowed_nonO, writeAllowed_flowsto.
    + admit. (* TODO see how it's done in the FTLR *)
  }
  (* ---- lea csp 1 ---- *)
  iInstr "Hcode".
  { transitivity (Some (a_stk ^+ 2%Z)%a); auto;solve_addr. }


  Qed.


  Lemma switcher_interp (W : WORLD) (C : CmptName) (N : namespace)
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr) (ot_switcher : OType) :
    na_inv logrel_nais N (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher) -∗
    interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
    iIntros "#Hswitcher_inv".
    rewrite fixpoint_interp1_eq /=.
    iModIntro.
    rewrite /enter_cond.
    iIntros (reg W') "_".
    iSplitL ; iNext ; iApply switcher_interp_expr; auto.
  Qed.

  Lemma future_priv_mono_interp_switcher (C : CmptName) (Nswitcher : namespace)
    (b_switcher e_switcher a_switcher_cc b_tstk e_tstk : Addr) (ot_switcher : OType) :
    na_inv logrel_nais Nswitcher (switcher_inv b_switcher e_switcher a_switcher_cc b_tstk e_tstk ot_switcher) -∗
    future_priv_mono C interpC (WSentry XSRW_ Local b_switcher e_switcher a_switcher_cc).
  Proof.
    iIntros "#Hswitcher_inv".
    iModIntro.
    iIntros (W W' Hrelated) "_".
    iApply switcher_interp; auto.
  Qed.


End Switcher.
