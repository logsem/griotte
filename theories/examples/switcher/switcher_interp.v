From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From cap_machine Require Import logrel fundamental interp_weakening addr_reg_sample rules proofmode.
From cap_machine Require Import multiple_updates region_invariants_revocation region_invariants_allocation.
From cap_machine Require Export switcher switcher_preamble.

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

  Lemma writeLocalAllowed_valid_cap (W : WORLD) (C : CmptName) p g b e a':
    isWL p = true →
    interp W C (WCap p g b e a') -∗
    ⌜Forall (fun a => std W !! a = Some Temporary ) (finz.seq_between b e)⌝.
  Proof.
    iIntros (Hwa) "Hinterp".
    rewrite Forall_forall.
    iIntros (a Ha).
    apply elem_of_finz_seq_between in Ha.
    rewrite /interp; cbn.
    rewrite fixpoint_interp1_eq interp1_eq; cbn.
    replace (isO p) with false.
    2: { eapply isWL_nonO in Hwa ;done. }
    destruct (has_sreg_access p) eqn:HnXSR; auto.
    iDestruct "Hinterp" as "[Hinterp %Hloc]".
    iDestruct (extract_from_region_inv with "Hinterp")
             as (p' P' Hfl' Hpers') "(Hrel & Hzcond & Hrcond & Hwcond & HmonoR & %Hstate)";eauto.
    iPureIntro.
    destruct (isWL p); simplify_eq.
    by rewrite /region_state_pwl in Hstate.
  Qed.

  Lemma wp_store_interp (E : coPset) (W : WORLD) (C : CmptName) (rsrc rdst : RegName)
    (pc_p : Perm) (pc_g : Locality) (pc_b pc_e pc_a pc_a' : Addr)
    (p : Perm) (g : Locality) (b e a a' : Addr)
    (wi wsrc : Word)
    :
    decodeInstrW wi = Store rdst (inr rsrc) →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

     {{{ interp W C wsrc
           ∗ interp W C (WCap p g b e a')
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
     }}}
       Instr Executable @ E
       {{{ retv, RET retv;
           ⌜ retv = FailedV ⌝ ∨
          ( ⌜ retv = NextIV ⌝
           ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
           ∗ pc_a ↦ₐ wi
           ∗ rsrc ↦ᵣ wsrc
           ∗ rdst ↦ᵣ WCap p g b e a
           ∗ region W C
           ∗ sts_full_world W C
           ∗ ⌜ canStore p wsrc = true ⌝
           ∗ ⌜(b <= a < e)%a ⌝
          )
       }}}.
  Proof.
    iIntros (Hdecode_wi Hcorrect_pc Hpca' φ)
      "(#Hinterp_src & #Hinterp_dst & HPC & Hi & Hsrc & Hdst & Hregion & Hworld)".
    iIntros "Hφ".

    destruct (decide (canStore p wsrc = true))%a as [Hstore_src|Hstore_src]; cycle 1.
    {
      iApply (wp_store_fail_reg_perm with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { by destruct ( canStore p wsrc ); auto. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    pose proof ( canStore_writeAllowed p wsrc Hstore_src ) as Hp_stk_wa.
    destruct (decide (b <= a))%a as [Hba|Hba]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }
    destruct (decide (a < e))%a as [Hae|Hae]; cycle 1.
    {
      iApply (wp_store_fail_reg with "[HPC Hi Hdst Hsrc]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iNext; iIntros "_".
      iApply "Hφ"; by iLeft.
    }

    iDestruct (writeAllowed_valid_cap with "Hinterp_dst") as "%Hdst_in_region"; auto.
    assert ( ∃ ρ, std W !! a = Some ρ ∧ ρ ≠ Revoked) as ( ρ & Hρ & Hρ_not_revoked).
    {
      rewrite Forall_lookup in Hdst_in_region.
      assert ( a ∈ finz.seq_between b e) as Ha.
      { apply elem_of_finz_seq_between; solve_addr. }
      rewrite elem_of_list_lookup in Ha.
      destruct Ha as [ka Hka].
      apply Hdst_in_region in Hka.
      done.
    }

    iDestruct (interp_has_rel _ _ _ _ _ _ _ a with "Hinterp_dst")
      as (p_a φ_a)
           "#(Hrel_a & Hφ_a_wcond & %Hpers_φ_a & %Hflow_p_a)".
    { solve_addr. }
    { done. }
    iDestruct (region_open _ _ _ _ _ ρ with "[$Hrel_a $Hworld $Hregion]")
      as (wastk) "(Hregion & Hworld & Hsts_std_a & Ha & _ & #Hmono_φ_a & Hφ_a)"; eauto.
    { destruct ρ; naive_solver. }

    iApply (wp_store_success_reg _ _ _ _ _ _ _ _ rdst rsrc with "[$HPC Hi Hsrc Hdst Ha]")
    ; try iFrame
    ; try solve_pure.
    { rewrite /withinBounds; solve_addr. }
    iNext; iIntros "(HPC & Hi & Hsrc & Hdst & Ha)".
    iDestruct (region_close
                with "[$Hsts_std_a $Hregion $Ha Hmono_φ_a $Hrel_a]")
      as "Hregion".
    { intros.
      rewrite /persistent_cond in Hpers_φ_a.
      specialize (Hpers_φ_a Wv); apply _.
    }
    { destruct ρ; naive_solver. }
    { iSplit.
      + iPureIntro; by eapply writeAllowed_nonO, writeAllowed_flowsto.
      + admit. (* TODO see how it's done in the FTLR *)
    }

    iApply "Hφ"; iRight; iFrame "∗%".
    iSplit; first done.
    iPureIntro; solve_addr.
  Admitted.

  Lemma wp_unseal_unknown E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 wsealr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ wsealr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ psr gsr bsr esr asr wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ r1 ↦ᵣ wsealr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealr = (WSealRange psr gsr bsr esr asr) ⌝ ∗ ⌜ permit_unseal psr = true ⌝
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists p, g, b, e, a, sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.

  Lemma wp_unseal_unknown_sealed E pc_p pc_g pc_b pc_e pc_a pc_a' wi r1 r2 psr gsr bsr esr asr wsealed  :
    decodeInstrW wi = UnSeal r2 r1 r2 →
    isCorrectPC (WCap pc_p pc_g pc_b pc_e pc_a) →
    (pc_a + 1)%a = Some pc_a' →
    permit_unseal psr = true ->
    (bsr <= asr < esr)%ot ->

    {{{  PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a
          ∗ pc_a ↦ₐ wi
          ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
          ∗ r2 ↦ᵣ wsealed
    }}}
      Instr Executable @ E
      {{{ retv, RET retv;
          ⌜ retv = FailedV ⌝
          ∨ ∃ wsb,
              ⌜ retv = NextIV ⌝
              ∗ PC ↦ᵣ WCap pc_p pc_g pc_b pc_e pc_a'
              ∗ pc_a ↦ₐ wi
              ∗ r1 ↦ᵣ WSealRange psr gsr bsr esr asr
              ∗ r2 ↦ᵣ WSealable wsb
              ∗ ⌜ wsealed = WSealed asr wsb ⌝
      }}}.
  Proof.
    iIntros (Hinstr Hvpc Hpc_a' Hpsr Hsr ϕ) "(HPC & Hpc_a & Hr1 & Hr2) Hφ".

    iDestruct (map_of_regs_3 with "HPC Hr1 Hr2") as "[Hmap (%&%&%)]".
    iApply (wp_UnSeal with "[$Hmap Hpc_a]"); eauto; simplify_map_eq; eauto.
    by unfold regs_of; rewrite !dom_insert; set_solver+.
    iNext. iIntros (regs' retv) "(#Hspec & Hpc_a & Hmap)". iDestruct "Hspec" as %Hspec.

    destruct Hspec as [ | ]; iApply "Hφ"; [iRight | by iLeft].
    rewrite lookup_insert_ne // lookup_insert  in H2.
    rewrite lookup_insert_ne // lookup_insert_ne // lookup_insert in H3.
    apply incrementPC_Some_inv in H6.
    destruct H6 as ( ppc & gpc & bpc & epc & apc & apc' & HPC & Hapc' & ->).
    rewrite lookup_insert_ne // lookup_insert in HPC.
    simplify_eq.
    iExists sb.
    rewrite (insert_commute _ _ PC) //.
    rewrite (insert_commute _ _ r1) //.
    rewrite !insert_insert.
    iDestruct (big_sepM_insert with "Hmap") as "[HPC Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr1 Hmap]"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "Hmap") as "[Hr2 Hmap]"; first by simplify_map_eq.
    iFrame; done.
  Qed.



  Set Nested Proofs Allowed.
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
    assert (exists wctp, rmap !! ctp = Some wctp) as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.

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
    iAssert (interp W C wct1) as "#Hinterp_wct1".
    { iApply "Hrmap_interp"; eauto; done. }

    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
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

    (* ---- store csp cs0 ---- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[HPC Hi Hcsp Hcs0 $Hregion $Hworld Hinterp_wcsp $Hinterp_wcs0]")
    ; try iFrame "∗#"
    ; try solve_pure.
    iNext
    ; iIntros (retv) "[->|(-> & HPC & Hi & Hcs0 & Hcsp & Hregion & Hworld & %Hcanstore_cs0 & [%Hstk_ba0 %Hstk_a0e] )]"
    ; wp_pure ; first (wp_end ; by iIntros (?)).
    iDestruct ("Hcode" with "Hi") as "Hcode".

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 1%Z)%a); auto;solve_addr. }

    (* ---- store csp cs1 ---- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[HPC Hi Hcsp Hcs1 $Hregion $Hworld Hinterp_wcsp $Hinterp_wcs1]")
    ; try iFrame "∗#"
    ; try solve_pure.
    iNext
    ; iIntros (retv) "[->|(-> & HPC & Hi & Hcs1 & Hcsp & Hregion & Hworld & %Hcanstore_cs1 & [_ %Hstk_a1e] )]"
    ; wp_pure ; first (wp_end ; by iIntros (?)).
    iDestruct ("Hcode" with "Hi") as "Hcode".

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 2%Z)%a); auto;solve_addr. }

    (* ---- store csp cra ---- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[HPC Hi Hcsp Hcra $Hregion $Hworld Hinterp_wcsp $Hinterp_wcra]")
    ; try iFrame "∗#"
    ; try solve_pure.
    iNext
    ; iIntros (retv) "[->|(-> & HPC & Hi & Hcra & Hcsp & Hregion & Hworld & %Hcanstore_cra & [_ %Hstk_a2e] )]"
    ; wp_pure ; first (wp_end ; by iIntros (?)).
    iDestruct ("Hcode" with "Hi") as "Hcode".

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 3%Z)%a); auto;solve_addr. }

    (* ---- store csp cgp ---- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[HPC Hi Hcsp Hcgp $Hregion $Hworld Hinterp_wcsp $Hinterp_wcgp]")
    ; try iFrame "∗#"
    ; try solve_pure.
    iNext
    ; iIntros (retv) "[->|(-> & HPC & Hi & Hcgp & Hcsp & Hregion & Hworld & %Hcanstore_cgp & [_ %Hstk_a3e] )]"
    ; wp_pure ; first (wp_end ; by iIntros (?)).
    iDestruct ("Hcode" with "Hi") as "Hcode".

    (* ---- lea csp 1 ---- *)
    iInstr "Hcode".
    { transitivity (Some (a_stk ^+ 4%Z)%a); auto;solve_addr. }

    (* --- getp ct2 csp --- *)
    iInstr "Hcode".
    (* --- mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".
    (* --- sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    destruct ( decide (p_stk = RWL)) as [-> |Hpstk]; cycle 1.
    { (* pstk is not RWL - will fail *)
      assert ( (encodePerm p_stk - encodePerm RWL)%Z ≠ 0%Z ) as Heq.
      { intro Hcontra.
        apply Hpstk.
        assert ( encodePerm p_stk = encodePerm RWL )%Z by lia.
        by apply encodePerm_inj in H1.
      }
      iInstr "Hcode".
      { congruence. }
      iInstr "Hcode".
      wp_end ; by iIntros (?).
    }
    replace ((encodePerm RWL - encodePerm RWL)%Z) with 0%Z by lia.
    (* --- jnz 2 ct2 --- *)
    iInstr "Hcode".
    (* --- jmp 2 --- *)
    iInstr "Hcode".

    (* --- getl ct2 csp --- *)
    iInstr "Hcode".
    (* --- mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".
    (* --- sub ct2 ct2 ctp --- *)
    iInstr "Hcode".
    destruct ( decide (g_stk = Local)) as [-> |Hgstk]; cycle 1.
    { (* pstk is not RWL - will fail *)
      assert ( (encodeLoc g_stk - encodeLoc Local)%Z ≠ 0%Z ) as Heq.
      { intro Hcontra.
        apply Hgstk.
        assert ( encodeLoc g_stk = encodeLoc Local )%Z by lia.
        by apply encodeLoc_inj in H1.
      }
      iInstr "Hcode".
      { congruence. }
      iInstr "Hcode".
      wp_end ; by iIntros (?).
    }
    replace ((encodeLoc Local - encodeLoc Local)%Z) with 0%Z by lia.
    (* --- jnz 2 ct2 --- *)
    iInstr "Hcode".
    (* --- jmp 2 --- *)
    iInstr "Hcode".


    (* --- readsr ct2 mtdc --- *)
    iInstr "Hcode".

    destruct (decide ((a_tstk ^+ 1) < e_tstk))%a as [Htstk_ae|Htstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    destruct (decide (b_tstk <= a_tstk))%a as [Htstk_ba|Htstk_ba]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    iAssert (⌜ exists tstk_a1 tstk_next', (tstk_next = tstk_a1 :: tstk_next')⌝)%I
      as %(tstk_a1 & tstk_next' & ->).
    { iEval (rewrite /region_pointsto) in "Htstk".
      iDestruct (big_sepL2_length with "Htstk") as %Hlen_tstk.
      iPureIntro.
      assert (0 < length (finz.seq_between (a_tstk ^+ 1)%a e_tstk)) as Hlen_tstk_ae.
      { rewrite finz_seq_between_length.
        (* assert (a_tstk^+1 < e_tstk)%a by solve_addr. *)
        assert (a_tstk < e_tstk)%a by solve_addr.
        (* rewrite finz_dist_S; last solve_addr. *)
        rewrite finz_dist_S; last solve_addr; lia.
      }
      destruct tstk_next as [|stk_a1 tstk_next]; first (cbn in Hlen_tstk; lia).
      exists stk_a1, tstk_next; done.
    }
    iDestruct (region_pointsto_cons with "Htstk") as "[Ha1_tstk Htstk]".
    { transitivity (Some (a_tstk ^+ 2)%a); auto; solve_addr. }
    { solve_addr. }

    (* Lea ct2 1%Z; *)
    iInstr "Hcode".
    {  transitivity (Some (a_tstk ^+1)%a); solve_addr. }

    (* Store ct2 csp; *)
    iInstr "Hcode".
    { rewrite /withinBounds andb_true_iff; solve_addr. }

    (* WriteSR mtdc ct2; *)
    iInstr "Hcode".

    (* Zero out the callee's stack frame *)
    (* GetE cs0 csp; *)
    iInstr "Hcode".

    (* GetA cs1 csp; *)
    iInstr "Hcode".

    (* Subseg csp cs1 cs0 *)
    iInstr "Hcode" with "Hlc".
    { rewrite /isWithin andb_true_iff; solve_addr. }

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 1 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcont"; iHide "Hcont" as hcont.

    iDestruct (writeLocalAllowed_valid_cap with "Hinterp_wcsp") as "%Hstk_in_region"; auto.
    opose proof ( extract_temps_split_world W (finz.seq_between (a_stk ^+4)%a e_stk)) as
      (ltemp_unknown & HNoDup_unk & W_temps).
    { apply finz_seq_between_NoDup. }
    { rewrite !Forall_lookup in Hstk_in_region |- *.
      intros k a Hka.
      apply elem_of_list_lookup_2 in Hka.
      assert (a ∈ finz.seq_between b_stk e_stk) as Hka'.
      { rewrite !elem_of_finz_seq_between in Hka |- *; solve_addr. }
      apply elem_of_list_lookup_1 in Hka'.
      destruct Hka' as [k' Hka'].
      eapply Hstk_in_region; eauto.
    }
    set ( Wtemp := (ltemp_unknown ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ).
    (* 1) revoke the world *)

    iMod ( monotone_revoke_keep _ C Wtemp with "[$Hworld $Hregion]") as "(Hworld & Hregion & Htemp)".
    { by cbn. }
    { iPureIntro.
      intros k' a' Hk'; cbn.
      apply W_temps.
      apply elem_of_list_lookup.
      by eexists.
    }
    rewrite revoke_resources_later
    ; iMod (lc_fupd_elim_later with "Hlc Htemp") as "Htemp".
    subst Wtemp.
    iDestruct (big_sepL_app with "Htemp") as "[Htemp_unknown Htemp_stk]".
    iDestruct (big_sepL_sep with "Htemp_stk") as "[Htemp_stk Hstk_revoked]".
    iDestruct (region_addrs_exists with "Htemp_stk") as (lp) "Htemp_stk".
    iDestruct (region_addrs_exists2 with "Htemp_stk") as (lφ) "[%Hlen_lφ Htemp_stk]".
    iDestruct (big_sepL2_sep with "Htemp_stk") as "[Hpers_stk_φ Htemp_stk]".
    iDestruct (big_sepL2_sep with "Htemp_stk") as "[Htemp_stk Hrel_stk]".
    iDestruct (region_addrs_exists2 with "Htemp_stk") as (lw) "[%Hlen_lw Htemp_stk]".
    iDestruct (big_sepL2_sep with "Htemp_stk") as "[Hlp_notO Htemp_stk]".
    iDestruct (big_sepL2_sep with "Htemp_stk") as "[Hstk Hmono_stk]".
    rewrite (big_sepL2_zip_snd_2 _ (zip lp lφ) lw (λ a w, a ↦ₐ w)%I); last by rewrite Hlen_lw.


    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hcs0 $Hcs1 $Hcode $Hstk]"); eauto.
    { solve_addr. }
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".

    iDestruct (sts_update_frm _ _ (W0.2 + 1) with "Hworld") as ">Hworld".
    iMod (update_region_revoked_temp_pwl_multiple ⊤ _ _
                 (finz.seq_between (a_stk ^+ 4)%a e_stk) (region_addrs_zeroes (a_stk ^+ 4)%a e_stk) RWL interpC
                with "[$] [$] [Hstk Hstk_revoked Hpers_stk_φ Hrel_stk Hlp_notO Hmono_stk]") as "[Hregion Hworld]".
    { done. }
    { done. }
    { apply finz_seq_between_NoDup. }
    { admit. (* NOTE easy, but tedious *) }
    iMod (monotone_close_list_region W _ _ ltemp_unknown
                with "[] [$Hworld $Hregion Htemp_unknown]") as "[Hworld Hregion]".
    { admit. (* should be OK *) }
    { iDestruct (big_sepL_sep with "Htemp_unknown") as "[Htemp_unknown _]".
      iFrame.
    }
    clear Hlen_lφ Hlen_lw.

    iMod ( sts_alloc_loc _ C true frame_rel_pub frame_rel_pub frame_rel_priv with "Hworld")
      as "(Hworld & %Hfresh_ι & %Hfresh_ι' & Hsts_loc_ι & #Hsts_rel_ι)".
    rewrite -!/(frame_W (close_list ltemp_unknown (std_update_multiple (revoke W) (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary))).

    set (W1 := (close_list ltemp_unknown (std_update_multiple (revoke W) (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary))).
    set (W2 := frame_W W1).
    set (ι := fresh_cus_name W1).

    iDestruct (region_monotone _ _ W2 with "Hregion") as "Hregion".
    { subst W2. rewrite /frame_W //=. }
    { apply frame_W_related_sts_pub_world. }

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    focus_block 2 "Hcode" as a_unseal Ha_unseal "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* GetB cs1 PC *)
    iInstr "Hcode".

    (* GetA cs0 PC *)
    iInstr "Hcode".

    (* Sub cs1 cs1 cs0 *)
    iInstr "Hcode".
    (* Mov cs0 PC *)
    iInstr "Hcode".
    (* Lea cs0 cs1 *)
    assert ( (a_unseal ^+ 3 + (b_switcher - (a_unseal ^+ 1)))%a = Some ( (b_switcher ^+ 2%Z)%a ))
    as ?.
    { solve_addr+H0 Ha_unseal H. }
    iInstr "Hcode".

    (* Lea cs0 (-2)%Z *)
    iInstr "Hcode" with "Hlc".
    { transitivity (Some b_switcher); solve_addr+H0 Ha_unseal H. }

    (* Load cs0 cs0 *)
    iInstr "Hcode" with "Hlc".
    iEval (cbn) in "Hcs0".

    (* UnSeal ct1 cs0 ct1 *)
    (* subst Hwct1_caller. *)

    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed with "[HPC Hi Hct1 Hcs0 ]")
    ; try iFrame "∗"
    ; try solve_pure.
    { done. }
    { solve_addr. }
    iNext ; iIntros (retv) "[->|Hret]" ; first (wp_pure ; wp_end ; by iIntros (?)).
    iDestruct "Hret" as (w_entry_point) "(-> & HPC & Hi & Hcs0 & Hct1 & ->)".
    iDestruct ("Hcode" with "Hi") as "Hcode".
    wp_pure.

    (* iInstr "Hcode". *)
    (* { done. (* TODO solve_pure *) } *)
    (* { apply withinBounds_true_iff; solve_addr. (* TODO solve_pure *) } *)
    (* rewrite Heq_entry_point. *)

    iDestruct ( interp_monotone_sd W W2 with "[] [$Hinterp_wct1]" ) as "Hinterp_wct1'".
    { iPureIntro. subst W2 W1.
      admit. (* TODO should be fine *)  }
    iEval (rewrite fixpoint_interp1_eq /= /interp_sb) in "Hinterp_wct1'".
    iDestruct "Hinterp_wct1'"
      as (Pct1 Hpers_Pct1) "(HmonoReq & Hseal_pred_Pct1 & HPct1')".
    rewrite -bi.later_sep.
    iDestruct "Hlc" as "[Hlc Hlc']".
    assert (Persistent (Pct1 W2 C (WSealable w_entry_point))) as Hpers_Pct1'
    by (by specialize (Hpers_Pct1 (W2,C,(WSealable w_entry_point)))).
    assert (Persistent (Pct1 W2 C (borrow (WSealable w_entry_point)))) as Hpers_Pct1''
    by (by specialize (Hpers_Pct1 (W2,C,(borrow (WSealable w_entry_point))))).
    iMod (lc_fupd_elim_later with "Hlc' HPct1'") as "#[HPct1 HPct1_borrow]".
    clear Hpers_Pct1' Hpers_Pct1''; iClear "HPct1'".
    iDestruct (seal_pred_agree with "Hseal_pred_Pct1 Hp_ot_switcher") as "Hot_switcher_agree_later".
    iSpecialize ("Hot_switcher_agree_later" $! (W2,C,WSealable w_entry_point)).
    iMod (lc_fupd_elim_later with "Hlc Hot_switcher_agree_later") as "#Hot_switcher_agree".
    iClear "Hot_switcher_agree_later".

    rewrite /ot_switcher_prop.
    iEval (rewrite /safeC /=) in "Hot_switcher_agree".
    iRewrite "Hot_switcher_agree" in "HPct1".
    rewrite /ot_switcher_propC /ot_switcher_prop.
    iDestruct "HPct1" as (g_tbl b_tbl e_tbl a_tbl
                         bpcc epcc bcgp ecgp nargs off_entry
                            Heq_entry_point Hatbl Hbtbl Hbtbl1 Hnargs)
                           "(#Hinv_pcc_B & #Hinv_cgp_B & #Hinv_entry_B_f & #Hjmp_callee_pc)".
    iClear "Hot_switcher_agree".
    cbn in Heq_entry_point.
    rewrite !Heq_entry_point.


    (* Load cs0 ct1 *)
    wp_instr.
    iInv "Hinv_entry_B_f" as ">Hatbl" "Hcls_atbl".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr. }
    iEval (cbn) in "Hcs0".
    iMod ("Hcls_atbl" with "Hatbl") as "_"; iModIntro.
    wp_pure.

    (* LAnd ct2 cs0 7%Z *)
    iInstr "Hcode".

    (* ShiftR cs0 cs0 3%Z *)
    iInstr "Hcode".

    replace ( (Z.land (encode_entry_point nargs off_entry) 7)) with nargs by admit.
    replace ( (encode_entry_point nargs off_entry ≫ 3)%Z) with off_entry by admit.
    (* TODO unclear why the above are true: should be properties of encode_entry_point *)
    (* GetB cgp ct1 *)
    iInstr "Hcode".

    (* GetA cs1 ct1 *)
    iInstr "Hcode".

    (* Sub cs1 cgp cs1 *)
    iInstr "Hcode".

    (* Lea ct1 cs1 *)
    iInstr "Hcode".
    { transitivity (Some b_tbl); solve_addr+Hatbl. }

    (* Load cra ct1 *)
    wp_instr.
    iInv "Hinv_pcc_B" as ">Hbtbl" "Hcls_btbl".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr+Hatbl. }
    iEval (cbn) in "Hcra".
    iMod ("Hcls_btbl" with "Hbtbl") as "_"; iModIntro.
    wp_pure.

    (* Lea ct1 1%Z *)
    iInstr "Hcode".
    { transitivity (Some (b_tbl ^+ 1)%a); solve_addr+Hbtbl1. }

    (* Load cgp ct1 *)
    wp_instr.
    iInv "Hinv_cgp_B" as ">Hbtbl1" "Hcls_btbl1".
    iInstr "Hcode".
    { split ; first solve_pure.
      rewrite /withinBounds; solve_addr+Hatbl Hbtbl1. }
    iEval (cbn) in "Hcra".
    iMod ("Hcls_btbl1" with "Hbtbl1") as "_"; iModIntro.
    wp_pure.

    (* Lea cra cs0 *)
    iInstr "Hcode".
    { transitivity (Some (bpcc ^+ off_entry)%a); last solve_addr. admit. }
    (* TODO actually, it's fine if the offset fail, the machine fails...
       we just need not to use iInstr, but instead manually choose the wp rule
     *)

    (* Add ct2 ct2 1%Z *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 3 "Hcode" as a_clear_pre_reg1 Ha_clear_pre_reg1 "Hcode" "Hcont"; iHide "Hcont" as hcont.

    assert (exists wca0, rmap !! ca0 = Some wca0) as [wca0 Hwca0] by (by specialize (Hfull_rmap ca0)).
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert (exists wca1, rmap !! ca1 = Some wca1) as [wca1 Hwca1] by (by specialize (Hfull_rmap ca1)).
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert (exists wca2, rmap !! ca2 = Some wca2) as [wca2 Hwca2] by (by specialize (Hfull_rmap ca2)).
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert (exists wca3, rmap !! ca3 = Some wca3) as [wca3 Hwca3] by (by specialize (Hfull_rmap ca3)).
    iDestruct (big_sepM_delete _ _ ca3 with "Hrmap") as "[Hca3 Hrmap]"; first by simplify_map_eq.
    assert (exists wca4, rmap !! ca4 = Some wca4) as [wca4 Hwca4] by (by specialize (Hfull_rmap ca4)).
    iDestruct (big_sepM_delete _ _ ca4 with "Hrmap") as "[Hca4 Hrmap]"; first by simplify_map_eq.
    assert (exists wca5, rmap !! ca5 = Some wca5) as [wca5 Hwca5] by (by specialize (Hfull_rmap ca5)).
    iDestruct (big_sepM_delete _ _ ca5 with "Hrmap") as "[Hca5 Hrmap]"; first by simplify_map_eq.
    assert (exists wct0, rmap !! ct0 = Some wct0) as [wct0 Hwct0] by (by specialize (Hfull_rmap ct0)).
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.

    iDestruct (map_of_regs_4 with "[$Hca0] [$Hca1] [$Hca2] [$Hca3] ") as "[Hargmap _]".
    iDestruct (big_sepM_insert with "[$Hargmap $Hca4]") as "Hargmap"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "[$Hargmap $Hca5]") as "Hargmap"; first by simplify_map_eq.
    iDestruct (big_sepM_insert with "[$Hargmap $Hct0]") as "Hargmap"; first by simplify_map_eq.
    set ( argmap := <[ct0:=wct0]> (<[ca5:=wca5]> (<[ca4:=wca4]> (<[ca0:=wca0]> (<[ca1:=wca1]> (<[ca2:=wca2]> (<[ca3:=wca3]> ∅)))))) ).
    iAssert ( [∗ map] r↦w ∈ argmap, r ↦ᵣ w ∗ interp W2 C w)%I with "[Hargmap]" as "Hargmap".
    { admit. (* NOTE easy enough *) }

    iApply (clear_registers_pre_call_skip_spec with "[- $HPC $Hargmap $Hct2 $Hcode]"); try solve_pure.
    { set_solver. }
    { solve_addr. }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hct2 & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 4 "Hcode" as a_clear_pre_reg2 Ha_clear_pre_reg2 "Hcode" "Hcont"; iHide "Hcont" as hcont.

    iDestruct (big_sepM_insert _ _ ctp with "[$Hrmap $Hctp]") as "Hrmap"; first by simplify_map_eq.
    (* rewrite insert_delete_insert. *)
    repeat (try (rewrite -delete_insert_ne ; last done)); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ ct2 with "[$Hrmap $Hct2]") as "Hrmap"; first by simplify_map_eq.
    repeat (try (rewrite -delete_insert_ne ; last done)); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ ct1 with "[$Hrmap $Hct1]") as "Hrmap"; first by simplify_map_eq.
    repeat (try (rewrite -delete_insert_ne ; last done)); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ cs0 with "[$Hrmap $Hcs0]") as "Hrmap"; first by simplify_map_eq.
    repeat (try (rewrite -delete_insert_ne ; last done)); rewrite insert_delete_insert.
    iDestruct (big_sepM_insert _ _ cs1 with "[$Hrmap $Hcs1]") as "Hrmap"; first by simplify_map_eq.
    repeat (try (rewrite -delete_insert_ne ; last done)); rewrite insert_delete_insert.

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Harg_rmap' Hfull_rmap.
      rewrite !dom_delete_L.
      rewrite !dom_insert_L.
      rewrite !dom_delete_L.
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.

      rewrite -difference_difference_l_L.
      do 4 rewrite union_assoc_L.
      rewrite union_comm_L.
      admit. (* TODO should be OK, but just need to do some gset manipulation *)
      (* replace {[cs1; cs0; ct1; ct2; ctp]} *)
      (*   with ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]} : gset _) by set_solver. *)
      (* replace ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]}) *)
      (*            ∪ ({[cs1; cs0; ct1]} ∪ {[ct2; ctp]})) *)
      (*   with ( (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]} *)
      (*             ∪ {[cs1; cs0; ct1]}) ∪ {[ct2; ctp]}) by set_solver. *)
      (* rewrite union_comm_L. *)
      (* replace ( *)
      (*    (all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp; cs0; cs1; ct1]} ∪ {[cs1; cs0; ct1]}) *)
      (*   ) *)
      (*   with ( *)
      (*    all_registers_s ∖ dom arg_rmap ∖ {[PC; cgp; cra; csp]} *)
      (*   ). *)
      (* 2:{ *)
      (*   replace {[PC; cgp; cra; csp; cs0; cs1; ct1]} *)
      (*   with ( {[PC; cgp; cra; csp]} ∪ {[cs1; cs0; ct1]} : gset _) *)
      (*        by set_solver. *)
      (* rewrite -(difference_difference_l_L  _ _ {[cs1; cs0; ct1]}). *)
      (* rewrite difference_union_L. *)
      (* set_solver. *)
      (* } *)
      (* rewrite subseteq_union_1_L; set_solver. *)
    }
    iNext; iIntros "H".
    iDestruct "H" as (rmap') "(%Hrmap' & HPC & Hrmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 5 "Hcode" as a_jmp Ha_jmp "Hcode" "Hcont"; iHide "Hcont" as hcont.
    set (
        rmap'' :=
       <[PC:=WCap RX Global bpcc epcc (bpcc ^+ off_entry)%a]>
      (<[csp:=WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a]>
         (<[cra:=WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a]>
            (<[cgp:=WCap RW Global bcgp ecgp bcgp]> (arg_rmap' ∪ rmap'))))
      ).
    iSpecialize ("Hjmp_callee_pc" $! W2 rmap'' (related_sts_priv_refl_world W2)).

    (* Jalr cra cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    iEval (cbn) in "Hcgp".

    iDestruct (tframe_agree with "Htframe_full Htframe_frag") as "->".
    iDestruct (tframe_update _ _ (frm W + 1) with "Htframe_full Htframe_frag")
                as ">[Htframe_full Htframe_frag]".
    iMod ("Hclose_switcher_inv" with
           "[$Hna Hmtdc Hcode Hb_switcher Htstk Htframe_full]")
      as "Hna"
    .
    { iNext; iFrame "Hmtdc".
      iExists (frm W + 1),tstk_next'.
      iSplit; first done.
      iSplit; first done.
      iFrame.
      replace ((a_tstk ^+ 1) ^+ 1)%a with (a_tstk ^+ 2)%a by solve_addr+Htstk_ae.
      iFrame "∗#".
      iPureIntro.
      clear -H_tstk_frame Htstk_ba Htstk_ae Hbounds_tstk_b Hbounds_tstk_e.
      split; replace a_tstk with (b_tstk ^+ frm W)%a; solve_addr.
    }

    set (Pframe := ((a_tstk ^+ 1)%a ↦ₐ WCap RWL Local b_stk e_stk (a_stk ^+ 4)%a)%I).
    assert ( Nframe : namespace ). admit.
    iMod (na_inv_alloc
            logrel_nais
            ⊤ (Nframe .@ ι)
            (frame_inv C ι Pframe)
           with "[$Hsts_loc_ι $Ha1_tstk ]") as "#Hinv_frame".

    (* show that csp in safe-to-share *)
    iAssert ( interp W2 C (WCap RWL Local (a_stk ^+ 4)%a e_stk (a_stk ^+ 4)%a)) as "Hinterp_csp".
    { iApply (interp_monotone W).
      + admit. (* TODO should be fine *)
      + iApply (interp_weakeningEO with "Hinterp_wcsp"); auto.
        * solve_addr+Hstk_a3e Hstk_ba0.
        * solve_addr+Hstk_a3e Hstk_ba0.
    }

    iAssert (interp W2 C (WSentry XSRW_ Local b_switcher e_switcher (a_jmp ^+ 1)%a)) as "Hinterp_return".
    { shelve. }

    iDestruct (big_sepM_sep with "Harg_rmap'") as "[Harg_rmap' #Harg_rmap'_interp]".
    iDestruct (big_sepM_sep with "Hrmap'") as "[Hrmap' %Hrmap'_zero]".
    iCombine "Harg_rmap' Hrmap'" as "Hrmap'".

    rewrite -(big_sepM_union _ arg_rmap' rmap').
    2: {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      apply map_disjoint_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cgp with "[$Hrmap' $Hcgp]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ cra with "[$Hrmap' $Hcra]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ csp with "[$Hrmap' $Hcsp]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 2 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }
    iDestruct (big_sepM_insert _ _ PC with "[$Hrmap' $HPC]") as "Hrmap'".
    {
      clear -Harg_rmap' Hrmap'.
      rewrite /is_arg_rmap in Harg_rmap'; simplify_eq.
      rewrite /dom_arg_rmap in Hrmap'.
      do 3 rewrite lookup_insert_ne //.
      apply not_elem_of_dom.
      set_solver.
    }

    match goal with
    | _ : _ |- context [<[PC:=?w]> ?m] =>
        subst rmap'' ; set (rmap'' := <[PC:=w]> m)
    end.


    iApply "Hjmp_callee_pc"; iFrame.
    iSplitR "Htframe_frag"; cycle 1.
    { subst W2 W1. rewrite frame_W_lookup_frm /= std_update_multiple_frm /=. }
    Lemma
  tframe_frag (close_list ltemp_unknown (std_update_multiple (revoke W) (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary)).2

    { rewrite /execute_entry_point_register; cbn.
      iSplitR.
      {
        clear -Hrmap' Harg_rmap'.
        subst hinv_switcher hφ0 htemp_unknown Pframe.
        iPureIntro.
        intros r; cbn.
        destruct (decide (r = PC)) as [Hrpc | Hrpc]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = csp)) as [Hrcsp | Hrcsp]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = cra)) as [Hrcra | Hrcra]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        destruct (decide (r = cgp)) as [Hrcgp | Hrcgp]; simplify_eq; first by rewrite lookup_insert.
        rewrite lookup_insert_ne //.
        apply elem_of_dom.
        rewrite dom_union.
        rewrite elem_of_union.
        destruct (decide (r ∈ dom arg_rmap')); first by left.
        right.
        rewrite Harg_rmap' in n.
        assert (r ∉ ({[PC; cra; cgp; csp]} : gset RegName)).
        { set_solver.  }
        rewrite Hrmap'.
        rewrite elem_of_difference.
        split; first by apply all_registers_s_correct.
        set_solver.
      }
      iSplitR.
      { iPureIntro. by rewrite lookup_insert. }
      iSplitR.
      { iPureIntro.
        subst rmap''.
        do 3 (rewrite lookup_insert_ne //).
        by rewrite lookup_insert.
      }
      iSplitR.
      { iIntros (wstk Hcsp).
        subst rmap''.
        rewrite lookup_insert_ne // in Hcsp.
        rewrite lookup_insert in Hcsp; simplify_eq.
        iFrame "#".
      }
      iSplitR.
      { iIntros (wret Hcra).
        subst rmap''.
        do 2 (rewrite lookup_insert_ne // in Hcra).
        rewrite lookup_insert in Hcra; simplify_eq.
        iFrame "#".
      }

      iSplitR.
      { iIntros (r wr Hr_arg Hr).
        subst rmap''.
        iClear "Hjmp_callee_pc Hp_ot_switcher".
        clear -Hr_arg Hr Harg_rmap' Hrmap'.
        rewrite /dom_arg_rmap in Hr_arg.
        destruct (decide (r = PC)) as [Hrpc|Hrpc]
        ; first (exfalso ; set_solver+Hr_arg Hrpc).
        destruct (decide (r = csp)) as [Hrcsp|Hrcsp]
        ; first (exfalso ; set_solver+Hr_arg Hrcsp).
        destruct (decide (r = cra)) as [Hrcra|Hrcra]
        ; first (exfalso ; set_solver+Hr_arg Hrcra).
        destruct (decide (r = cgp)) as [Hrcgp|Hrcgp]
        ; first (exfalso ; set_solver+Hr_arg Hrcgp).
        do 4 (rewrite lookup_insert_ne // in Hr).
        rewrite lookup_union in Hr.
        rewrite union_Some in Hr.
        destruct Hr as [Hr | Hr]; cycle 1.
        { exfalso.
          destruct Hr as [Hcontra _].
          rewrite /is_arg_rmap /dom_arg_rmap in Harg_rmap'.
          rewrite -Harg_rmap' in Hr_arg.
          apply lookup_lookup_total_dom in Hr_arg.
          congruence.
        }
        rewrite big_sepM_lookup; eauto.
      }
      {
        iIntros (r Hr); iPureIntro.
        clear -Hr Harg_rmap' Hrmap' Hrmap'_zero.

        rewrite not_elem_of_union in Hr.
        destruct Hr as [Hr1 Hr2].
        repeat (rewrite not_elem_of_union in Hr2).
        repeat (rewrite not_elem_of_singleton in Hr2).
        destruct Hr2 as [ [ [Hrpc Hrcra ] Hrcgp] Hrcsp] .
        do 4 (rewrite lookup_insert_ne //).
        rewrite lookup_union.
        rewrite union_Some.
        right.
        split.
        {
        rewrite /is_arg_rmap in Harg_rmap'.
        rewrite -Harg_rmap' not_elem_of_dom in Hr1.
        done.
        }
        assert (is_Some (rmap' !! r)) as [wr Hr].
        { rewrite -elem_of_dom.
          rewrite Hrmap'.
          rewrite elem_of_difference.
          split ; first apply all_registers_s_correct.
          set_solver.
        }
        eapply map_Forall_lookup_1 in Hrmap'_zero; eauto.
        by simplify_eq.
    }

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
