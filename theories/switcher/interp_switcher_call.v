From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel region_invariants bitblast.
From cap_machine Require Import interp_weakening.
From cap_machine Require Import wp_rules_interp switcher_macros_spec.
From cap_machine Require Import rules proofmode monotone.
From cap_machine Require Import fundamental.
From cap_machine Require Import switcher_preamble.
From cap_machine Require Import interp_switcher_return.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp) W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv_switcher %cstk %Ws %Cs %regs [[%Hfull_rmap #Hreg] (Hrmap & Hr & Hsts & Hcont & Hna & Hcstk & %Hframe)]".
    rewrite /registers_pointsto.
    iPoseProof fundamental_ih as "IH". (* used for weakening lemma later *)

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    specialize (Hfull_rmap csp) as HH;destruct HH as [wcsp Hstk].
    specialize (Hfull_rmap ct2) as HH;destruct HH as [? wct2].
    specialize (Hfull_rmap ctp) as HH;destruct HH as [? wctp].
    iExtract "Hrmap" csp as "Hcsp".
    iExtract "Hrmap" ct2 as "Hct2".
    iExtract "Hrmap" ctp as "Hctp".

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    iDestruct ("Hreg" $! csp with "[//] [//]") as "#Hspv".

    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* --- GetP ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & Hcap_wstk & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|];cycle 1.
    { (* p ≠ RWL *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      iIntros "!> (HPC & Hi & Hct2)".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* -----------------------------------  *)
      (* ------ Lcommon_force_unwind -------  *)
      (* -----------------------------------  *)
      focus_block 17 "Hcode" as a_force_unwind Ha_force_unwind "Hcode" "Hcls"; iHide "Hcls" as hcont.
      specialize (Hfull_rmap ca0) as HH;destruct HH as [? ?].
      specialize (Hfull_rmap ca1) as HH;destruct HH as [? ?].
      iExtract "Hrmap" ca0 as "Hca0".
      iExtract "Hrmap" ca1 as "Hca1".
      (* Mov ca0 ECOMPARTMENTFAIL; *)
      iInstr "Hcode".
      (* Mov ca1 0; *)
      iInstr "Hcode".
      (* Jmp Lswitcher_after_compartment_call_z *)
      iInstr "Hcode".
      { transitivity (Some a_switcher_return); last done.
        pose proof switcher_return_entry_point.
        solve_addr.
      }
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
      { iNext. iExists _,_. iFrame "∗ # %".
        iPureIntro; split; auto.
      }

      iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
      iApply interp_expr_switcher_return; iFrame "∗%#".
      rewrite /interp_reg /=.
      iSplit.
      + rewrite /full_map.
        iIntros (r) ; iPureIntro.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_rmap.
      + iIntros (r w HrPC Hr).
        destruct (decide (r = ca1)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ca0)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ct2)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ctp)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = csp)); simplify_map_eq ; iApply "Hreg"; eauto.
    }

    (* p = RWL *)
    rewrite Hp0'.
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls"; iHide "Hcls" as hcont.
    (* --- GetL ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%g0 & %Hg0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|];cycle 1.
    { (* g ≠ Local *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_jnz_success_jmp_z with "[$HPC $Hi $Hct2]"); try solve_pure.
      { intros Hcontr; inversion Hcontr; done. }
      { set (Lcommon_force_unwind := default 0 (switcher_labels !! ".Lcommon_force_unwind")).
        transitivity (Some ((a_switcher_call ^+ Lcommon_force_unwind)%a)); auto.
        subst Lcommon_force_unwind; rewrite /switcher_labels; simplify_map_eq.
        solve_addr+Ha_csp_check_loc Hcont_switcher_region.
      }
      iIntros "!> (HPC & Hi & Hct2)".
      iEval (simplify_map_eq) in "HPC".
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* -----------------------------------  *)
      (* ------ Lcommon_force_unwind -------  *)
      (* -----------------------------------  *)
      focus_block 17 "Hcode" as a_force_unwind Ha_force_unwind "Hcode" "Hcls"; iHide "Hcls" as hcont.
      specialize (Hfull_rmap ca0) as HH;destruct HH as [? ?].
      specialize (Hfull_rmap ca1) as HH;destruct HH as [? ?].
      iExtract "Hrmap" ca0 as "Hca0".
      iExtract "Hrmap" ca1 as "Hca1".
      (* Mov ca0 ECOMPARTMENTFAIL; *)
      iInstr "Hcode".
      (* Mov ca1 0; *)
      iInstr "Hcode".
      (* Jmp Lswitcher_after_compartment_call_z *)
      iInstr "Hcode".
      { transitivity (Some a_switcher_return); last done.
        pose proof switcher_return_entry_point.
        solve_addr.
      }
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
      { iNext. iExists _,_. iFrame "∗ # %".
        iPureIntro; split; auto.
      }

      iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
      iApply interp_expr_switcher_return; iFrame "∗%#".
      rewrite /interp_reg /=.
      iSplit.
      + rewrite /full_map.
        iIntros (r) ; iPureIntro.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_rmap.
      + iIntros (r w HrPC Hr).
        destruct (decide (r = ca1)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ca0)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ct2)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ctp)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = csp)); simplify_map_eq ; iApply "Hreg"; eauto.
    }
    rewrite Hg0'.
    (* g = Local *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    specialize (Hfull_rmap cs0) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cs1) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cra) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap cgp) as HH;destruct HH as [? ?].
    specialize (Hfull_rmap ct1) as HH;destruct HH as [? ?].
    iExtract "Hrmap" cs0 as "Hcs0".
    iExtract "Hrmap" cs1 as "Hcs1".
    iExtract "Hrmap" cra as "Hcra".
    iExtract "Hrmap" cgp as "Hcgp".
    iExtract "Hrmap" ct1 as "Hct1".

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block 2 "Hcode" as a_entry_first_spill Ha_entry_first_spill "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_csp_check_loc.

    (* --- Store csp cs0 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp with "[$HPC $Hi Hcsp Hcs0 $Hr $Hsts]"); try solve_pure.
    { iFrame. iFrame "#". by iApply "Hreg";eauto. }
    iIntros "!>" (v) "[-> | (% & % & % & % & % & -> & -> & HPC & Hi & Hcs0
    & Hcsp & Hr & Hsts & %Hcanstore & %bounds)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    cbn in Hp0,Hg0; simplify_eq.
    assert (encodePerm p = encodePerm RWL)%Z as ?%encodePerm_inj by lia; simplify_eq; clear Hp0'.
    assert (encodeLoc g = encodeLoc Local)%Z as ?%encodeLoc_inj by lia; simplify_eq; clear Hg0'.

    (* --- Lea csp 1 --- *)
    destruct (a + 1)%a eqn:Ha1;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcs1 $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcs1
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f + 1)%a eqn:Ha2;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    (* --- Store csp cra --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcra $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcra
    & Hcsp & Hr & Hsts & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f0 + 1)%a eqn:Ha3;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".


    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$HPC $Hi Hcsp Hcgp $Hr $Hsts]"); try solve_pure.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & HPC & Hi & Hcgp
    & Hcsp & Hr & Hsts & _ & %bounds')] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f1 + 1)%a eqn:Ha4;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block 3 "Hcode" as a_tstack_push Ha_tstack_push "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_entry_first_spill.

    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- GetA cs0 ct2 --- *)
    iInstr "Hcode".

    (* --- Add cs0 cs0 1%Z --- *)
    iInstr "Hcode".

    (* --- GetE ctp ct2 --- *)
    iInstr "Hcode".

    (* --- Sub ctp ctp cs0 --- *)
    iInstr "Hcode".

    (* --- Jnz 2%Z ctp --- *)
    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; cycle 1.
    {
      iInstr "Hcode".
      (* --- Jmp  Lswitch_trusted_stack_exhausted_z --- *)
      iInstr "Hcode".
      { set (Lswitch_trusted_stack_exhausted := default 0 (switcher_labels !! ".Lswitch_trusted_stack_exhausted")).
        transitivity (Some ((a_switcher_call ^+ Lswitch_trusted_stack_exhausted)%a)); auto.
        subst Lswitch_trusted_stack_exhausted; rewrite /switcher_labels; simplify_map_eq.
        solve_addr+Ha_tstack_push Hsize.
      }
      iEval (simplify_map_eq) in "HPC".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* ----------------------------------------------  *)
      (* ------ Lswitch_trusted_stack_exhausted -------  *)
      (* ----------------------------------------------  *)
      focus_block 16 "Hcode" as a_tstk_exhausted Ha_tstk_exhausted "Hcode" "Hcls"; iHide "Hcls" as hcont.
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some f1); auto; solve_addr. }
      (* Load cgp csp; *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_interp_cap with "[$HPC $Hi Hcsp Hcgp $Hr $Hsts]"); try solve_pure.
      { iFrame. by iApply (interp_lea with "Hspv"). }
      iIntros "!>" (v) "[-> | (%wcgp & -> & HPC & Hi & Hcsp
    & Hcgp & #Hinterp_wcgp & Hr & Hsts & _ & _)] /=".
      { wp_pure; wp_end; iIntros "%Hcontr";done. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some f0); auto. solve_addr+Ha3. }
      (* Load cra csp; *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_interp_cap with "[$HPC $Hi Hcsp Hcra $Hr $Hsts]"); try solve_pure.
      { iFrame. by iApply (interp_lea with "Hspv"). }
      iIntros "!>" (v) "[-> | (%wcra & -> & HPC & Hi & Hcsp
    & Hcra & #Hinterp_wcra & Hr & Hsts & _ & _)] /=".
      { wp_pure; wp_end; iIntros "%Hcontr";done. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some f); auto. solve_addr+Ha2. }
      (* Load cs1 csp; *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_interp_cap with "[$HPC $Hi Hcsp Hcs1 $Hr $Hsts]"); try solve_pure.
      { iFrame. by iApply (interp_lea with "Hspv"). }
      iIntros "!>" (v) "[-> | (%wcs1 & -> & HPC & Hi & Hcsp
    & Hcs1 & #Hinterp_wcs1 & Hr & Hsts & _ & _)] /=".
      { wp_pure; wp_end; iIntros "%Hcontr";done. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some a); auto. solve_addr+Ha1. }
      (* Load cs0 csp; *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_load_interp_cap with "[$HPC $Hi Hcsp Hcs0 $Hr $Hsts]"); try solve_pure.
      { iFrame. by iApply (interp_lea with "Hspv"). }
      iIntros "!>" (v) "[-> | (%wcs0 & -> & HPC & Hi & Hcsp
    & Hcs0 & #Hinterp_wcs0 & Hr & Hsts & _ & _)] /=".
      { wp_pure; wp_end; iIntros "%Hcontr";done. }
      wp_pure.
      iSpecialize ("Hcode" with "[$]").

      specialize (Hfull_rmap ca0) as HH;destruct HH as [? ?].
      specialize (Hfull_rmap ca1) as HH;destruct HH as [? ?].
      iExtract "Hrmap" ca0 as "Hca0".
      iExtract "Hrmap" ca1 as "Hca1".
      (* Mov ca0 ENOTENOUGHTRUSTEDSTACK; *)
      iInstr "Hcode".
      (* Mov ca1 0; *)
      iInstr "Hcode".
      (* Jmp Lswitch_callee_dead_zeros_z *)
      iInstr "Hcode".
      { set (Lswitch_callee_dead_zeros := default 0 (switcher_labels !! ".Lswitch_callee_dead_zeros")).
        transitivity (Some ((a_switcher_call ^+ Lswitch_callee_dead_zeros)%a)); auto.
        subst Lswitch_callee_dead_zeros; rewrite /switcher_labels; simplify_map_eq.
        solve_addr.
      }
      iEval (simplify_map_eq) in "HPC".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* ---- clear registers  ---- *)
      focus_block 14 "Hcode" as a7 Ha7 "Hcode" "Hcls"; iHide "Hcls" as hcont.
      iInsertList "Hrmap" [ct1;ctp;ct2].
      iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
      { clear -Hfull_rmap.
        repeat (rewrite -delete_insert_ne //).
        repeat (rewrite dom_delete_L).
        repeat (rewrite dom_insert_L).
        apply regmap_full_dom in Hfull_rmap.
        rewrite Hfull_rmap.
        set_solver.
      }
      iNext; iIntros "H".
      iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hrmap & Hcode)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      focus_block 15 "Hcode" as a10 Ha10 "Hcode" "Hcsl"; iHide "Hcsl" as hcont.
      (* Jalr cnull cra *)
      iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) arg_rmap' ⌝)%I as
        "%Harg_rmap'_zeroes".
      { iDestruct (big_sepM_sep with "Hrmap") as "[_ %]"; auto. }
      iExtract "Hrmap" cnull as "[Hcnull %]".
      iInstr "Hcode" with "Hlc".
      iAssert ( ∃ wnull, cnull ↦ᵣ wnull ∗ ⌜ wnull = WInt 0⌝ )%I with "[Hcnull]" as (wnull) "Hcnull".
      { iFrame; done. }
      iInsert "Hrmap" cnull.
      iAssert (⌜ <[cnull := wnull]> arg_rmap' = arg_rmap' ⌝)%I as "%Harg_rmap'_id".
      { iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hint]".
        iPureIntro.
        clear -Harg_rmap' Hint Harg_rmap'_zeroes.
        assert (is_Some (arg_rmap' !! cnull)) as [? Hcnull] by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
        apply insert_id.
        pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
        rewrite H.
        rewrite Hcnull.
        by eapply map_Forall_lookup in Hcnull; eauto; cbn in *; simplify_map_eq.
      }
      rewrite Harg_rmap'_id.
      clear dependent Harg_rmap'_id Harg_rmap'_zeroes wcnull wnull.
      unfocus_block "Hcode" "Hcsl" as "Hcode"; subst hcont.

    (* Close the switcher's invariant *)
      iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
      { iNext. iExists _,_. iFrame "∗ # %".
        iPureIntro; split; auto.
      }

      iAssert (
          ∃ rmap', ⌜ dom rmap' = dom arg_rmap' ⌝ ∗ ([∗ map] r↦w ∈ rmap', r ↦ᵣ w)
                   ∗ (∀ (r : RegName) (v : leibnizO Word), ⌜r ≠ PC⌝ → ⌜rmap' !! r = Some v⌝ → interp W C v)
        )%I with "[Hrmap]" as (rmap') "(%Hdom_rmap' & Hrmap & #Hrmap_interp')".
      {
        iExists (fmap (fun v => WInt 0) arg_rmap').
        iSplit ; [iPureIntro; apply dom_fmap_L|].
        iSplitL.
        {
          iClear "#".
          iStopProof.
          clear.
          induction arg_rmap' using map_ind; first rewrite fmap_empty; auto.
          rewrite fmap_insert.
          iIntros "Hrmap".
          iDestruct ( big_sepM_insert with "Hrmap" ) as "[ [Hi ->] Hrmap]"; auto.
          iApply big_sepM_insert.
          { by rewrite lookup_fmap H; simplify_map_eq. }
          iFrame.
          iApply (IHarg_rmap' with "Hrmap").
        }
        iIntros (r w HrPC Hr).
        rewrite lookup_fmap_Some in Hr.
        destruct Hr as (? & <- & Hr').
        iEval (rewrite fixpoint_interp1_eq); done.
      }

      (* Insert the registers in the rmap *)
      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cra m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcra]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cgp m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcgp]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca0 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca1 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs0 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs1 m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete csp m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcsp]") as "Hrmap".

      destruct ( decide (isCorrectPC (updatePcPerm wcra))) as [HcorrectWret|HcorrectWret]; cycle 1.
      { (* The PC is not correct, the execution will crash *)
        iApply (wp_bind (fill [SeqCtx])).
        iApply (wp_notCorrectPC with "HPC"); first done.
        iNext; iIntros "HPC /=".
        iApply wp_pure_step_later; auto; iNext; iIntros "_".
        iApply wp_value; iIntros; discriminate.
      }
      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete PC m) end.
      2: { rewrite delete_notin; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $HPC]") as "Hrmap".

    rewrite -(insert_id (<[PC:=updatePcPerm wcra]> _) PC (updatePcPerm wcra))
    ; last (clear;simplify_map_eq; done).
    destruct wcra as [ z | [pcra gcra bcra ecra acra|]  | pcra gcra bcra ecra acra | ot sb ] ; iEval (cbn) in "Hrmap".
    all: cbn in HcorrectWret.
    all: inversion HcorrectWret; simplify_eq.
      + (* wret was a regular capability: apply the FTLR *)
        iApply ("IH" with "[] [] [$] [$] [$] [$] [%] [$] [$]"); eauto.
        { iIntros (r); iPureIntro.
          clear -Hdom_rmap' Harg_rmap'.
          destruct (decide (r = PC)); simplify_map_eq; first done.
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          apply elem_of_dom.
          rewrite Hdom_rmap' Harg_rmap'.
          pose proof all_registers_s_correct.
          set_solver.
        }
        {
          iIntros (r rv HrPC Hr).
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first (iApply interp_int).
          destruct (decide (r = ca0)); simplify_map_eq; first (iApply interp_int).
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          iApply "Hrmap_interp'"; eauto.
          iPureIntro.
          rewrite lookup_delete_ne; eauto.
        }
      + iAssert (interp W C (WSentry pcra gcra bcra ecra acra)) as "#Hinterp_wret'" ; first done.
        iEval (rewrite fixpoint_interp1_eq /=) in "Hinterp_wcra".
        iDestruct "Hinterp_wcra" as "#Hinterp_wret".
        rewrite /enter_cond.
        iAssert (future_world gcra W W) as "-#Hfuture".
        { destruct gcra; cbn; iPureIntro
          ; [apply related_sts_priv_refl_world| apply related_sts_pub_refl_world].
        }
        iSpecialize ("Hinterp_wret" $! W with "[$]").
        iSpecialize ("Hinterp_wret" $! gcra (LocalityFlowsToReflexive gcra)).
        iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_wret]") as ">Hinterp_wret".
        rewrite /interp_expr /=.
        iDestruct ("Hinterp_wret" with "[$Hcont $Hrmap $Hr $Hsts $Hcstk $HH]") as "HA"; eauto.
        iSplitR; last (iPureIntro; simplify_map_eq; done).
        iSplit.
        * iIntros (r); iPureIntro.
          clear -Hdom_rmap' Harg_rmap'.
          destruct (decide (r = PC)); simplify_map_eq; first done.
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          apply elem_of_dom.
          rewrite Hdom_rmap' Harg_rmap'.
          pose proof all_registers_s_correct.
          set_solver.
        * iIntros (r rv HrPC Hr).
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first (iApply interp_int).
          destruct (decide (r = ca0)); simplify_map_eq; first (iApply interp_int).
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          iApply "Hrmap_interp'"; eauto.
          iPureIntro.
          rewrite lookup_delete_ne; eauto.
    }
    iInstr "Hcode".

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Hastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr "Hcode".

    (* --- Store ct2 csp --- *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr "Hcode".
    { solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block 4 "Hcode" as a_stack_chop Ha_stack_chop "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_push.

    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".
    { solve_addr. }

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block 5 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_stack_chop.
    iApply (clear_stack_interp_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hr $Hsts]"); try solve_pure.
    iSplit.
    { iApply interp_weakeningEO;eauto. all: solve_addr. }
    iSplitL;cycle 1.
    { iIntros "!> %Hcontr"; done. }
    iIntros "!> ((HPC & Hcsp & Hcs0 & Hcs1 & Hcode) & Hr & Hsts)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block 6 "Hcode" as a_LoadCapPCC Ha_LoadCapPCC "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear_stk1.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]"); auto; [solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= b_switcher). solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.


    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block 7 "Hcode" as a_unseal_entry Ha_unseal_entry "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_LoadCapPCC.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    rewrite /load_word. iSimpl in "Hcs0".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_unseal_unknown with "[$HPC $Hi $Hcs0 $Hct1]"); try solve_pure.
    iIntros "!>" (ret) "[-> | (% & % & % & % & % & %wsb & -> & HPC & Hi & Hcs0 & Hct1 & %Heq & % & %spec)]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    simplify_eq.

    (* get the seal inv and compare with wsb *)
    iDestruct ("Hreg" $! ct1 with "[//] [//]") as "#Hct1v".
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher wsb)).
    iDestruct "Hct1v" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable wsb)).

    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (??????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & #Hentry & Hexec)". simpl fst. simpl snd.
    inversion Heq.

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.


    (* ------------------------------  *)
    (* ---- Lswitch_callee_load -----  *)
    (* ------------------------------  *)
    focus_block 8 "Hcode" as a_callee_load Ha_callee_load "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_unseal_entry.


    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=b_tbl). solve_addr-. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(b_tbl ^+ 1)%a). solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    (* clear registers except parameters *)
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.


    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block 9 "Hcode" as a_clear Ha_clear "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_callee_load.

    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    set (params := dom_arg_rmap 8).
    (* ({[ca0; ca1; ca2; ca3; ca4; ca5; ca5; ct0]} : gset RegName)). *)
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    rewrite -(map_filter_union_complement Pf rmap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }

    rewrite encode_entry_point_eq_nargs;last lia.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ _ (nargs+1) with "[- $HPC $Hcode]"); try solve_pure.
    { instantiate (1:=filter (λ v : RegName * Word, (Pf v)%type) rmap').
      rewrite /is_arg_rmap /dom_arg_rmap.
      apply dom_filter_L. clear -Hfull_rmap.
      rewrite /rmap'. split.
      - intros Hi.
        repeat (rewrite lookup_delete_ne;[|set_solver]).
        specialize (Hfull_rmap i) as [x Hx].
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    { lia. }
    iSplitL "Hct2".
    { replace (Z.of_nat nargs + 1)%Z with (Z.of_nat (nargs + 1))%Z by lia; done. }
    iSplitL "Hparams".
    { iApply big_sepM_sep. iFrame. iApply big_sepM_forall.
      { intros k v.
        destruct (decide ( (k ∈ dom_arg_rmap (nargs + 1 - 1)) )); tc_solve.
      }
      iIntros (k v [Hin Hspec]%map_lookup_filter_Some).
      destruct ( decide (k ∈ dom_arg_rmap (nargs + 1 - 1)) ); last done.
      iApply ("Hreg" $! k);iPureIntro; first set_solver+Hspec.
      repeat (apply lookup_delete_Some in Hin as [_ Hin]); auto.
    }
    iIntros "!> (%arg_rmap' & %Hisarg_rmap' & HPC & Hct2 & Hparams & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ----------------------------------- *)
    (* ---- clear_registers_pre_call ----- *)
    (* ----------------------------------- *)
    focus_block 10 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear.

    rewrite /rmap'. rewrite !map_filter_delete.
    iDestruct (big_sepM_insert with "[$Hrest $Hct1]") as "Hrest"
    ; [clear; by simplify_map_eq|rewrite insert_delete_insert].
    iInsertList "Hrest" [ctp;ct2;cs1;cs0].

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hrest]"); try solve_pure.
    { clear -Hfull_rmap. apply regmap_full_dom in Hfull_rmap as Heq'.
      rewrite !dom_insert_L !dom_delete_L.
      cut (dom (filter (λ v, ¬ Pf v) regs) = all_registers_s ∖ dom_arg_rmap 8);[set_solver|].
      apply (dom_filter_L _ (regs : gmap RegName Word)).
      split.
      - intros [Hi Hni]%elem_of_difference.
        specialize (Hfull_rmap i) as [x Hx]. eauto.
      - intros [? [? ?] ]. apply elem_of_difference.
        split;auto. apply all_registers_s_correct. }

    iIntros "!> (%rmap'' & %Hrmap'' & HPC & Hrest & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------ *)
    (* ---- Lswitch_callee_call ----- *)
    (* ------------------------------ *)
    focus_block 11 "Hcode" as a_callee_call Ha_callee_call "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear'.

    eset (frame :=
           {| wret := WInt 0;
              wstk := (WCap RWL Local b e a);
              wcgp := WInt 0;
              wcs0 := WInt 0;
              wcs1 := WInt 0;
              is_untrusted_caller := true
           |}).

    iSpecialize ("Hexec" with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }
    iInstr "Hcode".
    iSpecialize ("Hexec" $! (frame :: cstk) (W :: Ws) (C :: Cs)).
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hf3 Hstk_interp]") as "HH".
    { iNext. iExists _,_. iFrame "∗ #".
      rewrite (finz_incr_eq Hf4).
      replace (f3 ^+ -1)%a with a_tstk by solve_addr+Hastk.
      iFrame. simpl. iPureIntro.
      repeat (split;auto);[solve_addr..|repeat f_equiv;solve_addr].
    }

    iApply "Hexec".
    iSplitL "Hcont".
    { iFrame. iNext. simpl.
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ???????) "(HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iSplitR.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iFrame.
    rewrite /execute_entry_point_register.
    iDestruct (big_sepM_sep with "Hrest") as "[Hrest #Hnil]".
    iDestruct (big_sepM_sep with "Hparams") as "[Hparams #Hval]".
    iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap'' Hisarg_rmap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].

    cbn.
    iFrame.
    iSplit;last (iPureIntro; split ;[split|];[reflexivity|reflexivity|solve_addr]).
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Hisarg_rmap' Hrmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap'' Hisarg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    repeat iSplit.
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_callee_call Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro. clear -Ha4 Ha3 Ha2 Ha1 bounds. simplify_map_eq.
      replace f2 with (a^+4)%a by solve_addr.
      done.
    - iApply (interp_weakening with "IH Hspv");auto
      ;[solve_addr+bounds' Ha4 Ha3 Ha2 Ha1|solve_addr-].
    - iIntros (r v Hr Hv).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?" ;eauto.
        destruct (decide (r ∈ _)) as [|Hcontra]; first iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
        iApply interp_int.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?";eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "Hinv").
  Qed.

End fundamental.
