From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From cap_machine Require Export logrel logrel_extra monotone.
From cap_machine Require Import rules_JmpCap.
From cap_machine Require Import fundamental.
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

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName) (wstk : Word)
    (Nswitcher : namespace)
    :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp cstk Ws Cs) cstk Ws Cs W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_return) wstk.
  Proof.
    iIntros  " #Hinv_switcher %rmap [[%Hfull_rmap #Hrmap_interp] (Hrmap & %Hstk & Hr & Hsts & Hcont_K & Hna & Hcstk & %Hfreq)]".
    rewrite /registers_pointsto.

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

    (* --- Extract scratch registers ct2 ctp --- *)
    iDestruct (big_sepM_delete _ _ PC with "Hrmap") as "[HPC Hrmap]"; first by simplify_map_eq.
    rewrite delete_insert_delete.
    assert (exists wcra, rmap !! cra = Some wcra)
      as [wcra Hwcra] by (by specialize (Hfull_rmap cra)).
    iDestruct (big_sepM_delete _ _ cra with "Hrmap") as "[Hcra Hrmap]"; first by simplify_map_eq.
    assert (exists wcsp, rmap !! csp = Some wcsp)
      as [wcsp Hwcsp] by (by specialize (Hfull_rmap csp)).
    iDestruct (big_sepM_delete _ _ csp with "Hrmap") as "[Hcsp Hrmap]"; first by simplify_map_eq.
    assert (exists wcgp, rmap !! cgp = Some wcgp)
      as [wcgp Hwcgp] by (by specialize (Hfull_rmap cgp)).
    iDestruct (big_sepM_delete _ _ cgp with "Hrmap") as "[Hcgp Hrmap]"; first by simplify_map_eq.
    assert (exists wca0, rmap !! ca0 = Some wca0)
      as [wca0 Hwca0] by (by specialize (Hfull_rmap ca0)).
    iDestruct (big_sepM_delete _ _ ca0 with "Hrmap") as "[Hca0 Hrmap]"; first by simplify_map_eq.
    assert (exists wca1, rmap !! ca1 = Some wca1)
      as [wca1 Hwca1] by (by specialize (Hfull_rmap ca1)).
    iDestruct (big_sepM_delete _ _ ca1 with "Hrmap") as "[Hca1 Hrmap]"; first by simplify_map_eq.
    assert (exists wctp, rmap !! ctp = Some wctp)
      as [wctp Hwctp] by (by specialize (Hfull_rmap ctp)).
    iDestruct (big_sepM_delete _ _ ctp with "Hrmap") as "[Hctp Hrmap]"; first by simplify_map_eq.
    assert (exists wca2, rmap !! ca2 = Some wca2)
      as [wca2 Hwca2] by (by specialize (Hfull_rmap ca2)).
    iDestruct (big_sepM_delete _ _ ca2 with "Hrmap") as "[Hca2 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs1, rmap !! cs1 = Some wcs1)
      as [wcs1 Hwcs1] by (by specialize (Hfull_rmap cs1)).
    iDestruct (big_sepM_delete _ _ cs1 with "Hrmap") as "[Hcs1 Hrmap]"; first by simplify_map_eq.
    assert (exists wcs0, rmap !! cs0 = Some wcs0)
      as [wcs0 Hwcs0] by (by specialize (Hfull_rmap cs0)).
    iDestruct (big_sepM_delete _ _ cs0 with "Hrmap") as "[Hcs0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct0, rmap !! ct0 = Some wct0)
      as [wct0 Hwct0] by (by specialize (Hfull_rmap ct0)).
    iDestruct (big_sepM_delete _ _ ct0 with "Hrmap") as "[Hct0 Hrmap]"; first by simplify_map_eq.
    assert (exists wct1, rmap !! ct1 = Some wct1)
      as [wct1 Hwct1] by (by specialize (Hfull_rmap ct1)).
    iDestruct (big_sepM_delete _ _ ct1 with "Hrmap") as "[Hct1 Hrmap]"; first by simplify_map_eq.


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
    iAssert (interp W C wca0) as "#Hinterp_wca0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wca1) as "#Hinterp_wca1".
    { iApply "Hrmap_interp"; eauto; done. }

    rewrite /switcher_instrs /switcher_call_instrs /switcher_return_instrs.
    rewrite -!app_assoc.

    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }
    focus_block_0 "Hcode" as "Hcode" "Hcont"; iHide "Hcont" as hcont.
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.
    focus_block_nochangePC 6 "Hcode" as a5 Ha5 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a5 = a_switcher_return); [|simplify_eq].
    { cbn in Ha5.
      clear -Ha5.
      pose proof switcher_return_entry_point as Hret; cbn in Hret.
      pose proof switcher_call_entry_point as Hcall; cbn in Hcall.
      solve_addr.
    }

    (* ReadSR ctp mtdc *)
    iInstr "Hcode" with "Hlc".


    (* Load csp ctp *)
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Load.wp_load_fail_not_withinbounds with "[HPC Hi Hctp Hcsp]")
      ; try iFrame
      ; try solve_pure.
      { rewrite /withinBounds.
        apply andb_false_iff; right.
        solve_addr+Htstk_ae.
      }
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }

    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.
    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    { (* In the case where main tries to return, the initial stack is simply 0 *)
    (*      and it will fails *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iInstr "Hcode".
      { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
      (* Lea ctp (-1)%Z *)
      destruct (decide (b_trusted_stack <= (b_trusted_stack ^+ -1))%a) as [Hb_trusted_stack1'|Hb_trusted_stack1'].
      {
        assert ((b_trusted_stack + -1) = None)%a by solve_addr+Hb_trusted_stack1'.
        iInstr_lookup "Hcode" as "Hi" "Hcode".
        wp_instr.
        iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
        ; try iFrame
        ; try solve_pure.
        iNext; iIntros "_".
        wp_pure; wp_end ; by iIntros (?).
      }
      assert (is_Some (b_trusted_stack + -1))%a as [b_trusted_stack1 Hb_trusted_stack1] by solve_addr+Hb_trusted_stack1'.
      clear Hb_trusted_stack1'.
      iInstr "Hcode".
      (* WriteSR mtdc ctp *)
      iInstr "Hcode".
      (* Lea csp (-1)%Z *)

      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_integer with "[HPC Hi Hcsp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    destruct Ws;[done|].
    destruct Cs;[done|].
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as (wtstk4) "[Ha_tstk Hcframe_interp]".
    destruct wstk0; try done.
    destruct sb; try done.
    destruct p; try done.
    destruct rx; try done.
    destruct w; try done.
    destruct dl; try done.
    destruct dro; try done.
    destruct g; try done.
    rename a into a_stk; rename b into b_stk; rename e into e_stk.
    iDestruct "Hcframe_interp" as "(%HWF & -> & Hcframe_interp)".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hfreq).

    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".
    iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_callee_wstk]") as ">#Hinterp_callee_wstk'".
    iClear "Hinterp_callee_wstk" ; iRename "Hinterp_callee_wstk'" into "Hinterp_callee_wstk".
    iAssert (
        ∃ wastk wastk1 wastk2 wastk3,
        let la := (if is_untrusted_caller then finz.seq_between a_stk (a_stk ^+ 4)%a else []) in
        let lv := (if is_untrusted_caller then [wastk;wastk1;wastk2;wastk3] else []) in
          a_stk ↦ₐ wastk
          ∗ (a_stk ^+ 1)%a ↦ₐ wastk1
          ∗ (a_stk ^+ 2)%a ↦ₐ wastk2
          ∗ (a_stk ^+ 3)%a ↦ₐ wastk3
          ∗ ▷ ([∗ list] a ; v ∈ la ; lv, ▷ closing_resources interp W C a v)
          ∗ ⌜if is_untrusted_caller then True else (wastk = wcs2 ∧ wastk1 = wcs3 ∧ wastk2 = wret ∧ wastk3 = wcgp0)⌝
          ∗ open_region_many W C la
          ∗ sts_full_world W C
      )%I
      with "[Hcframe_interp Hr Hsts]" as "Hcframe_interp"
    ; [|iDestruct "Hcframe_interp" as
        (wastk wastk1 wastk2 wastk3) "(Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hclose_res & %Hwastks & Hr & Hsts)"
      ].
    {
      destruct is_untrusted_caller; cycle 1.
      * iExists wcs2, wcs3, wret, wcgp0.
        iEval (rewrite region_open_nil) in "Hr"; iFrame "Hr Hsts".
        iDestruct "Hcframe_interp" as "($&$&$&$)".
        cbn.
        iSplit;first done.
        iPureIntro.
        repeat (split;auto).
      * iEval (rewrite region_open_nil) in "Hr".
        iDestruct (region_open_list_interp_gen _ _ (finz.seq_between a_stk (a_stk^+4)%a)
                    with "[$Hinterp_callee_wstk $Hr $Hsts]")
                    as "(Hr & Hsts & Hres)"; auto.
        { eapply finz_seq_between_NoDup. }
        { clear- Hb_a4 He_a1 ; apply Forall_forall; intros a' Ha'.
          apply elem_of_finz_seq_between in Ha'; solve_addr.
        }
        { set_solver. }
        do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
        rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
        cbn.
        replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
        replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
        cbn.
        iDestruct "Hres" as "(Hres0 & Hres1 & Hres2 & Hres3 & _)".
        iDestruct (opening_closing_resources with "Hres0") as (wastk) "[Hres0 $]".
        iDestruct (opening_closing_resources with "Hres1") as (wastk1) "[Hres1 $]".
        iDestruct (opening_closing_resources with "Hres2") as (wastk2) "[Hres2 $]".
        iDestruct (opening_closing_resources with "Hres3") as (wastk3) "[Hres3 $]".
        iFrame.
    }

    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    rewrite -/(interp_cont).
    iEval (cbn) in "Hinterp_callee_wstk".

    (* Lea ctp (-1)%Z *)
    destruct (decide (a_tstk <= (a_tstk ^+ -1))%a) as [Ha_tstk1'|Ha_tstk1'].
    {
      assert ((a_tstk + -1) = None)%a by solve_addr+Ha_tstk1'.
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (rules_Lea.wp_Lea_fail_none_z with "[HPC Hi Hctp]")
      ; try iFrame
      ; try solve_pure.
      iNext; iIntros "_".
      wp_pure; wp_end ; by iIntros (?).
    }
    assert (is_Some (a_tstk + -1))%a as [a_tstk1 Ha_tstk1] by solve_addr+Ha_tstk1'.
    clear Ha_tstk1'.
    iInstr "Hcode".
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4. }
    (* Load cgp csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.



    iDestruct (region_open_list_interp_gen _ _ (finz.seq_between (a_stk^+4)%a e_stk)
                with "[$Hinterp_callee_wstk $Hr $Hsts]")
                    as "(Hr & Hsts & Hres)"; auto.
    { eapply finz_seq_between_NoDup. }
    { clear- Hb_a4 He_a1 ; apply Forall_forall; intros a' Ha'.
      apply elem_of_finz_seq_between in Ha'.
      destruct is_untrusted_caller; solve_addr.
    }
    {
      destruct is_untrusted_caller; last set_solver.
      set (la := finz.seq_between (a_stk ^+ 4)%a e_stk).
      assert ( a_stk ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 1)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 2)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 3)%a ∉ la) by (subst la; apply not_elem_of_finz_seq_between; solve_addr+).
      do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
      rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
      replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
      replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
      set_solver.
    }

    iAssert (∃ (lv : list Word),
                ⌜ length lv = length (finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
                ∗ ▷ ([∗ list] a ; v ∈ finz.seq_between (a_stk ^+ 4)%a e_stk ; lv, closing_resources interp W C a v)
                ∗ ([∗ list] a ; v ∈ finz.seq_between (a_stk ^+ 4)%a e_stk  ; lv, a ↦ₐ v)
            )%I
             with "[Hres]"
      as (lv Hlen_lv) "[Hres Hstk]".
    {
      iClear "#"; clear.
      iStopProof.
      generalize (finz.seq_between (a_stk ^+ 4)%a e_stk).
      induction l; cbn; iIntros "Hres".
      - iExists []; cbn; done.
      - iDestruct "Hres" as "[Ha Hres]".
        iDestruct (IHl with "Hres") as (lv) "(%Hlen & Hres & Hlv)".
        iDestruct ( opening_closing_resources with "Ha" ) as (va) "[Hres_a Ha]".
        iExists (va::lv).
        iFrame.
        iPureIntro ; cbn ; lia.
    }

    iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: lv]])%I
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk]" as "Hstk".
    {
      iAssert ([[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ lv ]])%I with "[$Hstk]" as "Hstk".
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }
    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iSplitL; cycle 1.
    { iIntros "!> %"; simplify_eq. }
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode" with "Hlc".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 9 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    do 2 (rewrite (delete_commute _ _ ca2); auto).
    do 2 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca2]") as "Hrmap".
    do 2 (rewrite (delete_commute _ _ ctp); auto).
    do 3 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hctp]") as "Hrmap".

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
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 10 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    iHide "Hcode" as hcode.
    rewrite (region_addrs_zeroes_split _ (a_stk ^+ 4)%a); last solve_addr+Ha_stk4 Hb_a4 He_a1.
    rewrite (region_pointsto_split _ _ (a_stk ^+ 4)%a)
    ; [| solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
    iDestruct "Hstk" as "[Hstk_register_save Hstk]".

    set (lv' := region_addrs_zeroes (a_stk ^+ 4)%a e_stk).
    assert (Forall (λ y : Word, y = WInt 0) lv') as Hlv'.
    { subst lv'.
      rewrite /region_addrs_zeroes.
      by apply Forall_replicate.
    }

    pose proof (related_sts_pub_refl_world W) as Hpub_W.
    iSpecialize ("Hexec_topmost_frm" $! W Hpub_W).
    rewrite /interp_cont_exec.
    iEval (cbn) in "Hexec_topmost_frm".

    (* Update the call-stack: depop the topmost frame *)
    iDestruct (cstack_update _ _ cstk with "[$] [$]") as ">[Hcstk_full Hcstk_frag]".

    (* Close the switcher's invariant *)
    iDestruct (region_pointsto_cons with "[$Ha_tstk $Htstk]") as "Htstk"; [solve_addr| solve_addr| ].
    iMod ("Hclose_switcher_inv"
           with "[Hstk_interp_next $Hna $Hmtdc $Hcode $Hb_switcher Htstk $Hcstk_full $Hp_ot_switcher]")
      as "Hna".
    {
      replace (a_tstk1 ^+ 1)%a with a_tstk by solve_addr.
      replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
      iFrame.
      iNext.
      iSplit; first (iPureIntro; done).
      iSplit; first (iPureIntro; solve_addr+Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1).
      iPureIntro; solve_addr+Hbounds_tstk_b  Hlen_cstk Ha_tstk1.
    }

    destruct is_untrusted_caller; cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).
      iEval (rewrite app_nil_r) in "Hr".
      (* iAssert ([[a_stk,e_stk]] ↦ₐ [[region_addrs_zeroes a_stk e_stk%a]])%I with "[Hstk_register_save Hstk]" as "Hstk". *)
      (* { *)
      (*   rewrite (region_addrs_zeroes_split a_stk (a_stk ^+4)%a e_stk); last solve_addr+Ha_stk4 He_a1 Hb_a4. *)
      (*   rewrite region_pointsto_split; first iFrame. *)
      (*   solve_addr+Ha_stk4 He_a1 Hb_a4. *)
      (*   by rewrite /region_addrs_zeroes length_replicate. *)
      (* } *)
      iAssert (([∗ list] a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk, closing_resources interp W C a (WInt 0)))%I
        with "[Hres]" as "Hres".
      { iClear "#".
        clear -Hlen_lv.
        iStopProof.
        revert Hlen_lv.
        generalize dependent lv.
        generalize (finz.seq_between (a_stk ^+ 4)%a e_stk) as la.
        induction la; iIntros (lv Hlen) "H"; destruct lv as [|v lv]; simplify_eq; cbn; first done.
        iDestruct "H" as "[Ha H]".
        iDestruct (closing_resources_zeroed with "Ha") as "$".
        by iApply (IHla with "H").
      }

      iAssert (([∗ list] a ; v ∈ finz.seq_between (a_stk ^+ 4)%a e_stk ; lv' , closing_resources interp W C a v))%I
        with "[Hres]" as "Hres".
      { rewrite /region_pointsto.
        iApply big_sepL2_replicate_r; auto.
        by rewrite finz_seq_between_length.
      }

      iApply ("Hexec_topmost_frm" with
               "[$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hstk_register_save $Hstk $Hr $Hres $Hsts $Hcont_K $Hcstk_frag $Hna]").
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we use the IH *)

    iAssert (
        ([∗ list] a ; v ∈ finz.seq_between (a_stk ^+ 4)%a e_stk ; lv', a ↦ₐ v ∗ closing_resources interp W C a v)
      )%I with "[Hres Hstk]" as "Hres".
    { iClear "#".
      clear -Hlen_lv Hlv'.
      rewrite /region_pointsto.
      iStopProof.
      assert (length lv' = length (finz.seq_between (a_stk ^+ 4)%a e_stk)) as Hlen_lv'.
      { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      revert Hlen_lv Hlen_lv' Hlv'.
      generalize dependent lv.
      generalize dependent lv'.
      generalize (finz.seq_between (a_stk ^+ 4)%a e_stk) as la.
      induction la; iIntros (lv' lv Hlen' Hlen Hlv') "H"
      ; destruct lv as [|v lv]; simplify_eq; cbn
      ; destruct lv' as [|v' lv']; simplify_eq; cbn
      ; first done.
      iDestruct "H" as "[ [Hclose Hres] [Ha H] ]"; iFrame.
      apply Forall_cons in Hlv' ; destruct Hlv' as [-> Hlv'].
      iDestruct (closing_resources_zeroed with "Hclose") as "$".
      iApply (IHla with "[Hres H]"); last iFrame; eauto.
    }

    iDestruct (region_close_list_interp_gen with "[$Hr $Hres]") as "Hr".
    { apply finz_seq_between_NoDup. }
    { clear -He_a1 Ha_stk4.
      assert (a_stk ∉ finz.seq_between (a_stk ^+ 4)%a e_stk)
        by (by apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 1)%a ∉ finz.seq_between (a_stk ^+ 4)%a e_stk)
        by (by apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 2)%a ∉ finz.seq_between (a_stk ^+ 4)%a e_stk)
        by (by apply not_elem_of_finz_seq_between; solve_addr+).
      assert ( (a_stk ^+ 3)%a ∉ finz.seq_between (a_stk ^+ 4)%a e_stk)
        by (by apply not_elem_of_finz_seq_between; solve_addr+).
      do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
      rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
      replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
      replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
      set_solver.
    }
    { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }

    iAssert ((interp W C wastk)
              ∗ (interp W C wastk1)
              ∗ (interp W C wastk2)
              ∗ (interp W C wastk3)
            )%I with "[Hclose_res]" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
    {
      do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
      rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
      replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
      replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
      iDestruct "Hclose_res" as "(Hclose_wastk & Hclose_wastk1 & Hclose_wastk2 & Hclose_wastk3 & _)".
      iDestruct (closing_resources_interp with "Hclose_wastk") as "$".
      iDestruct (closing_resources_interp with "Hclose_wastk1") as "$".
      iDestruct (closing_resources_interp with "Hclose_wastk2") as "$".
      iDestruct (closing_resources_interp with "Hclose_wastk3") as "$".
    }


    clear lv' Hlv'.
    set (lv' := region_addrs_zeroes a_stk (a_stk ^+ 4)%a).
    assert (Forall (λ y : Word, y = WInt 0) lv') as Hlv'.
    { subst lv'.
      rewrite /region_addrs_zeroes.
      by apply Forall_replicate.
    }

    iAssert (
        ([∗ list] a ; v ∈ finz.seq_between a_stk (a_stk ^+ 4)%a ; lv', a ↦ₐ v ∗ closing_resources interp W C a v)
      )%I with "[Hclose_res Hstk_register_save]" as "Hclose_res".
    { iClear "#".
      clear -Hlv' Ha_stk4.
      rewrite /region_pointsto.
      iStopProof.
      assert (length lv' = length (finz.seq_between a_stk (a_stk ^+ 4)%a)) as Hlen_lv'.
      { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      assert (length [wastk; wastk1; wastk2; wastk3] = length (finz.seq_between a_stk (a_stk ^+ 4)%a)) as Hlen_lv.
      { cbn. rewrite finz_seq_between_length.
        do 4 (rewrite finz_dist_S; last solve_addr+Ha_stk4).
        by rewrite finz_dist_0; last solve_addr+Ha_stk4.
      }
      revert Hlen_lv' Hlen_lv Hlv'.
      generalize [wastk; wastk1; wastk2; wastk3] as lv.
      generalize dependent lv'.
      generalize (finz.seq_between a_stk (a_stk ^+ 4)%a) as la.
      induction la; iIntros (lv' lv Hlen' Hlen Hlv') "H"
      ; destruct lv as [|v lv]; simplify_eq; cbn
      ; destruct lv' as [|v' lv']; simplify_eq; cbn
      ; try done.
      iDestruct "H" as "[ [Hclose Hres] [Ha H] ]"; iFrame.
      apply Forall_cons in Hlv' ; destruct Hlv' as [-> Hlv'].
      iDestruct (closing_resources_zeroed with "Hclose") as "$".
      iApply (IHla with "[Hres H]"); last iFrame; eauto.
    }

    iEval (rewrite -(app_nil_r (finz.seq_between a_stk (a_stk ^+ 4)%a))) in "Hr".
    iDestruct (region_close_list_interp_gen with "[$Hr $Hclose_res]") as "Hr".
    { apply finz_seq_between_NoDup. }
    { set_solver. }
    { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
    rewrite -region_open_nil.


    destruct ( decide (isCorrectPC (updatePcPerm wastk2))) as [HcorrectWret|HcorrectWret]; cycle 1.
    { (* The PC is not correct, the execution will crash *)
      iApply (wp_bind (fill [SeqCtx])).
      iApply (wp_notCorrectPC with "HPC"); first done.
      iNext; iIntros "HPC /=".
      iApply wp_pure_step_later; auto; iNext; iIntros "_".
      iApply wp_value; iIntros; discriminate.
    }
    (* The PC is correct, we can use the continuation*)

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

    match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete PC m) end.
    2: { rewrite delete_notin; auto.
         apply not_elem_of_dom.
         repeat (rewrite dom_insert_L).
         rewrite Hdom_rmap' Harg_rmap'.
         set_solver+.
    }
    iDestruct (big_sepM_insert_delete with "[$Hrmap $HPC]") as "Hrmap".

    rewrite -(insert_id (<[PC:=updatePcPerm wastk2]> _) PC (updatePcPerm wastk2))
    ; last (clear;simplify_map_eq; done).
    destruct wastk2 as [ z | [p g b
                                e a|]  | p g b e a | ot sb ] ; iEval (cbn) in "Hrmap".
    all: cbn in HcorrectWret.
    all: inversion HcorrectWret; simplify_eq.
      + (* wret was a regular capability: apply the FTLR *)
        iPoseProof ( fundamental W cstk Ws Cs C (WCap p g b e a) (WCap RWL Local b_stk e_stk a_stk) Nswitcher with "Hinv_switcher Hinterp_wstk2") as "IH".
        rewrite /interp_expression /=.
        iApply ("IH" with "[- $Hr $Hsts $Hcont_K $Hna $Hcstk_frag $Hrmap]"); eauto.
        repeat iSplit;auto.
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
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          iApply "Hrmap_interp'"; eauto.
          iPureIntro.
          rewrite lookup_delete_ne; eauto.
        }
        { by iPureIntro; simplify_map_eq. }

      + (* wret was a sentry capability: apply the def of safe for sentry *)
        iAssert (interp W C (WSentry p g b e a)) as "#Hinterp_wret'" ; first done.
        iEval (rewrite fixpoint_interp1_eq /=) in "Hinterp_wstk2".
        iDestruct "Hinterp_wstk2" as "#Hinterp_wret".
        rewrite /enter_cond.
        iAssert (future_world g W W) as "-#Hfuture".
        { destruct g; cbn; iPureIntro
          ; [apply related_sts_priv_refl_world| apply related_sts_pub_refl_world].
        }
        iSpecialize ("Hinterp_wret" $! cstk Ws Cs (WCap RWL Local b_stk e_stk a_stk) W with "[$]").
        iDestruct "Hinterp_wret" as "[Hinterp_wret _]".
        iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_wret]") as ">Hinterp_wret".
        rewrite /interp_expr /=.
        iDestruct ("Hinterp_wret" with "[$Hcont_K $Hrmap $Hr $Hsts $Hcstk_frag $Hna]") as "HA"; eauto.
        iSplitR.
        { iSplit.
          - iIntros (r); iPureIntro.
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
          - iIntros (r rv HrPC Hr).
            destruct (decide (r = csp)); simplify_map_eq; first done.
            destruct (decide (r = cs1)); simplify_map_eq; first done.
            destruct (decide (r = cs0)); simplify_map_eq; first done.
            destruct (decide (r = ca1)); simplify_map_eq; first done.
            destruct (decide (r = ca0)); simplify_map_eq; first done.
            destruct (decide (r = cgp)); simplify_map_eq; first done.
            destruct (decide (r = cra)); simplify_map_eq; first done.
            iApply "Hrmap_interp'"; eauto.
            iPureIntro.
            rewrite lookup_delete_ne; eauto.
        }
        iPureIntro; simplify_map_eq; done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %cstk %Ws %Cs %regs %W' _"; iSplitL; iNext ; iApply (interp_expr_switcher_return with "Hinv").
  Qed.


End fundamental.
