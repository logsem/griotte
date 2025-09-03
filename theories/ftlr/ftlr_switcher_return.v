From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From cap_machine Require Export logrel.
From cap_machine.ftlr Require Import ftlr_base.
From cap_machine.rules Require Import rules_JmpCap.
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

  Notation STS := (leibnizO (STS_states * STS_rels)).
  Notation STS_STD := (leibnizO (STS_std_states Addr region_type)).
  Notation WORLD := (prodO STS_STD STS).
  Notation CSTK := (leibnizO cstack).
  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (WORLD -n> (leibnizO CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  Lemma switcher_return_ftlr (W : WORLD) (C : CmptName) (rmap : leibnizO Reg)
    (cstk : CSTK) (wstk : Word)
    (Nswitcher : namespace)
    :
    (∀ x, is_Some (rmap !! x)) ->
    rmap !! csp = Some wstk ->
    ftlr_IH -∗
    (∀ (r : RegName) (v : leibnizO Word) , ⌜r ≠ PC⌝ → ⌜rmap !! r = Some v⌝ → interp W C v) -∗
    na_inv logrel_nais Nswitcher switcher_inv -∗
    interp_continuation cstk W C -∗
    sts_full_world W C -∗
    na_own logrel_nais ⊤ -∗
    cstack_frag cstk -∗
    ([∗ map] k↦y ∈ <[PC:=WCap XSRW_ Local b_switcher e_switcher a_switcher_return]> rmap , k ↦ᵣ y) -∗
    region W C -∗
    ▷ (£ 1 -∗ WP Seq (Instr Executable) {{ v0, ⌜v0 = HaltedV⌝ → na_own logrel_nais ⊤ }}).
  Proof.
    iIntros (Hfull_rmap Hwstk) "#IH #Hrmap_interp #Hinv_switcher Hcont_K Hsts Hna Hcstk Hrmap Hr".
    iNext; iIntros "_".

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
    iInstr "Hcode".

    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.
    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    replace a_tstk with (b_trusted_stack ^+ (-1))%a by solve_addr.
    { (* the stack is empty, it will fail *)
      admit. (* Loading fails *)
    }
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp & %Ha_tstk1)".
    destruct Ha_tstk1 as [a_tstk1 Ha_tstk1].
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk Hcframe_interp]".
    destruct wstk0; try done.
    destruct sb; try done.
    destruct p; try done.
    destruct rx; try done.
    destruct w; try done.
    destruct dl; try done.
    destruct dro; try done.
    destruct g; try done.
    rename a into a_stk; rename b into b_stk; rename e into e_stk.
    iDestruct "Hcframe_interp" as "[%HWF Hcframe_interp]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    replace (a_stk ^+ -4)%a with a_stk4 by solve_addr.
    assert (is_Some (a_stk + -1)%a) as [a_stk1 Ha_stk1] by solve_addr.
    replace (a_stk ^+ -1)%a with a_stk1 by solve_addr.
    assert (is_Some (a_stk + -2)%a) as [a_stk2 Ha_stk2] by solve_addr.
    replace (a_stk ^+ -2)%a with a_stk2 by solve_addr.
    assert (is_Some (a_stk + -3)%a) as [a_stk3 Ha_stk3] by solve_addr.
    replace (a_stk ^+ -3)%a with a_stk3 by solve_addr.

    (* TODO: be clever to not repeat the proof,
       and assert
       (exists wa4,
       (if is_untrusted_caller then V(wa4) else ⌜wa4 = wcs2⌝ ) ∗
       (a_stk ^+ -4 ↦ₐ wa4)
       )
       etc
     *)
    destruct is_untrusted_caller.
    { admit. }
    iDestruct "Hcframe_interp" as "(Hstk_4 & Hstk_3 & Hstk_2 & Hstk_1)".
    destruct (decide (a_tstk < e_trusted_stack)%a) as [Htstk_ae|Htstk_ae]; cycle 1.
    { admit. (* NOTE will fail in the next upcoming instructions *) }
    (* Load csp ctp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    rewrite -/(interp_cont).
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".


    (* Lea ctp (-1)%Z *)
    iInstr "Hcode".
    (* WriteSR mtdc ctp *)
    iInstr "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    (* Load cgp csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk2); solve_addr. }
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk3); solve_addr. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk4); solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.


    set ( callee_stk_range := (finz.seq_between (a_stk ^+4)%a e_stk ) ).
    assert (Forall (fun a => (std W) !! a = Some Temporary) callee_stk_range)
      as Hcallee_stk_temporary.
    { (* I should get this from Hinterp_callee_wstk *)
      admit.
      (* apply Forall_forall. *)
      (* intros a Ha. *)
      (* eapply region_state_pub_temp; eauto. *)
      (* subst W1. *)
      (* cbn. *)
      (* destruct (decide (a ∈ a_local_args)). *)
      (* - by apply std_sta_update_multiple_lookup_in_i. *)
      (* - rewrite std_sta_update_multiple_lookup_same_i; last done. *)
      (*   rewrite frame_W_lookup_std. *)
      (*   by apply std_sta_update_multiple_lookup_in_i. *)
    }

    set ( callee_stk_range_l :=
            map (fun a => (a, RWL, interpC, Temporary)) (finz.seq_between (a_stk ^+4)%a e_stk ) ).
    iAssert ([∗ list] '(a, p, φ, _) ∈ callee_stk_range_l, rel C a p φ)%I as "Hrel_stk_callee".
    { admit. }
    iDestruct (region_open_list with "[$Hrel_stk_callee $Hr $Hsts]") as (lv) "(Hr & Hsts & Hstd & Hv & Hmono & Hφ)".
    { admit. }
    { admit. }
    { admit. }

    iAssert ([[ a_stk4 , e_stk ]] ↦ₐ [[ wcs2::wcs3::wret::wcgp0::lv ]])%I
      with "[Hstk_1 Hstk_2 Hstk_3 Hstk_4 Hv]" as "Hstk".
    { admit. }

    focus_block 7 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto.
    { solve_addr. }
    { solve_addr. }
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 8 "Hcode" as a8 Ha8 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* Mov cra ca2 *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 9 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    (* do 2 (rewrite -delete_insert_ne //). *)
    (* iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap". *)
    (* do 3 (rewrite -delete_insert_ne //). *)
    (* iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap". *)
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
    iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Harg_rmap' & Hcode)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 10 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    (* JmpCap cra *)
    iInstr "Hcode".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* TODO close the region *)

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
      clear -Hot_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1.
      repeat (iSplit ;[iPureIntro; try solve_addr|]); [|iPureIntro; try solve_addr].
      split; last solve_addr.
      admit. (* TODO is this true? *)
    }

    (* Use the continuation *)
    pose proof (related_sts_pub_refl_world W) as Hpub_W.
    iSpecialize ("Hexec_topmost_frm" $! W Hpub_W).
    rewrite /interp_cont_exec.
    iEval (cbn) in "Hexec_topmost_frm".
    iAssert ([∗ map] r↦w ∈ arg_rmap', r ↦ᵣ WInt 0)%I with "[Harg_rmap']" as "Hrmap".
    { admit. }
    iApply ("Hexec_topmost_frm" with
      "[$HPC $Hcra Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap Hr $Hsts $Hcont_K $Hcstk_frag $Hna]").
    iSplitL.
    (* TODO: I think the switcher's invariant should have (frm.(wstk) + 4);
       otherwise we can't match csp *)
    admit.
    iSplitL.
    iPureIntro.
    rewrite Harg_rmap'; set_solver.
    (* Should be done with closing the region *)
    admit.

  Admitted.


End fundamental.
