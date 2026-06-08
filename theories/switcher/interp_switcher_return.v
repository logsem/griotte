From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From cap_machine Require Export logrel monotone.
From cap_machine Require Import fundamental.
From cap_machine Require Import switcher_preamble.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.
From cap_machine Require Export world_interp_stack world_ghost_theory_interface switcher_helpers.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Reg) -n> iPropO Σ).
  Implicit Types w : (leibnizO Word).
  Implicit Types interp : (V).

  (** Informal proof of the interp of the return-to-switcher entry point.
      When we call an adversary entry point, we first need to prove that it is safe (see [ot_switcher_interp]),
      which is defined by [ot_switcher_prop].
      Concretely, it means when the adversary starts the execution,
      it contains (among others) the return-to-switcher entry point,
      and so it must be safe-to-share.
      Because the entry point is a Sentry, we must prove that it is safe-to-execute.

      We initially start with a state where all the registers contain safe-to-share words,
      with a PC pointing to the the switcher's return address [a_switcher_return].
      We also have some call-stack [cstk] with the fragmental view [cstack_frag cstk].

      We extract the registers used in the code out of the map into individual resources,
      and we derive [interp] of their content
      (because safe-to-exec means that all registers are safe-to-share).
      We open the switcher's invariant, giving the points-to of the code region,
      allowing us to execute through the code.
      We obtain the authoritative view of the call-stack [cstack_full cstk'],
      which we can unify with [cstk].
      We obtain some current trusted stack address [a_tstk],
      which matches the size of the call-stack [cstk].

      To execute the code, we need to have the points-to resources of the top-most
      frame of the call stack:
      - the top-most address of the trusted stack
      - the 4 addresses of the callee-save registers area in the compartment's stack.

      We can distinguish 2 cases.
      1) The call-stack is empty.
         We know it's a case that should no be possible,
         because empty call-stack means that main tries to return,
         but it doesn't have access to the return-to-switcher.
         It's not a problem though, because the code will fail.
      2) The call-stack is not empty,
         in which case we can derive information about the top-most frame
         with [cframe_interp].

      From now, we can (again) distinguish 2 cases
      (the Rocq proof combines them with a clever way to derive the points-to resources):
      1) If the caller was untrusted, the callee-save area is owned the caller,
         and the points-to are therefore in the world.
         We know that the only (untrusted) caller being able to call an untrusted callee
         has to be itself, so we have access to the right world (for the right compartment).
         In this case, we open the world, and obtain the points-to:
         theirs values don't have to be the ones stored in the (logical) call-frame,
         but we know that they are safe values
      2) If the caller was trusted, the callee-save area is owned by the switcher,
         and we know that their content has to be the one from the (logical) call-frame.

      From that point, the proof consists on executing the code,
      up-to the final jump.
      We update the call-stack (depop the topmost stack frame),
      and we can close the switcher invariant.
      To finish the proof, we have to use a form of continuation.

      In the case of a trusted caller, we can finish the proof by using
      the continuation relation K.
      In the case of an untrusted caller, we finish by using the FTLR itself.
      We need, in particular, to close the world,
      which requires to massage the context.

   *)

  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp) W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv_switcher %cstk %Ws %Cs %rmap [[%Hfull_rmap #Hrmap_interp] (Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)]".
    rewrite /registers_pointsto.

    (* --- Extract scratch registers ct2 ctp --- *)
    cbn in Hfull_rmap.

    getRegValList [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1].
    iExtractList "Hrmap" [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["HPC";"Hcra";"Hcsp";"Hcgp";"Hca0";"Hca1";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1"].
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
    set (rmap0 := delete ct1 _).


    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.

    (* ------------------------------------------------ *)
    (* ----- Start the proof of the switcher here ----- *)
    (* ------------------------------------------------ *)

    (* Boilerplate for being able to use the automation *)
    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }
    focus_block_nochangePC 12 "Hcode" as a5 Ha5 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    assert (a5 = a_switcher_return); [|simplify_eq].
    { cbn in Ha5.
      clear -Ha5 swlayoutwf.
      pose proof switcher_return_entry_point as Hret; cbn in Hret.
      pose proof switcher_call_entry_point as Hcall; cbn in Hcall.
      solve_addr.
    }

    (* ReadSR ctp mtdc *)
    iInstr "Hcode".

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

    (* To continue the execution of the code, we need the points-to resources
       of the top-most trusted stack,
       and the poinst-to resources of the callee-save registers area in the compartment stack.
       We distinguish the case with empty-call stack and non-empty call-stack.
     *)
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

    (* Non empty call-stack *)
    destruct Ws;[done|].
    destruct Cs;[done|].
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk (%HWF & Hcframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hccrel_known_to_known & Hfreq).

    (* We derive the points-to resources of the compartment's stack.
       Ownership of the points-to depend on trusted and untrusted caller.
       To avoid having two similar proofs, we factor out those 2 cases within
       a clever existential quantifier.
     *)
    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "Hcont_K"; rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    cbn.
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".

    iDestruct (open_world_interp_cframe with "[$Hcframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3
          & Hstk'
          & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.

    (* With the points-to in hand, we can now continue the execution of the code *)
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

    iDestruct (big_sepL2_lookup_acc _ _ _ 3 (a_stk ^+3)%a wastk3 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 3 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4. }
    (* Load ca2 csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 2 (a_stk ^+2)%a wastk2 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 2 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4. }
    (* Load cs1 csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 1 (a_stk ^+1)%a wastk1 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 1 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); solve_addr. }
    (* Load cs0 csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 0 a_stk wastk with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 0 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode".
    (* GetA ct1 csp *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* Before clearing the stack, the lemma [clear_stack_spec] requires
       a specific shape for the points-to resources of the stack.
       The following massage the context for getting the points-to of the rest
       of the callee's frame out of the world, while keeping around the closing resources.
     *)
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & Hstk & Hres))"; eauto.

    iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: lv]])%I
      with "[Hstk' Hstk]" as "Hstk".
    {
      iDestruct (region_pointsto_split a_stk e_stk (a_stk^+4)%a with "[$Hstk' $Hstk]") as "H"
      ; [solve_addr+He_a1| | done].
      repeat (rewrite finz_dist_S; [|solve_addr+He_a1]).
      by rewrite finz_dist_0; [|solve_addr+He_a1].
    }

    (* We continue the execution *)
    focus_block 13 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    focus_block 14 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    subst rmap0.
    iInsertList "Hrmap" [ct0;ct1;ca2;ctp].
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

    focus_block 15 "Hcode" as a10 Ha10 "Hcode" "Hcont"; iHide "Hcont" as hcont.
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
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* The execution of the code is done, we need to finish proving the WP
       by using a continuation:
       either the continuation relation K, or safe-to-execute. *)
    iHide "Hcode" as hcode.
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

    (* We split the compartment stack frame into 2 area:
       - the one that was used for the callee-save registers
       - the callee stack frame
       We need to treat them differently because of the distinction between
       trusted and untrusted caller.
     *)
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

    destruct (is_untrusted_caller ccrel) eqn:Hccrel ; cycle 1.
    - (* Case where caller is trusted, we use the continuation relation K *)
      destruct Hwastks as (-> & -> & -> & ->).
      iEval (rewrite app_nil_r) in "Hworld_interp".

      (* We massage the context to get the necessary shape to apply the continuation relation *)
      (* iDestruct (StackOpenWorldResources_length with "Hres" ) as "%Hlen_lv". *)
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.

      iSpecialize ("Hexec_topmost_frm" $! W (related_sts_pub_refl_world W)).
      iApply ("Hexec_topmost_frm" with
               "[$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hstk_register_save $Hstk $Hworld_interp $Hres $Hcont_K $Hcstk_frag $Hna]").
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we use the IH *)

      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk $Hres]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { clear -He_a1 Ha_stk4.
        intros a Ha Ha'.
        apply elem_of_finz_seq_between in Ha, Ha'.
        solve_addr.
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
        iDestruct "Hclose_res" as "[ Hclose_res Hstates ]".
        iDestruct "Hclose_res" as "(Hclose_wastk & Hclose_wastk1 & Hclose_wastk2 & Hclose_wastk3 & _)".
        iDestruct (StackWorldResource_interp with "Hclose_wastk") as "$".
        iDestruct (StackWorldResource_interp with "Hclose_wastk1") as "$".
        iDestruct (StackWorldResource_interp with "Hclose_wastk2") as "$".
        iDestruct (StackWorldResource_interp with "Hclose_wastk3") as "$".
      }

      clear Hlen_lv' Hlv' lv'.
      set (lv' := region_addrs_zeroes a_stk (a_stk ^+ 4)%a).
      assert (Forall (λ y : Word, y = WInt 0) lv') as Hlv'.
      { subst lv'; rewrite /region_addrs_zeroes; by apply Forall_replicate. }

      iDestruct (big_sepL2_length with "Hstk_register_save") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ _ lv' with "Hclose_res") as "Hclose_res"; auto.
      iEval (rewrite -(app_nil_r (finz.seq_between a_stk (a_stk ^+ 4)%a))) in "Hworld_interp".
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk_register_save $Hclose_res]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { set_solver. }
      { subst lv'; by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      rewrite open_world_interp_empty.


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

      (* Insert the registers in the rmap *)
      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cra m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcra]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cgp m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcgp]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca0 m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete ca1 m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs0 m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs0]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete cs1 m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcs1]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete csp m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcsp]") as "Hrmap".

      match goal with | _ : _ |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => replace m with (delete PC m) end.
      2: { rewrite delete_id; auto.
           apply not_elem_of_dom.
           repeat (rewrite dom_insert_L).
           rewrite Hdom_rmap' Harg_rmap'.
           set_solver+.
      }
      iDestruct (big_sepM_insert_delete with "[$Hrmap $HPC]") as "Hrmap".

    rewrite -(insert_id (<[PC:=updatePcPerm wastk2]> _) PC (updatePcPerm wastk2))
    ; last (clear;simplify_map_eq; done).
    rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq.
    destruct wastk2 as [ z | [p g b
                                e a|]  | p g b e a | ot sb ] ; iEval (cbn) in "Hrmap".
    all: cbn in HcorrectWret.
    all: inversion HcorrectWret; simplify_eq.
      + (* wret was a regular capability: apply the FTLR *)
        iPoseProof ( fundamental W C (WCap p g b e a) with "Hinterp_wstk2") as "IH".
        rewrite /interp_expression /=.
        iApply ("IH" with "[- $Hworld_interp $Hcont_K $Hna $Hcstk_frag $Hrmap]"); eauto.
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

      + (* wret was a sentry capability: apply the def of safe for sentry *)
        iAssert (interp W C (WSentry p g b e a)) as "#Hinterp_wret'" ; first done.
        iEval (rewrite fixpoint_interp1_eq /=) in "Hinterp_wstk2".
        iDestruct "Hinterp_wstk2" as "#Hinterp_wret".
        rewrite /enter_cond.
        iAssert (future_world g W W) as "-#Hfuture".
        { destruct g; cbn; iPureIntro
          ; [apply related_sts_priv_refl_world| apply related_sts_pub_refl_world].
        }
        iSpecialize ("Hinterp_wret" $! W with "[$]").
        iSpecialize ("Hinterp_wret" $! g (LocalityFlowsToReflexive g)).
        iDestruct (lc_fupd_elim_later with "[$] [$Hinterp_wret]") as ">Hinterp_wret".
        rewrite /interp_expr /=.
        iDestruct ("Hinterp_wret" with "[$Hcont_K $Hrmap $Hworld_interp $Hcstk_frag $Hna]") as "HA"; eauto.
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
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          iApply "Hrmap_interp'"; eauto.
          iPureIntro.
          rewrite lookup_delete_ne; eauto.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv logrel_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "Hinv").
  Qed.


End fundamental.
