From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary monotone_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import map_simpl register_tactics_binary proofmode_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary switcher_helpers_binary.

(** Gets the values of the registers [rnames] in the register files of both
    runs, from their [full_map] hypotheses. *)
Ltac get_rvals_pair Hfull1 Hfull2 rnames :=
  match rnames with
  | nil => idtac
  | ?r :: ?rt =>
      let w := fresh "w" r in
      let Hw := fresh "Hw" r in
      let sw := fresh "sw" r in
      let Hsw := fresh "Hsw" r in
      destruct (Hfull1 r) as [w Hw];
      destruct (Hfull2 r) as [sw Hsw];
      get_rvals_pair Hfull1 Hfull2 rt
  end.

Section fundamental.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {relg : relGS Σ}
    {specg : specG Σ}
    {cstackg : CSTACKG Σ} {cstackg_spec : CSTACK_specG Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.

  (** The return-to-switcher entry point is safe to execute, in both runs.

      The proof follows the unary one. Both runs execute the same switcher
      code, in lockstep. Both call stacks have the same length (they are
      related position by position), so both trusted stacks have the same
      top address [a_tstk].
      The topmost pair of frames has the same caller-callee relationship and
      the same stack bounds in both runs (see [cframe_pair_cond]), so both
      runs restore the same stack pointer. The callee-saved registers are
      restored separately in each run:
      - for an untrusted caller, from the shared callee-saved area, whose
        words are related by the world; we then conclude with the FTLR;
      - for a trusted caller, from each frame; we then conclude with the
        continuation relation. *)
  Lemma interp_expr_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp_expr interp (interp_cont interp) W C
        (WCap XSRW_ Local b_switcher e_switcher a_switcher_return,
         WCap XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv_switcher %stk %Ws %Cs %rmap %smap
      (#Hspec & [%Hfull_rmap [%Hfull_smap #Hrmap_interp]] & Hrmap & Hsmap & Hj & Hworld_interp
      & Hcont_K & Hna & Hcstk & Hcstk_spec & %Hfreq)".
    rewrite /registers_pointsto /spec_registers_pointsto.
    cbn in Hfull_rmap, Hfull_smap.

    (* --- Extract the registers --- *)
    get_rvals_pair Hfull_rmap Hfull_smap [cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1].
    iExtractList "Hrmap" [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["HPC";"Hcra";"Hcsp";"Hcgp";"Hca0";"Hca1";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1"].
    iExtractList "Hsmap" [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["HsPC";"Hscra";"Hscsp";"Hscgp";"Hsca0";"Hsca1";"Hsctp";"Hsca2";"Hscs1";"Hscs0";"Hsct0";"Hsct1"].
    iEval (cbn) in "HPC". iEval (cbn) in "HsPC".
    iAssert (interp W C (wca0, swca0)) as "#Hinterp_wca0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C (wca1, swca1)) as "#Hinterp_wca1".
    { iApply "Hrmap_interp"; eauto; done. }

    (* --- Open the switcher's invariant --- *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "([Hswitcher_inv Hswitcher_inv_spec] & Hna & Hclose_switcher_inv)" ; auto.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iDestruct "Hswitcher_inv_spec"
      as (sa_tstk scstk' ststk_next)
           "(>Hsmtdc & >Hscode & >Hsb_switcher & >Hststk & >[%Hsbounds_tstk_b %Hsbounds_tstk_e]
           & >Hcstk_full_spec & >%Hslen_cstk & Hsstk_interp)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hslen_cstk Hsbounds_tstk_b Hsbounds_tstk_e.

    (* Boilerplate for being able to use the automation *)
    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    repeat (iEval (cbn [fmap list_fmap]) in "Hscode").
    repeat (iEval (cbn [concat]) in "Hscode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }
    focus_block_nochangePC_lockstep 12 "Hscode" "Hcode" as a5 Ha5 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    assert (a5 = a_switcher_return); [|simplify_eq].
    { cbn in Ha5.
      clear -Ha5 swlayoutwf.
      pose proof switcher_return_entry_point as Hret; cbn in Hret.
      pose proof switcher_call_entry_point as Hcall; cbn in Hcall.
      solve_addr.
    }

    (* ReadSR ctp mtdc *)
    iInstr_lockstep "Hscode" "Hcode".

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

    destruct stk as [|[frm1 frm2] stk]
    ; iEval (cbn) in "Hstk_interp"; iEval (cbn) in "Hsstk_interp"; cbn in Hlen_cstk.
    { (* Empty call stack: the execution fails in the implementation run *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iInstr "Hcode".
      { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ]. }
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
      (* Lea ctp (-1)%Z *)
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
    iDestruct "Hsstk_interp" as "(Hsstk_interp_next & Hscframe_interp)".
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hccrel_known_to_known & Hfreq).
    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "Hcont_K".
    iDestruct "Hcont_K" as "(Hcont_K & %Hframe_pair & Hcont_top)".
    rewrite Hccrel_known_to_known.
    iDestruct "Hcont_top" as "(#Hinterp_callee_wstk & Hexec_topmost_frm)".
    destruct (Hframe_pair (or_introl Hccrel_known_to_known)) as (Hccrel_eq & Hb_eq & Ha_eq & He_eq).
    destruct frm1 as [wret wcgp0 wcs2 wcs3 b_stk a_stk e_stk ccrel].
    destruct frm2 as [swret swcgp0 swcs2 swcs3 sb_stk sa_stk se_stk sccrel].
    cbn in Hccrel_eq, Hb_eq, Ha_eq, He_eq, Hccrel_known_to_known, Hfreq.
    subst sccrel sb_stk sa_stk se_stk.
    rewrite /cframe_interp /cframe_interp_spec.
    iEval (cbn) in "Hcframe_interp".
    iEval (cbn) in "Hscframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk (%HWF & Hcframe_interp)]".
    iDestruct "Hscframe_interp" as "[Hsa_tstk (_ & Hscframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    iEval (cbn) in "Hinterp_callee_wstk".
    rewrite /is_untrusted_caller_frm /=.

    iDestruct (open_world_interp_cframe with
                "[$Hinterp_callee_wstk $Hcframe_interp $Hscframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 & %swastk & %swastk1 & %swastk2 & %swastk3
          & Hstk' & Hsstk' & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.

    (* Load csp ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr ].

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
    iInstr_lockstep "Hscode" "Hcode".
    (* WriteSR mtdc ctp *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some (a_stk ^+ 3)%a); solve_addr+Ha_stk4.

    (* Load cgp csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 3 (a_stk ^+3)%a wastk3 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 3 4); try solve_addr+Hb_a4 Ha_stk4. }
    iDestruct (big_sepL2_lookup_acc _ _ _ 3 (a_stk ^+3)%a swastk3 with "Hsstk'") as "[Hsa Hsstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 3 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iDestruct ("Hsstk'" with "Hsa") as "Hsstk'".
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some (a_stk ^+ 2)%a); solve_addr+Ha_stk4.
    (* Load cra csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 2 (a_stk ^+2)%a wastk2 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 2 4); try solve_addr+Hb_a4 Ha_stk4. }
    iDestruct (big_sepL2_lookup_acc _ _ _ 2 (a_stk ^+2)%a swastk2 with "Hsstk'") as "[Hsa Hsstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 2 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iDestruct ("Hsstk'" with "Hsa") as "Hsstk'".
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some (a_stk ^+ 1)%a); solve_addr+Ha_stk4.
    (* Load cs1 csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 1 (a_stk ^+1)%a wastk1 with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 1 4); try solve_addr+Hb_a4 Ha_stk4. }
    iDestruct (big_sepL2_lookup_acc _ _ _ 1 (a_stk ^+1)%a swastk1 with "Hsstk'") as "[Hsa Hsstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 1 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iDestruct ("Hsstk'" with "Hsa") as "Hsstk'".
    (* Lea csp (-1)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some a_stk); solve_addr.
    (* Load cs0 csp *)
    iDestruct (big_sepL2_lookup_acc _ _ _ 0 a_stk wastk with "Hstk'") as "[Ha Hstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 0 4); try solve_addr+Hb_a4 Ha_stk4. }
    iDestruct (big_sepL2_lookup_acc _ _ _ 0 a_stk swastk with "Hsstk'") as "[Hsa Hsstk']"; auto.
    { erewrite (finz_seq_between_lookup _ _ 0 4); try solve_addr+Hb_a4 Ha_stk4. }
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    iDestruct ("Hstk'" with "Ha") as "Hstk'".
    iDestruct ("Hsstk'" with "Hsa") as "Hsstk'".
    (* GetE ct0 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    (* GetA ct1 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* Points-to predicates of the rest of the callee's stack frame *)
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & %slv & Hstk & Hsstk & Hres))"; eauto.

    iAssert ([[ a_stk , e_stk ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: lv]])%I
      with "[Hstk' Hstk]" as "Hstk".
    {
      iDestruct (region_pointsto_split a_stk e_stk (a_stk^+4)%a with "[$Hstk' $Hstk]") as "H"
      ; [solve_addr+He_a1| | done].
      repeat (rewrite finz_dist_S; [|solve_addr+He_a1]).
      by rewrite finz_dist_0; [|solve_addr+He_a1].
    }
    iAssert ([[ a_stk , e_stk ]] ↣ₐ [[swastk :: swastk1 :: swastk2 :: swastk3 :: slv]])%I
      with "[Hsstk' Hsstk]" as "Hsstk".
    {
      iDestruct (spec_region_pointsto_split a_stk e_stk (a_stk^+4)%a with "[$Hsstk' $Hsstk]") as "H"
      ; [solve_addr+He_a1| | done].
      repeat (rewrite finz_dist_S; [|solve_addr+He_a1]).
      by rewrite finz_dist_0; [|solve_addr+He_a1].
    }

    (* Clear the stack *)
    focus_block_lockstep 13 "Hscode" "Hcode" as a7 Ha7 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iApply (clear_stack_spec with
             "[ - $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct0 $Hct1 $Hsct0 $Hsct1 $Hcode $Hscode $Hstk $Hsstk]")
    ; eauto; [solve_addr|].
    iNext ; iIntros "(Hj & HPC & HsPC & Hcsp & Hscsp & Hct0 & Hct1 & Hsct0 & Hsct1 & Hcode & Hscode & Hstk & Hsstk)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* Clear the registers *)
    focus_block_lockstep 14 "Hscode" "Hcode" as a9 Ha9 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iInsertList "Hrmap" [ct0;ct1;ca2;ctp].
    iInsertListSpec "Hsmap" [ct0;ct1;ca2;ctp].
    iApply (clear_registers_post_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hrmap $Hsmap $Hcode $Hscode]")
    ; try solve_pure.
    { clear -Hfull_rmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    { clear -Hfull_smap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      apply regmap_full_dom in Hfull_smap.
      rewrite Hfull_smap.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap' arg_smap') "(%Harg_rmap' & %Harg_smap' & Hj & HPC & HsPC & Hrmap & Hsmap & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* Both register files are cleared: they are the same map *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zero]".
    iDestruct (big_sepM_sep with "Hsmap") as "[Hsmap %Hsmap_zero]".
    assert (arg_smap' = arg_rmap') as ->.
    { symmetry; apply zero_rmaps_eq; auto. by rewrite Harg_rmap' Harg_smap'. }
    clear Hsmap_zero Harg_smap'.

    focus_block_lockstep 15 "Hscode" "Hcode" as a10 Ha10 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    (* Jalr cnull cra *)
    assert (is_Some (arg_rmap' !! cnull)) as [wcnull Hcnull]
        by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first done.
    iDestruct (big_sepM_delete _ _ cnull with "Hsmap") as "[Hscnull Hsmap]"; first done.
    iInstr_spec "Hscode".
    iInstr "Hcode" with "Hlc".
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcnull]") as "Hrmap".
    iDestruct (big_sepM_insert_delete with "[$Hsmap $Hscnull]") as "Hsmap".
    pose proof (Hrmap_zero _ _ Hcnull) as Hwcnull; cbn in Hwcnull; subst wcnull.
    rewrite insert_id; last done.
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* Update both call stacks: pop the topmost frames *)
    iHide "Hcode" as hcode.
    iHide "Hscode" as hscode.
    iDestruct (cstack_update _ _ (map fst stk) with "Hcstk_full Hcstk") as ">[Hcstk_full Hcstk_frag]".
    iDestruct (cstack_update_spec _ _ (map snd stk) with "Hcstk_full_spec Hcstk_spec")
      as ">[Hcstk_full_spec Hcstk_frag_spec]".
    (* Close the switcher's invariant *)
    iDestruct (region_pointsto_cons with "[$Ha_tstk $Htstk]") as "Htstk"; [solve_addr| solve_addr| ].
    iDestruct (spec_region_pointsto_cons with "[$Hsa_tstk $Hststk]") as "Hststk"; [solve_addr| solve_addr| ].
    iMod ("Hclose_switcher_inv"
           with "[Hstk_interp_next Hsstk_interp_next $Hna $Hmtdc $Hsmtdc $Hcode $Hscode
                  $Hb_switcher $Hsb_switcher Htstk Hststk $Hcstk_full $Hcstk_full_spec $Hp_ot_switcher]")
      as "Hna".
    {
      replace (a_tstk1 ^+ 1)%a with a_tstk by solve_addr.
      replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.
      iFrame.
      iNext.
      rewrite !length_map in Hlen_cstk |- *.
      repeat iSplit; iPureIntro; try done.
      all: solve_addr+Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Ha_tstk1.
    }

    (* Split the stack frame: the callee-saved area and the callee's stack frame *)
    rewrite (region_addrs_zeroes_split _ (a_stk ^+ 4)%a); last solve_addr+Ha_stk4 Hb_a4 He_a1.
    rewrite (region_pointsto_split _ _ (a_stk ^+ 4)%a)
    ; [| solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
    rewrite (spec_region_pointsto_split _ _ (a_stk ^+ 4)%a)
    ; [| solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
    iDestruct "Hstk" as "[Hstk_register_save Hstk]".
    iDestruct "Hsstk" as "[Hsstk_register_save Hsstk]".
    set (lv' := region_addrs_zeroes (a_stk ^+ 4)%a e_stk).
    assert (Forall (λ y : Word, y = WInt 0) lv') as Hlv'.
    { subst lv'.
      rewrite /region_addrs_zeroes.
      by apply Forall_replicate.
    }

    destruct (is_untrusted_caller ccrel) eqn:Hccrel ; cycle 1.
    - (* The caller is trusted: we use the continuation relation *)
      destruct Hwastks as (-> & -> & -> & -> & -> & -> & -> & ->).
      iEval (rewrite app_nil_r) in "Hworld_interp".
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv slv lv' lv' with "Hres") as "Hres"; auto.
      iSpecialize ("Hexec_topmost_frm" $! W (related_sts_pub_refl_world W)).
      iDestruct (big_sepM_sep with "[$Hrmap $Hsmap]") as "Hrmap".
      iApply ("Hexec_topmost_frm" $! (wca0, swca0) (wca1, swca1) arg_rmap' with
               "[$Hspec $HPC $HsPC $Hcra $Hscra $Hcsp $Hscsp $Hcgp $Hscgp $Hcs0 $Hscs0 $Hcs1 $Hscs1
                 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hinterp_wca0 $Hinterp_wca1
                 $Hstk_register_save $Hsstk_register_save $Hstk $Hsstk $Hworld_interp $Hres $Hcont_K
                 $Hcstk_frag $Hcstk_frag_spec $Hj $Hna Hrmap]").
      iSplit; first (iPureIntro; rewrite Harg_rmap'; set_solver).
      iApply (big_sepM_impl with "Hrmap").
      iIntros "!> %r %w %Hr [Hr Hsr]".
      iFrame. iPureIntro. by apply (Hrmap_zero r w).

    - (* The caller is untrusted: we use the FTLR *)
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv slv lv' lv' with "Hres") as "Hres"; auto.
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk $Hsstk $Hres]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { clear -He_a1 Ha_stk4.
        intros a Ha Ha'.
        apply elem_of_finz_seq_between in Ha, Ha'.
        solve_addr.
      }
      { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }

      iAssert ((interp W C (wastk, swastk))
               ∗ (interp W C (wastk1, swastk1))
               ∗ (interp W C (wastk2, swastk2))
               ∗ (interp W C (wastk3, swastk3))
              )%I with "[Hclose_res]" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      {
        do 4 (rewrite (finz_seq_between_cons _ (a_stk ^+ 4)%a); last solve_addr+He_a1).
        rewrite (finz_seq_between_empty _ (a_stk ^+ 4)%a); last solve_addr+.
        replace ((a_stk ^+ 1) ^+ 1)%a with (a_stk ^+ 2)%a by solve_addr+Ha_stk4.
        replace ((a_stk ^+ 2) ^+ 1)%a with (a_stk ^+ 3)%a by solve_addr+Ha_stk4.
        iDestruct "Hclose_res" as "[ [_ Hclose_res] Hstates ]".
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
      iDestruct (StackOpenWorldResources_zeros _ _ _ _ _ lv' lv' with "Hclose_res") as "Hclose_res"; auto.
      iEval (rewrite -(app_nil_r (finz.seq_between a_stk (a_stk ^+ 4)%a))) in "Hworld_interp".
      iDestruct (close_world_interp_opening_resources
                  with "[$Hworld_interp $Hstk_register_save $Hsstk_register_save $Hclose_res]")
        as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { set_solver. }
      { subst lv'; by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      rewrite -open_world_interp_empty.

      (* Insert the registers in the register files *)
      iInsertList "Hrmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
      iInsertListSpec "Hsmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
      iDestruct (big_sepM_insert with "[$Hrmap $HPC]") as "Hrmap".
      { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hsmap $HsPC]") as "Hsmap".
      { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }

      iDestruct (interp_updatePcPerm with "Hinterp_wstk2") as "Hinterp_wret".
      iMod (lc_fupd_elim_later with "Hlc Hinterp_wret") as "Hinterp_wret'".
      rewrite /interp_expression /interp_expr /=.
      match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => set (rmap' := m) end.
      match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↣ᵣ w)%I ] => set (smap' := m) end.
      iApply ("Hinterp_wret'" $! stk Ws Cs rmap' smap' with "[- $Hspec $Hworld_interp $Hcont_K $Hna $Hcstk_frag $Hcstk_frag_spec $Hj]").
      rewrite /registers_pointsto /spec_registers_pointsto /rmap' /smap' !insert_insert_eq.
      iFrame "Hrmap Hsmap".
      iSplit; last (iPureIntro; rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq; done).
      iSplit; [|iSplit].
      * iIntros (r); iPureIntro.
        clear -Harg_rmap'.
        destruct (decide (r = PC)); simplify_map_eq; first done.
        destruct (decide (r = csp)); simplify_map_eq; first done.
        destruct (decide (r = cs1)); simplify_map_eq; first done.
        destruct (decide (r = cs0)); simplify_map_eq; first done.
        destruct (decide (r = ca1)); simplify_map_eq; first done.
        destruct (decide (r = ca0)); simplify_map_eq; first done.
        destruct (decide (r = cgp)); simplify_map_eq; first done.
        destruct (decide (r = cra)); simplify_map_eq; first done.
        apply elem_of_dom.
        rewrite Harg_rmap'.
        pose proof all_registers_s_correct.
        set_solver.
      * iIntros (r); iPureIntro.
        clear -Harg_rmap'.
        destruct (decide (r = PC)); simplify_map_eq; first done.
        destruct (decide (r = csp)); simplify_map_eq; first done.
        destruct (decide (r = cs1)); simplify_map_eq; first done.
        destruct (decide (r = cs0)); simplify_map_eq; first done.
        destruct (decide (r = ca1)); simplify_map_eq; first done.
        destruct (decide (r = ca0)); simplify_map_eq; first done.
        destruct (decide (r = cgp)); simplify_map_eq; first done.
        destruct (decide (r = cra)); simplify_map_eq; first done.
        apply elem_of_dom.
        rewrite Harg_rmap'.
        pose proof all_registers_s_correct.
        set_solver.
      * iIntros (r rv1 rv2 HrPC Hr1 Hr2); cbn in Hr1, Hr2.
        destruct (decide (r = csp)); simplify_map_eq.
        { iApply (interp_weakening with "[] Hinterp_callee_wstk"); auto; try solve_addr.
          iApply fundamental_ih. }
        destruct (decide (r = cs1)); simplify_map_eq; first done.
        destruct (decide (r = cs0)); simplify_map_eq; first done.
        destruct (decide (r = ca1)); simplify_map_eq; first done.
        destruct (decide (r = ca0)); simplify_map_eq; first done.
        destruct (decide (r = cgp)); simplify_map_eq; first done.
        destruct (decide (r = cra)); simplify_map_eq; first done.
        repeat match goal with H : arg_rmap' !! r = Some ?v |- _ =>
                 apply Hrmap_zero in H; cbn in H; subst v end.
        iApply interp_int.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return,
                  WSentry XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /= /interp1_pair /=.
    iSplit; first done.
    iIntros "!> %W' % %g' %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "Hinv").
  Qed.

End fundamental.
