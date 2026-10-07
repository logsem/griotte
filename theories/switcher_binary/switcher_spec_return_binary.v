From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import sts_multiple_updates.
From griotte Require Import ftlr_base_binary interp_weakening_binary.
From griotte Require Import logrel_binary fundamental_binary memory_region memory_region_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Export switcher switcher_preamble_binary.
From stdpp Require Import base.
From griotte Require Import map_simpl register_tactics_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary switcher_helpers_binary.
From griotte Require Import interp_switcher_return_binary.

Section Switcher.
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

  (** Specification of the return-to-switcher routine, for a trusted callee
      returning in both runs (lockstep). Both runs return with the same stack
      pointer: the callee was given the same stack frame in both runs. The
      return values are related, and the stack contents may differ. *)
  Lemma switcher_ret_specification_gen
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap smap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem stk_mem_spec : list Word)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word * Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    dom smap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs stk W0 C ->
    csp_sync stk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ [[csp_b,csp_e]]↣ₐ[[stk_mem_spec]]
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ([∗ map] k↦y ∈ smap, k ↣ᵣ y)
    ∗ ca0 ↦ᵣ wca0.1
    ∗ ca0 ↣ᵣ wca0.2
    ∗ ca1 ↦ᵣ wca1.1
    ∗ ca1 ↣ᵣ wca1.2
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hsmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hspec & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hsstk
       & Hcstk & Hcstk_spec & HK & Hworld_interp & Hna & Hj
       & HPC & HsPC & Hclose_list_res & Hrmap & Hsmap & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp)".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "([Hswitcher_inv Hswitcher_inv_spec] & Hna & Hclose_switcher_inv)" ; auto.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iDestruct "Hswitcher_inv_spec"
      as (sa_tstk scstk' ststk_next)
           "(>Hsmtdc & >Hscode & >Hsb_switcher & >Hststk & >[%Hsbounds_tstk_b %Hsbounds_tstk_e]
           & >Hcstk_full_spec & >%Hslen_cstk & Hsstk_interp)".
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hslen_cstk Hsbounds_tstk_b Hsbounds_tstk_e.

    set (Hret := switcher_return_entry_point).
    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    rewrite {2}/switcher_instrs.
    assert (SubBounds b_switcher e_switcher a_switcher_return (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    codefrag_facts "Hcode".
    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    repeat (iEval (cbn [fmap list_fmap]) in "Hscode").
    repeat (iEval (cbn [concat]) in "Hscode").
    focus_block_nochangePC_lockstep 12 "Hscode" "Hcode" as a_ret Ha_ret "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    replace a_switcher_return with a_ret by solve_addr.

    assert (is_Some (rmap !! cra)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cgp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ctp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ca2)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cs1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! cs0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ct0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    assert (is_Some (rmap !! ct1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtractList "Hrmap" [cra;cgp;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["Hcra";"Hcgp";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1"].
    assert (is_Some (smap !! cra)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cgp)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ctp)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ca2)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cs1)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! cs0)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ct0)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    assert (is_Some (smap !! ct1)) as [??];[apply elem_of_dom;rewrite Hsmap;set_solver-|].
    iExtractList "Hsmap" [cra;cgp;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["Hscra";"Hscgp";"Hsctp";"Hsca2";"Hscs1";"Hscs0";"Hsct0";"Hsct1"].

    (* --- ReadSR ctp mtdc --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Load csp ctp --- *)
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
    { (* no caller, return subroutine fails *)
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

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    iDestruct "Hsstk_interp" as "(Hsstk_interp_next & Hscframe_interp)".
    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK".
    iDestruct "HK" as "(Hcont_K & %Hframe_pair & HK)".
    rewrite Hccrel_known_to_known.
    iDestruct "HK" as "(#Hinterp_callee_wstk & Hexec_topmost_frm)".
    destruct (Hframe_pair (or_introl Hccrel_known_to_known)) as (Hccrel_eq & Hb_eq & Ha_eq & He_eq).
    destruct frm1 as [wret wcgp0 wcs2 wcs3 b_stk a_stk' e_stk ccrel].
    destruct frm2 as [swret swcgp0 swcs2 swcs3 sb_stk sa_stk se_stk sccrel].
    cbn in Hccrel_eq, Hb_eq, Ha_eq, He_eq, Hccrel_known_to_known, Hframe, Hcsp_sync.
    subst sccrel sb_stk sa_stk se_stk.
    destruct Hcsp_sync as (Ha & He & _ & _); simplify_eq.
    rewrite /cframe_interp /cframe_interp_spec.
    iEval (cbn) in "Hcframe_interp".
    iEval (cbn) in "Hscframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk (%HWF & Hcframe_interp)]".
    iDestruct "Hscframe_interp" as "[Hsa_tstk (_ & Hscframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    set (a_stk := (csp_b ^+ -4)%a).
    iEval (cbn) in "Hinterp_callee_wstk".
    rewrite /is_untrusted_caller_frm /=.

    (* --- Load csp ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; rewrite /withinBounds; solve_addr.

    (* --- Lea ctp -1 --- *)
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
    iInstr_lockstep "Hscode" "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Lea csp -1 --- *)
    iInstr_spec "Hscode".
    { transitivity (Some (a_stk ^+ 3)%a); subst a_stk; solve_addr+Ha_stk4. }
    (* --- Lea csp -1 --- *)
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (a_stk ^+ 3)%a); subst a_stk; solve_addr+Ha_stk4. }

    iMod (open_world_interp_cframe_gen
           with "Hinterp_callee_wstk Hcframe_interp Hscframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 & %swastk & %swastk1 & %swastk2 & %swastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hsa_stk & Hsa_stk1 & Hsa_stk2 & Hsa_stk3
            & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* --- Load cgp csp --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    (* --- Lea csp (-1)%Z --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some (a_stk ^+ 2)%a); subst a_stk; solve_addr+Ha_stk4.
    replace ((csp_b ^+ -4) ^+ 3)%a with (a_stk ^+ 3)%a by (subst a_stk; solve_addr+Ha_stk4).
    replace ((csp_b ^+ -4) ^+ 2)%a with (a_stk ^+ 2)%a by (subst a_stk; solve_addr+Ha_stk4).
    (* --- Load cra csp --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    (* --- Lea csp (-1)%Z --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some (a_stk ^+ 1)%a); subst a_stk; solve_addr+Ha_stk4.
    (* --- Load cs1 csp --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    (* --- Lea csp (-1)%Z --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: by transitivity (Some a_stk); subst a_stk; solve_addr.
    (* --- Load cs0 csp --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ].
    (* --- GetE ct0 csp --- *)
    iInstr_spec "Hscode".
    (* --- GetE ct0 csp --- *)
    iInstr "Hcode" with "Hlc".
    (* --- GetA ct1 csp --- *)
    iInstr_spec "Hscode".
    (* --- GetA ct1 csp --- *)
    iInstr "Hcode" with "Hlc'".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* -------- CLEAR STACK --------- *)
    focus_block_lockstep 13 "Hscode" "Hcode" as a7 Ha7 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iAssert ([[ a_stk , csp_e ]] ↦ₐ [[wastk :: wastk1 :: wastk2 :: wastk3 :: stk_mem]])%I
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hstk]" as "Hstk".
    {
      iAssert ([[ (a_stk ^+ 4)%a , csp_e ]] ↦ₐ [[ stk_mem ]])%I with "[Hstk]" as "Hstk".
      { replace (a_stk ^+ 4)%a with csp_b; first done. subst a_stk;solve_addr+Ha_stk4. }
      subst a_stk.
      iDestruct (region_pointsto_cons with "[$Ha_stk3 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk2 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk1 $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (region_pointsto_cons with "[$Ha_stk $Hstk]") as "Hstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }
    iAssert ([[ a_stk , csp_e ]] ↣ₐ [[swastk :: swastk1 :: swastk2 :: swastk3 :: stk_mem_spec]])%I
      with "[Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3 Hsstk]" as "Hsstk".
    {
      iAssert ([[ (a_stk ^+ 4)%a , csp_e ]] ↣ₐ [[ stk_mem_spec ]])%I with "[Hsstk]" as "Hsstk".
      { replace (a_stk ^+ 4)%a with csp_b; first done. subst a_stk;solve_addr+Ha_stk4. }
      subst a_stk.
      iDestruct (spec_region_pointsto_cons with "[$Hsa_stk3 $Hsstk]") as "Hsstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (spec_region_pointsto_cons with "[$Hsa_stk2 $Hsstk]") as "Hsstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (spec_region_pointsto_cons with "[$Hsa_stk1 $Hsstk]") as "Hsstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iDestruct (spec_region_pointsto_cons with "[$Hsa_stk $Hsstk]") as "Hsstk"; [solve_addr+Ha_stk4|solve_addr+He_a1|].
      iFrame.
    }

    iApply (clear_stack_spec with
             "[ - $Hspec $Hj $HPC $HsPC $Hcsp $Hscsp $Hct0 $Hct1 $Hsct0 $Hsct1 $Hcode $Hscode $Hstk $Hsstk]")
    ; eauto; [solve_addr|].
    iNext ; iIntros "(Hj & HPC & HsPC & Hcsp & Hscsp & Hct0 & Hct1 & Hsct0 & Hsct1 & Hcode & Hscode & Hstk & Hsstk)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    (* -------- CLEAR REGISTERS --------- *)
    focus_block_lockstep 14 "Hscode" "Hcode" as a9 Ha9 "Hscode" "Hscont" "Hcode" "Hcont".
    iHide "Hcont" as hcont. iHide "Hscont" as hscont.
    iInsertList "Hrmap" [ct1;ct0;ca2;ctp].
    iInsertListSpec "Hsmap" [ct1;ct0;ca2;ctp].
    iApply (clear_registers_post_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hrmap $Hsmap $Hcode $Hscode]")
    ; try solve_pure.
    { clear -Hrmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      rewrite Hrmap.
      set_solver.
    }
    { clear -Hsmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      rewrite Hsmap.
      set_solver.
    }
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap' arg_smap')
      "(%Harg_rmap' & %Harg_smap' & Hj & HPC & HsPC & Hrmap & Hsmap & Hcode & Hscode)".
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
    assert (is_Some (arg_rmap' !! cnull)) as [wcnull Hcnull]
        by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first done.
    iDestruct (big_sepM_delete _ _ cnull with "Hsmap") as "[Hscnull Hsmap]"; first done.
    (* --- Jalr cnull cra --- *)
    iInstr_spec "Hscode".
    (* --- Jalr cnull cra --- *)
    iInstr "Hcode" with "Hlc_jalr".
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcnull]") as "Hrmap".
    iDestruct (big_sepM_insert_delete with "[$Hsmap $Hscnull]") as "Hsmap".
    pose proof (Hrmap_zero _ _ Hcnull) as Hwcnull; cbn in Hwcnull; subst wcnull.
    rewrite insert_id; last done.
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscont" "Hcode" "Hcont" as "Hscode" "Hcode".

    iHide "Hcode" as hcode.
    iHide "Hscode" as hscode.

    (* Update both call stacks: pop the topmost frames *)
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

    iAssert
      ([[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]
       ∗ [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]]
      )%I with "[Hstk]" as "[Hstk' Hstk]".
    {
      rewrite (region_addrs_zeroes_split _ a_stk4); last (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      rewrite (region_pointsto_split _ _ a_stk4)
      ; [| subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
      done.
    }
    iAssert
      ([[a_stk,a_stk4]]↣ₐ[[region_addrs_zeroes a_stk a_stk4]]
       ∗ [[a_stk4,csp_e]]↣ₐ[[region_addrs_zeroes a_stk4 csp_e]]
      )%I with "[Hsstk]" as "[Hsstk' Hsstk]".
    {
      rewrite (region_addrs_zeroes_split _ a_stk4); last (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      rewrite (spec_region_pointsto_split _ _ a_stk4)
      ; [| subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
      done.
    }

    (* Fix the world *)
    iMod (world_interp_stack_fixing
           with "Hinterp_callee_wstk Hworld_interp Hstk' Hsstk' Hstk Hsstk Hrevoked Hlc'") as
      "(Hworld_interp & Hstk')"; eauto.

    iDestruct (interp_monotone with "[] [$Hinterp_callee_wstk]") as "Hinterp_callee_wstk'" ; first done.

    rewrite /is_untrusted_caller_frm /=
    ; rewrite /is_untrusted_caller_frm /= in Hframe
    ; destruct (is_untrusted_caller ccrel); cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & -> & -> & -> & -> & ->).
      iDestruct "Hstk'" as "[Hstk' Hsstk']".

      iEval (rewrite open_world_interp_empty) in "Hworld_interp".
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a_stk4 csp_e) []
                  with "[$Hinterp_callee_wstk' $Hworld_interp]")
        as "(Hworld_interp & (%lv & %slv & Hstk & Hsstk & Hres))"; auto.
      { apply finz_seq_between_NoDup. }
      { apply Forall_forall; intros y Hy.
        rewrite elem_of_finz_seq_between in Hy.
        subst a_stk.
        solve_addr+Ha_stk4 Hb_a4 He_a1 Hy.
      }
      { set_solver+. }
      iMod (lc_fupd_elim_later with "Hlc_jalr Hres") as "Hres".

      rewrite app_nil_r.
      replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
      replace csp_b with (a_stk ^+ 4)%a by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      replace ((a_stk ^+ 4) ^+ -4)%a with a_stk by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).

      iDestruct (big_sepM_sep with "[$Hrmap $Hsmap]") as "Hrmap".
      iApply ("Hexec_topmost_frm" $! Wfixed _ wca0 wca1 arg_rmap' with
               "[$Hspec $HPC $HsPC $Hcra $Hscra $Hcsp $Hscsp $Hcgp $Hscgp $Hcs0 $Hscs0 $Hcs1 $Hscs1
                 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
                 $Hworld_interp $Hstk $Hsstk $Hstk' $Hsstk' $Hres $Hcont_K $Hcstk_frag $Hcstk_frag_spec
                 $Hj $Hna Hrmap]").
      iSplit; first (iPureIntro; rewrite Harg_rmap'; set_solver).
      iApply (big_sepM_impl with "Hrmap").
      iIntros "!> %r %w %Hr [Hr Hsr]".
      iFrame. iPureIntro. by apply (Hrmap_zero r w).
      Unshelve. done.

    - (* Case where caller is untrusted, we use the FTLR *)
      iDestruct "Hinterp_wfrm" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      iClear "Hexec_topmost_frm".

      iInsertList "Hrmap" [ca0;ca1;cs0;cs1;cgp;cra;csp].
      iInsertListSpec "Hsmap" [ca0;ca1;cs0;cs1;cgp;cra;csp].
      iDestruct (big_sepM_insert with "[$Hrmap $HPC]") as "Hrmap".
      { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hsmap $HsPC]") as "Hsmap".
      { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }

      iDestruct (interp_updatePcPerm with "Hinterp_wstk2") as "Hinterp_wret".
      iMod (lc_fupd_elim_later with "Hlc_jalr Hinterp_wret") as "Hinterp_wret'".
      rewrite /interp_expression /interp_expr /=.
      match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => set (rmap' := m) end.
      match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↣ᵣ w)%I ] => set (smap' := m) end.
      iApply ("Hinterp_wret'" $! stk Ws Cs rmap' smap'
               with "[- $Hspec $Hworld_interp $Hcont_K $Hna $Hcstk_frag $Hcstk_frag_spec $Hj]").
      rewrite /registers_pointsto /spec_registers_pointsto /rmap' /smap' !insert_insert_eq.
      iFrame "Hrmap Hsmap".
      iSplit; last (iPureIntro; eapply frame_match_mono; eauto).
      iSplit; [|iSplit].
      * iIntros (r); iPureIntro.
        rewrite -elem_of_dom.
        repeat (rewrite dom_insert_L).
        rewrite Harg_rmap'.
        pose proof all_registers_s_correct.
        set_solver.
      * iIntros (r); iPureIntro.
        rewrite -elem_of_dom.
        repeat (rewrite dom_insert_L).
        rewrite Harg_rmap'.
        pose proof all_registers_s_correct.
        set_solver.
      * iIntros (r rv1 rv2 HrPC Hr1 Hr2); cbn in Hr1, Hr2.
        destruct (decide (r = csp)); simplify_map_eq.
        { iApply (interp_weakening with "[] Hinterp_callee_wstk'"); auto; try solve_addr.
          iApply fundamental_ih. }
        destruct (decide (r = cra)); simplify_map_eq; first done.
        destruct (decide (r = cgp)); simplify_map_eq; first done.
        destruct (decide (r = cs1)); simplify_map_eq; first done.
        destruct (decide (r = cs0)); simplify_map_eq; first done.
        destruct (decide (r = ca1)); simplify_map_eq; first (by destruct wca1).
        destruct (decide (r = ca0)); simplify_map_eq; first (by destruct wca0).
        repeat match goal with H : arg_rmap' !! r = Some ?v |- _ =>
                 apply Hrmap_zero in H; cbn in H; subst v end.
        iApply interp_int.
  Qed.

  Lemma switcher_ret_specification
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap smap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem stk_mem_spec : list Word)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word * Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    dom smap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs stk W0 C ->
    csp_sync stk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ [[csp_b,csp_e]]↣ₐ[[stk_mem_spec]]
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources W0 C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ([∗ map] k↦y ∈ smap, k ↣ᵣ y)
    ∗ ca0 ↦ᵣ wca0.1
    ∗ ca0 ↣ᵣ wca0.2
    ∗ ca1 ↦ᵣ wca1.1
    ∗ ca1 ↣ᵣ wca1.2
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ∗ csp ↣ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hsmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hspec & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hsstk
       & Hcstk & Hcstk_spec & HK & Hworld_interp & Hna & Hj
       & HPC & HsPC & Hclose_list_res & Hrmap & Hsmap & Hca0 & Hsca0 & Hca1 & Hsca1 & Hcsp & Hscsp)".
    iApply (switcher_ret_specification_gen _ _ _ _ rmap smap); eauto.
    iFrame "∗#".
    iApply close_list_resources_gen_eq; eauto.
    rewrite /close_list_resources /close_addr_resources /RevokedResources.
    iApply (big_sepL_impl with "Hclose_list_res").
    iModIntro; iIntros (k ka Hka) "(%pa & %Pa & $ & $ & (%va & ($ & $ & $ & $ & ?)))".
    by rewrite mono_temporary_eq.
  Qed.

End Switcher.
