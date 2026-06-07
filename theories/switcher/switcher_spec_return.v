From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import ftlr_base interp_weakening.
From cap_machine Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation.
From cap_machine Require Export switcher switcher_preamble.
From stdpp Require Import base.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.
From cap_machine Require Export logrel_extra world_ghost_theory_interface switcher_helpers.


Section Switcher.
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
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma switcher_ret_specification_gen
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem : list Word)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    (* NOTE: there is only one side of the implication... *)
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own logrel_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hcstk & HK & Hworld_interp & Hna
    & HPC & Hclose_list_res & Hrmap & Hca0 & Hca1 & Hcsp)".

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".

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
    focus_block_nochangePC 12 "Hcode" as a_ret Ha_ret "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.
    replace a_switcher_return with a_ret by solve_addr.

    assert (is_Some (rmap !! cra)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cra as "Hcra".
    assert (is_Some (rmap !! cgp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cgp as "Hcgp".
    assert (is_Some (rmap !! ctp)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ctp as "Hctp".
    assert (is_Some (rmap !! ca2)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ca2 as "Hca2".
    assert (is_Some (rmap !! cs1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cs1 as "Hcs1".
    assert (is_Some (rmap !! cs0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" cs0 as "Hcs0".
    assert (is_Some (rmap !! ct0)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ct0 as "Hct0".
    assert (is_Some (rmap !! ct1)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ct1 as "Hct1".

    (* --- ReadSR ctp mtdc --- *)
    iInstr "Hcode"; try solve_pure.

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

    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.

    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
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
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[Ha_tstk (%HWF & Hcframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    cbn in Hcsp_sync; destruct Hcsp_sync as [ Ha He ]; simplify_eq.
    set (a_stk := (csp_b ^+ -4)%a).

    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK"; rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".

    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }

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
    iInstr "Hcode".
    replace (a_tstk ^+ -1)%a with a_tstk1 by solve_addr.

    (* --- WriteSR mtdc ctp --- *)
    iInstr "Hcode".

    (* --- Lea csp -1 --- *)
    iInstr "Hcode" with "Hlc".
    { transitivity (Some (a_stk ^+ 3)%a); subst a_stk; solve_addr+Ha_stk4. }

    set (stk_len := finz.dist (a_stk ^+ 4)%a csp_e).
    set (stk_ws := repeat (WInt 0) stk_len).
    simpl.

    (* NOTE in the case of untrusted code calling,
       it means that the addresses (astk, astk+4) are stored in the world,
       but remember that we revoked the world,
       so the callee needs to pass the revoked addresses!
     *)

    iMod (
        open_world_interp_cframe_gen with "Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* --- Load cgp csp --- *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcgp".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 2)%a); subst a_stk; solve_addr+Ha_stk4. }
    replace ((csp_b ^+ -4) ^+ 3)%a with (a_stk ^+ 3)%a by (subst a_stk; solve_addr+Ha_stk4).
    replace ((csp_b ^+ -4) ^+ 2)%a with (a_stk ^+ 2)%a by (subst a_stk; solve_addr+Ha_stk4).
    (* Load ca2 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hca2".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some (a_stk ^+ 1)%a); subst a_stk; solve_addr+Ha_stk4. }
    (* Load cs1 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs1".
    (* Lea csp (-1)%Z *)
    iInstr "Hcode".
    { by transitivity (Some a_stk); subst a_stk; solve_addr. }
    (* Load cs0 csp *)
    iInstr "Hcode".
    { split ; [ solve_pure | rewrite le_addr_withinBounds ; subst a_stk; solve_addr+Ha_stk4 Hb_a4 He_a1 ]. }
    iEval (cbn) in "Hcs0".
    (* GetE ct0 csp *)
    iInstr "Hcode" with "Hlc".
    (* GetA ct1 csp *)
    iInstr "Hcode" with "Hlc'".

    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* -------- CLEAR STACK --------- *)
    focus_block 13 "Hcode" as a7 Ha7 "Hcode" "Hcont"; iHide "Hcont" as hcont.
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

    iApply (clear_stack_spec with "[ - $HPC $Hcsp $Hct0 $Hct1 $Hcode $Hstk]"); eauto; [solve_addr|].
    iNext ; iIntros "(HPC & Hcsp & Hct0 & Hct1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcont" as "Hcode"; subst hcont.

    (* -------- CLEAR REGISTERS --------- *)
    focus_block 14 "Hcode" as a9 Ha9 "Hcode" "Hcont"; iHide "Hcont" as hcont.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct1]") as "Hrmap".
    rewrite -delete_insert_ne //.
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hct0]") as "Hrmap".
    do 2 (rewrite (delete_delete _ _ ca2); auto).
    do 2 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hca2]") as "Hrmap".
    do 2 (rewrite (delete_delete _ _ ctp); auto).
    do 3 (rewrite -delete_insert_ne //).
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hctp]") as "Hrmap".

    iApply (clear_registers_post_call_spec with "[- $HPC $Hrmap $Hcode]"); try solve_pure.
    { clear -Hrmap.
      repeat (rewrite -delete_insert_ne //).
      repeat (rewrite dom_delete_L).
      repeat (rewrite dom_insert_L).
      rewrite Hrmap.
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

    iHide "Hcode" as hcode.
    subst a_stk; set (a_stk := (csp_b ^+ -4)%a).


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


    iAssert
      ([[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]] ∗ [[a_stk4,csp_e]]↦ₐ[[region_addrs_zeroes a_stk4 csp_e]]
      )%I with "[Hstk]" as "[Hstk' Hstk]".
    {
      rewrite (region_addrs_zeroes_split _ a_stk4); last (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      rewrite (region_pointsto_split _ _ a_stk4)
      ; [| subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1 | by rewrite /region_addrs_zeroes length_replicate].
      done.
    }
    set (closing_region := finz.seq_between csp_b csp_e).


    iDestruct "Hlc" as "[Hlc Hlc'']".

    (* Fix the world! *)
    iMod (world_interp_stack_fixing with "Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''") as
      "(Hworld_interp & Hstk')"; eauto.

    iDestruct (interp_monotone with "[] [$Hinterp_callee_wstk]") as "Hinterp_callee_wstk'" ; first done.


    rewrite /is_untrusted_caller_frm /=
    ; rewrite /is_untrusted_caller_frm /= in Hframe
    ; destruct (is_untrusted_caller ccrel); cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).

      iEval (rewrite -open_world_interp_empty) in "Hworld_interp".
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between a_stk4 csp_e) []
                  with "[$Hinterp_callee_wstk' $Hworld_interp]")
        as "(Hworld_interp & (%lv & Hstk & Hres))"; auto.
      { apply finz_seq_between_NoDup. }
      { apply Forall_forall; intros y Hy.
        rewrite elem_of_finz_seq_between in Hy.
        subst a_stk.
        solve_addr+Ha_stk4 Hb_a4 He_a1 Hy.
      }
      { set_solver+. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hres]") as ">Hres".

      rewrite app_nil_r.
      replace a_stk4 with csp_b by solve_addr+Ha_stk4 Hb_a4 He_a1.
      replace csp_b with (a_stk ^+ 4)%a by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      replace ((a_stk ^+ 4) ^+ -4)%a with a_stk by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).


      iApply ("Hexec_topmost_frm" with
               "[] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hworld_interp $Hstk $Hstk' $Hres $Hcont_K $Hcstk_frag $Hna]"); first done.
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we use the IH *)

      iDestruct "Hinterp_wfrm" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      iClear "Hexec_topmost_frm".

      iDestruct (jmp_or_fail_spec with "[$Hinterp_wstk2]") as "Hcont".
      destruct (decide (isCorrectPC (updatePcPerm wastk2))); cycle 1.
      { by iApply "Hcont"; iFrame. }

      iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zeroes]".
      iDestruct (big_sepM_insert with "[$Hrmap $Hca0]") as "Hrmap".
      { apply not_elem_of_dom; rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hca1]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcs0]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcs1]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcgp]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcra]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      iDestruct (big_sepM_insert with "[$Hrmap $Hcsp]") as "Hrmap".
      { apply not_elem_of_dom; repeat (rewrite dom_insert_L); rewrite Harg_rmap'; set_solver+. }
      set (regs := <[csp := _]> _ ).
      set (regs' := <[PC := WInt 0]> regs).

      iDestruct "Hcont" as "(%&%&%&%&%&Hcont)".
      iDestruct "Hcont" as "(%Hwastk & #Hcont)".
      iAssert (future_world g Wfixed Wfixed) as "Hfuture".
      { destruct g; cbn; iPureIntro; [ apply  related_sts_priv_refl_world
                                     | apply related_sts_pub_refl_world].
      }
      iSpecialize ("Hcont" $! Wfixed with "Hfuture").
      iDestruct "Hlc" as "[Hlc _]"
      ; iDestruct (lc_fupd_elim_later with "[$] [$Hcont]") as ">Hcont'".

      iApply ("Hcont'" $! cstk Ws Cs regs'); iFrame.

      iSplit.
      { iSplit.
        + iIntros (r); iPureIntro.
          rewrite -elem_of_dom.
          subst regs regs'.
          repeat (rewrite dom_insert_L).
          rewrite Harg_rmap'.
          set_solver+.
        + iIntros (r v) "%HrPC %Hr".
          subst regs' regs.
          clear -Hr HrPC Hrmap_zeroes.
          simplify_map_eq.
          destruct (decide (r = csp)); simplify_map_eq; first done.
          destruct (decide (r = cra)); simplify_map_eq; first done.
          destruct (decide (r = cgp)); simplify_map_eq; first done.
          destruct (decide (r = cs1)); simplify_map_eq; first done.
          destruct (decide (r = cs0)); simplify_map_eq; first done.
          destruct (decide (r = ca1)); simplify_map_eq; first done.
          destruct (decide (r = ca0)); simplify_map_eq; first done.
          eapply map_Forall_lookup_1 in Hr; eauto; cbn in Hr; simplify_eq.
          iApply interp_int.
      }
      iSplit.
      {  rewrite /registers_pointsto.
         subst regs'.
         rewrite insert_insert_eq.
         iApply big_sepM_insert; last iFrame.
         subst regs.
         simplify_map_eq.
         rewrite -not_elem_of_dom Harg_rmap'.
         set_solver+.
      }
      iPureIntro; eapply frame_match_mono; eauto.
      Unshelve. all: exact Wcur.
  Qed.

  Lemma switcher_ret_specification
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : Reg)
    (csp_e csp_b: Addr)
    (l : list Addr)
    (stk_mem : list Word)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : Word)
    :
    let Wfixed := (close_list (l ++ finz.seq_between csp_b csp_e) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ PC ; csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ finz.seq_between csp_b csp_e) ->
    (∀ a : finz MemNum, std W0 !! a = Some Temporary -> a ∈ l ++ finz.seq_between csp_b csp_e) ->

    (* Switcher Invariant *)
    na_inv logrel_nais Nswitcher switcher_inv
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own logrel_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources W0 C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hcstk & HK & Hworld_interp & Hna
    & HPC & Hclose_list_res & Hrmap & Hca0 & Hca1 & Hcsp)".
    iApply switcher_ret_specification_gen; eauto.
    iFrame "∗#".
    iApply close_list_resources_gen_eq; eauto.
    rewrite /close_list_resources /close_addr_resources /RevokedResources.
    iApply (big_sepL_impl with "Hclose_list_res").
    iModIntro; iIntros (k ka Hka) "(%pa & %Pa & $ & $ & (%va & ($ & $ & $ & ?)))".
    by rewrite mono_temporary_eq.
  Qed.

End Switcher.
