From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_return_states switcher_return_blocks_1 switcher_return_blocks_2.
From stdpp Require Import base.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
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
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ close_list_resources_gen C Wcur (l ++ finz.seq_between csp_b csp_e) l false
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - when the call-stack is empty: [switcher_return_blocks_1_empty_spec];
       - [switcher_return_blocks_1_spec]: pop the trusted stack;
       - [open_world_interp_cframe_gen]: obtain the callee-save area;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant and fix the world
         ([world_interp_stack_fixing]);
       - when the caller is trusted, use the continuation;
       - when the caller is untrusted, [switcher_jump_to_caller_spec]. *)
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hcstk & HK & Hworld_interp & Hna
    & HPC & Hclose_list_res & Hrmap & Hca0 & Hca1 & Hcsp)".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

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

    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.
    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    { (* No caller: the return fails *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iMod "Hstk_interp".
      iApply (switcher_return_blocks_1_empty_spec with
        "[$HPC $Hctp $Hcsp $Hmtdc $Hstk_interp $Hcode]").
    }

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[>Ha_tstk (>%HWF & Hcframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    cbn in Hcsp_sync; destruct Hcsp_sync as [ Ha He ]; simplify_eq.
    set (a_stk := (csp_b ^+ -4)%a).
    pose proof (switcher_stk_bounds_frame b_stk csp_e a_stk Hb_a4 He_a1 (ex_intro _ _ Ha_stk4))
      as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).

    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK"; rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".

    (* Block 12: pop the trusted stack *)
    iApply (switcher_return_blocks_1_spec with
      "[- $HPC $Hctp $Hcsp $Hmtdc $Ha_tstk $Hcode]"); [done|done|].
    iNext; iIntros (a_tstk1)
      "(%Ha_tstk1 & %Htstk_ae & HPC & Hctp & Hcsp & Hmtdc & Ha_tstk & Hcode & Hlc)".

    (* Obtain the callee-save area *)
    iMod (
        open_world_interp_cframe_gen with "Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* Blocks 12-15: restore, clear and return *)
    assert (csp_b = (a_stk ^+ 4)%a) as Hcsp_b by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite {1}Hcsp_b) in "Hstk".
    iApply (switcher_return_blocks_2_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hstk $Hrmap $Hcode]"); first done.
    { repeat (rewrite dom_delete_L). rewrite Hrmap. set_solver. }
    iNext; iIntros (arg_rmap')
      "(%Harg_rmap' & HPC & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & Hcode & Hlc)".
    iDestruct "Hlc" as "(Hlc & Hlc'' & _)".
    assert ((a_stk ^+ 4)%a = a_stk4) as Ha_stk4_eq by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite Ha_stk4_eq) in "Hstk' Hstk".

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

    (* Fix the world *)
    iMod (world_interp_stack_fixing with "Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''") as
      "(Hworld_interp & Hstk')"; eauto.

    iDestruct (interp_monotone with "[] [$Hinterp_callee_wstk]") as "Hinterp_callee_wstk'" ; first done.

    rewrite /is_untrusted_caller_frm /=
    ; rewrite /is_untrusted_caller_frm /= in Hframe
    ; destruct (is_untrusted_caller ccrel); cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).

      iEval (rewrite open_world_interp_empty) in "Hworld_interp".
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
      replace a_stk4 with (a_stk ^+ 4)%a by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).
      replace ((a_stk ^+ 4) ^+ -4)%a with a_stk by (subst a_stk ; solve_addr+Ha_stk4 Hb_a4 He_a1).

      iApply ("Hexec_topmost_frm" with
               "[] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hworld_interp $Hstk $Hstk' $Hres $Hcont_K $Hcstk_frag $Hna]"); first done.
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we jump to the return address *)
      iDestruct "Hinterp_wfrm" as "#(Hinterp_wstk0 & Hinterp_wstk1 & Hinterp_wstk2 & Hinterp_wstk3)".
      iApply (switcher_jump_to_caller_spec with
               "Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk'
                Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 HPC Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap Hworld_interp Hcont_K Hcstk_frag Hna Hlc"); first done.
      eapply frame_match_mono; eauto.
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
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources W0 C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
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
