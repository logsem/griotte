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
From griotte Require Import switcher_load_spec switcher_exception_stub.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG LAddr region_type OType LWord Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).

  Lemma switcher_ret_specification
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 : LWord)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    (* NOTE: there is only one side of the implication... *)
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv
    ∗ switcher_static
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ [[csp_b,csp_e]]↦ₐ[[stk_mem]]
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own cerise_nais ⊤
    ∗ PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ RevokedResources Wfixed C l
    ∗ ([∗ map] k↦y ∈ rmap, k ↦ᵣ y)
    ∗ ca0 ↦ᵣ wca0
    ∗ ca1 ↦ᵣ wca1
    ∗ csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - when the frame to pop is the entry frame, the thread exits:
         [switcher_return_blocks_1_exit_spec];
       - [switcher_return_blocks_1_spec]: pop the trusted stack;
       - [open_world_interp_cframe_gen]: obtain the callee-save area;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant and fix the world
         ([world_interp_stack_fixing]);
       - when the caller is trusted, use the continuation;
       - when the caller is untrusted, [switcher_jump_to_caller_cases_spec]. *)
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "(#Hswitcher & #Hstatic & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hcstk & HK & Hworld_interp & Hna
    & HPC & Hclose_list_res & Hrmap & Hca0 & Hca1 & Hcsp)".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe with "[$Hswitcher $Hstatic]") as "#Htrap".

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
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
    assert (is_Some (rmap !! ct2)) as [??];[apply elem_of_dom;rewrite Hrmap;set_solver-|].
    iExtract "Hrmap" ct2 as "Hct2".

    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.
    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    { (* No caller: the frame to pop is the entry frame, the thread exits *)
      iApply (switcher_return_blocks_1_exit_spec with
        "[$HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hcode
          Hna Hclose_switcher_inv Hsave_area HthreadID Htstk Hcstk_full Hstk_interp]").
      iIntros "!> [Hmtdc Hframeoffset]".
      subst hclose_switcher_inv.
      iMod ("Hclose_switcher_inv" with
             "[$Hna Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp]") as "Hna".
      { iNext. iExists a_tstk, [], save_area, tstk_next. iFrame "∗ # %". }
      iModIntro; iIntros (_); iFrame.
    }

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(>Ha_tstk & >[%wtbl Ha_tstk_tbl] & >[%wcnt Ha_tstk_cnt]
                                    & >%HWF & Hcframe_interp)".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4] & Hstk_mmio & Hstk_heap & Hret_ok).
    cbn in Hcsp_sync; destruct Hcsp_sync as [ Ha He ]; simplify_eq.
    set (a_stk := (csp_b ^+ -4)%a).
    pose proof (switcher_stk_bounds_frame b_stk csp_e a_stk Hb_a4 He_a1 (ex_intro _ _ Ha_stk4))
      as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).

    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK"; rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iDestruct "Hinterp_callee_wstk" as "[%Hstk_nonheap #Hinterp_callee_wstk]".
    assert (is_heap_address b_stk = false) as Hstk_base_nonheap.
    { eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      rewrite /withinBounds; solve_addr. }

    (* Block 13: pop the trusted stack *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iApply (switcher_return_blocks_1_spec with
      "[- $HPC $Hctp $Hct0 $Hct1 $Hct2 $Hcsp $Hmtdc $Hframeoffset $Ha_tstk $Hcode]");
      [done|done|done|done|].
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Ha_tstk
                    & _ & Hlc)".
    iInsertRegs "Hrmap" ["Hct2"].

    (* Obtain the callee-save area *)
    iMod (
        open_world_interp_cframe_gen with "Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* Blocks 13-16: restore, clear and return *)
    assert (csp_b = (a_stk ^+ 4)%a) as Hcsp_b by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite {1}Hcsp_b) in "Hstk".
    iEval (rewrite open_world_interp_empty) in "Hworld_interp".
    iAssert (switcher_stk_cells a_stk wastk wastk1 wastk2 wastk3)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply (switcher_return_blocks_2_world_spec Wcur Wfixed C [] ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hworld_interp $Hrmap $Hcode]"); [|done|done| |].
    { subst Wfixed. by rewrite close_list_heap. }
    { rewrite dom_insert_L. repeat (rewrite dom_delete_L). rewrite Hrmap. set_solver. }
    iSplitR.
    { destruct (is_untrusted_caller ccrel); last done.
      iDestruct "Hinterp_wfrm" as "(Hw0 & Hw1 & Hw2 & Hw3)".
      iFrame "Hw3 Hw2 Hw1 Hw0". }
    iNext; iIntros (arg_rmap' rstk3 rstk2 rstk1 rstk0)
      "((%Hr3 & %Hr2 & %Hr1 & %Hr0) & Hworld_interp & Hinterp_loaded & %Harg_rmap'
      & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & _ & Hlc)".
    iEval (rewrite -open_world_interp_empty) in "Hworld_interp".
    iDestruct "Hlc" as "(Hlc & Hlc'')".
    assert ((a_stk ^+ 4)%a = a_stk4) as Ha_stk4_eq by (subst a_stk; solve_addr+Ha_stk4).
    iEval (rewrite Ha_stk4_eq) in "Hstk' Hstk".

    (* Depop the topmost frame of the call-stack, close the switcher's
       invariant and fix the world, after the jump or the exception entry *)
    iAssert (|={⊤}=>
               na_own cerise_nais ⊤ ∗
               cstack_frag cstk ∗
               world_interp Wfixed C ∗
               (if is_untrusted_caller ccrel
                then True
                else [[a_stk,a_stk4]]↦ₐ[[region_addrs_zeroes a_stk a_stk4]]))%I
      with "[Hna Hmtdc Hsave_area Hframeoffset HthreadID Ha_tstk Ha_tstk_tbl Ha_tstk_cnt Htstk
             Hcstk_full Hstk_interp_next Hcstk Hclose_switcher_inv
             Hworld_interp Hstk' Hstk Hrevoked Hlc'']" as "Hupd".
    { iMod (cstack_update _ _ cstk with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk_frag]".
      iMod ("Hclose_switcher_inv"
             with "[$Hna Hmtdc Hsave_area Hframeoffset HthreadID Ha_tstk Ha_tstk_tbl Ha_tstk_cnt Htstk
                    Hcstk_full Hstk_interp_next]")
        as "Hna".
      { iNext.
        iApply (switcher_inv_pop_frame with
                 "Hmtdc Hsave_area Hframeoffset HthreadID Ha_tstk Ha_tstk_tbl Ha_tstk_cnt Htstk
                  Hcstk_full Hstk_interp_next Hp_ot_switcher"); done. }
      iMod (world_interp_stack_fixing with
             "Htrap Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''") as
        "(Hworld_interp & Hstk')"; eauto.
      by iFrame. }

    iDestruct (interp_monotone_cap_nonheap with "Hinterp_callee_wstk")
      as "Hinterp_callee_wstk'";
      [exact Hstk_nonheap|exact Hrelated_pub_W0_Wfixed|].

    rewrite /is_untrusted_caller_frm /=
    ; rewrite /is_untrusted_caller_frm /= in Hframe
    ; destruct (is_untrusted_caller ccrel) eqn:Hccrel; cycle 1.
    - (* Case where caller is trusted, we use the continuation *)
      destruct Hwastks as (-> & -> & -> & ->).
      iSplit; cycle 1.
      { (* The return address of a trusted caller is a valid target *)
        iIntros "%Hjalr".
        destruct (Hret_ok Hccrel) as [Hret_jalr Hret_heap].
        apply load_heap_in_world_nonheap in Hr2; last done.
        subst rstk2; congruence. }
      iIntros "[HPC _]".
      iMod "Hupd" as "(Hna & Hcstk_frag & Hworld_interp & Hstk')".

      iEval (rewrite open_world_interp_empty -(fmap_nil LNonHeap)) in "Hworld_interp".
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

      iEval (rewrite /interp_cont_exec /is_untrusted_caller_frm /=)
        in "Hexec_topmost_frm".
      iApply ("Hexec_topmost_frm" with
               "[] [%] [%] [%] [%] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hworld_interp $Hstk $Hstk' $Hres $Hcont_K $Hcstk_frag $Hna]");
        [done|exact Hr3|exact Hr2|exact Hr0|exact Hr1|].
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we jump to the return address *)
      iDestruct "Hinterp_loaded" as
        "#(Hinterp_wstk3 & Hinterp_wstk2 & Hinterp_wstk1 & Hinterp_wstk0)".
      iApply (switcher_jump_to_caller_cases_spec with
               "Htrap Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk'
                Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap Hcont_K [Hupd]"); first done.
      { eapply frame_match_mono; eauto. }
      iMod "Hupd" as "(Hna & Hcstk_frag & Hworld_interp & _)".
      by iFrame.
      Unshelve. all: exact Wcur.
  Qed.

  (** A fault in a trusted callee is safe: the exception entry sets the
      return values to integers, then the return routine returns to the
      caller as in [switcher_ret_specification]. The return values need no
      validity. The resources are only needed after the exception entry,
      hence under an update (for instance, to close an invariant). *)
  Lemma trap_safe_return
    (Nswitcher : namespace)
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (w : LWord)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk (csp_b ^+ -4)%a csp_e ->
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    (|={⊤}=>
       [[csp_b,csp_e]]↦ₐ[[stk_mem]] ∗
       cstack_frag cstk ∗
       interp_continuation cstk Ws Cs ∗
       world_interp Wcur C ∗
       na_own cerise_nais ⊤ ∗
       RevokedResources Wfixed C l ∗
       ([∗ map] k↦y ∈ rmap, k ↦ᵣ y) ∗
       ca0 ↦ᵣ - ∗
       ca1 ↦ᵣ - ∗
       csp ↦ᵣ WCap true RWL Local csp_b csp_e csp_b) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked)
      "#Hswitcher #Hstatic Hres".
    iApply (trap_safe_exception_entry with "Hstatic").
    iMod "Hres" as "(Hstk & Hcstk & HK & Hworld_interp & Hna & Hclose_list_res & Hrmap
                     & Hca0 & Hca1 & Hcsp)".
    iModIntro; iFrame "Hca0 Hca1".
    iIntros "(HPC & Hca0 & Hca1)".
    iApply (switcher_ret_specification with
             "[$Hswitcher $Hstatic $Hstk $Hcstk $HK $Hworld_interp $Hna $HPC
               $Hclose_list_res $Hrmap $Hca0 $Hca1 $Hcsp]"); try done.
    iSplit; iApply interp_int.
  Qed.

End Switcher.
