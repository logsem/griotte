From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble.
From griotte Require Import switcher_return_states.
From griotte.switcher.callback Require Import callback_path.
From stdpp Require Import base.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Import switcher_load_spec switcher_exception.
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
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 wcsp : LWord)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk csp_b csp_e ->
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
    ∗ csp ↦ᵣ wcsp
    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - when the frame to pop is the entry frame, the thread exits:
         [switcher_after_compartment_call_exit_path_spec];
       - [switcher_after_compartment_call_spec]: pop the trusted stack;
       - [open_world_interp_cframe_gen]: obtain the callee-save area;
       - [switcher_restore_spill_path_world_spec]: restore the callee-save registers,
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
    iEval (rewrite switcher_return_block_13) in "HPC".
    destruct cstk as [ef [|frm frms] ]; iEval (rewrite /cstack_interp; cbn) in "Hstk_interp";
      cbn in Hlen_cstk.
    { (* No caller: the frame to pop is the entry frame, the thread exits *)
      iApply (switcher_after_compartment_call_exit_path_spec with
        "[$HPC $Hctp $Hct0 $Hct2 $Hmtdc $Hframeoffset $Hcode
          Hna Hclose_switcher_inv Hsave_area HthreadID Htstk Hcstk_full Hstk_interp]").
      iIntros "!> [Hmtdc Hframeoffset]".
      subst hclose_switcher_inv.
      iMod ("Hclose_switcher_inv" with
             "[$Hna Hmtdc Hsave_area Hframeoffset HthreadID Htstk Hcstk_full Hstk_interp]") as "Hna".
      { iNext. iExists a_tstk, (entry_cstack ef), save_area, tstk_next. iFrame "∗ # %". }
      iModIntro; iIntros (_); iFrame.
    }

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm as [ [w_csp w_tbl n_cnt] [wret wcgp wcs0 wcs1] ccrel].
    rewrite /cframe_interp.
    iDestruct "Hcframe_interp" as "[>Hcframe_top Hcframe_interp]".
    iNamed "Hcframe_top". iNamed "Hcf_tframe".
    iDestruct "Htf_tbl" as "[Htf_tbl _]".
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(%b_stk & %e_stk & %a_stk & >%HWF & Hcframe_interp)".
    cbn in HWF.
    destruct HWF as (-> & Hstk_bounds & Hstk_mmio & Hstk_heap & Hret_ok).
    assert (∀ tf, tf.(tf_csp).(lw) = WCap true RWL Local b_stk e_stk (stk_saved_a a_stk) →
                  tf_caller_a tf = a_stk) as Hspill.
    { intros tf Htf. eapply tf_caller_a_saved; [apply Hstk_bounds | exact Htf]. }
    (* The callee's stack is the one carved out of the caller's *)
    cbn in Hcsp_sync; rewrite Hspill in Hcsp_sync; last done.
    destruct Hcsp_sync as [Hcsp_b Hcsp_e].
    subst csp_b csp_e.
    pose proof Hstk_bounds as (Hb_a4 & He_a1 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in He_a1.

    iDestruct (interp_monotone_continuation with "HK") as "HK"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "HK". rewrite Hspill; last done.
    rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    stk_unfold.
    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Htopmost_frm)".
    iDestruct "Hinterp_callee_wstk" as "[%Hstk_nonheap #Hinterp_callee_wstk]".
    assert (is_heap_address b_stk = false) as Hstk_base_nonheap.
    { eapply disjoint_from_heap_not_in; first exact Hstk_heap.
      rewrite /withinBounds; solve_addr. }

    (* Pop the trusted stack *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iApply (switcher_after_compartment_call_spec with
      "[- $HPC $Hctp $Hct0 $Hct1 $Hct2 $Hcsp $Hmtdc $Hframeoffset $Htf_csp $Hcode]");
      [done|done|done|].
    iNext; iIntros "(HPC & Hctp & Hct0 & Hct1 & Hct2 & Hcsp & Hmtdc & Hframeoffset & Htf_csp
                    & Hlc)".
    iInsertRegs "Hrmap" ["Hct2"].

    (* Obtain the callee-save area *)
    iMod (
        open_world_interp_cframe_gen with "Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.

    (* Restore, clear and return *)
    stk_unfold.
    iEval (rewrite open_world_interp_empty) in "Hworld_interp".
    iAssert (switcher_stk_cells (stk_spill_a a_stk) wastk wastk1 wastk2 wastk3)
      with "[$Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3]" as "Hcells".
    iApply (switcher_restore_spill_path_world_spec Wcur Wfixed C [] ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp
        $Hcells $Hstk $Hworld_interp $Hrmap $Hcode]"); [|done|done| |].
    { subst Wfixed. by rewrite close_list_heap. }
    { rewrite dom_insert_L. repeat (rewrite dom_delete_L). rewrite Hrmap. set_solver. }
    iSplitR.
    { destruct (is_untrusted_caller ccrel); last done.
      iDestruct "Hinterp_wfrm" as "(Hw0 & Hw1 & Hw2 & Hw3)".
      iFrame "Hw2 Hw3 Hw1 Hw0". }
    iNext; iIntros (arg_rmap' rstk3 rstk2 rstk1 rstk0)
      "((%Hr3 & %Hr2 & %Hr1 & %Hr0) & Hworld_interp & Hinterp_loaded & %Harg_rmap'
      & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hrmap & _ & Hlc)".
    iEval (rewrite -open_world_interp_empty) in "Hworld_interp".
    iDestruct "Hlc" as "(Hlc & Hlc'')".

    (* Depop the topmost frame of the call-stack, close the switcher's
       invariant and fix the world, after the jump or the exception entry *)
    iAssert (|={⊤}=>
               na_own cerise_nais ⊤ ∗
               cstack_frag {| cstk_entry := ef; cstk_frames := frms |} ∗
               world_interp Wfixed C ∗
               (if is_untrusted_caller ccrel
                then True
                else [[stk_spill_a a_stk, (stk_spill_a a_stk ^+ SpillSlot_size)%a]]↦ₐ[[region_addrs_zeroes
                       (stk_spill_a a_stk) (stk_spill_a a_stk ^+ SpillSlot_size)%a]]))%I
      with "[Hna Hmtdc Hsave_area Hframeoffset HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
             Hcstk_full Hstk_interp_next Hcstk Hclose_switcher_inv
             Hworld_interp Hstk' Hstk Hrevoked Hlc'']" as "Hupd".
    { iMod (cstack_update _ _ {| cstk_entry := ef; cstk_frames := frms |} with "Hcstk_full Hcstk")
        as "[Hcstk_full Hcstk_frag]".
      iMod ("Hclose_switcher_inv"
             with "[$Hna Hmtdc Hsave_area Hframeoffset HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
                    Hcstk_full Hstk_interp_next]")
        as "Hna".
      { iNext.
        iApply (switcher_inv_pop_frame _ {| cstk_entry := ef; cstk_frames := frms |} with
                 "Hmtdc Hsave_area Hframeoffset HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
                  Hcstk_full Hstk_interp_next Hp_ot_switcher"); done. }
      iMod (world_interp_stack_fixing _ _ _ _ b_stk e_stk a_stk with
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
      iDestruct (open_world_interp_opening_resources _ _ (finz.seq_between b_stk (stk_spill_a a_stk)) []
                  with "[$Hinterp_callee_wstk' $Hworld_interp]")
        as "(Hworld_interp & (%lv & Hstk & Hres))"; auto.
      { apply finz_seq_between_NoDup. }
      { apply Forall_forall; intros y Hy.
        rewrite elem_of_finz_seq_between in Hy. stk_unfold.
        solve_addr+Ha4 Hb_a4 He_a1 Hy.
      }
      { set_solver+. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hres]") as ">Hres".

      rewrite app_nil_r.

      iEval (rewrite /interp_cont_exec /is_untrusted_caller_frm /=)
        in "Htopmost_frm".
      stk_unfold.
      iApply ("Htopmost_frm" with
               "[] [%] [%] [%] [%] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hworld_interp $Hstk $Hstk' $Hres $Hcont_K $Hcstk_frag $Hna]");
        [done|exact Hr3|exact Hr2|exact Hr0|exact Hr1|].
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we jump to the return address *)
      iDestruct "Hinterp_loaded" as
        "#(Hinterp_wstk3 & Hinterp_wstk2 & Hinterp_wstk1 & Hinterp_wstk0)".
      (* The untrusted caller recorded that its topmost compartment is
         untrusted *)
      iDestruct "Htopmost_frm" as "#Htop_caller".
      iDestruct (top_cmpt_untrusted_mono_pub with "Htop_caller") as "#Htop";
        first exact Hrelated_pub_W0_Wfixed.
      iApply (switcher_jump_to_caller_cases_spec with
               "Htrap Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk'
                Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 Htop Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap Hcont_K [Hupd]"); first done.
      { eapply frame_match_mono; eauto. }
      iMod "Hupd" as "(Hna & Hcstk_frag & Hworld_interp & _)".
      by iFrame.
      Unshelve. all: exact Wcur.
  Qed.

  (** [csp_sync] does not read the error handler count of the topmost
      frame. *)
  Lemma csp_sync_set_top_count (cstk : CSTK) (n : Z) (b_stk' e_stk' : Addr) :
    csp_sync (cstack_set_top_count cstk n) b_stk' e_stk' ↔ csp_sync cstk b_stk' e_stk'.
  Proof. by destruct cstk as [ef [|frm frms] ]. Qed.

  (** A fault in a trusted callee whose table declares no handler is safe:
      the exception entry sets the return values to integers, then the
      return routine returns to the caller as in
      [switcher_ret_specification], for a fault that the exception path
      does not resume. The return values need no validity. The resources
      come under an update at the time of the fault (for instance, to close
      an invariant). *)
  Lemma trap_safe_return
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
    csp_sync cstk csp_b csp_e ->
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    trap_no_resume w ->

    na_inv cerise_nais Nswitcher switcher_inv -∗
    switcher_static -∗
    no_handler (top_export_tbl cstk) -∗
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
       csp ↦ᵣ -) -∗
    trap_safe w ⊤ (λ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤)%I.
  Proof.
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked
               Hno_resume)
      "#Hswitcher #Hstatic #Hno_handler Hres".
    iApply (trap_safe_exception_entry ⊤ with "Hswitcher Hstatic");
      [set_solver | set_solver |].
    iMod "Hres" as "(Hstk & Hcstk & HK & Hworld_interp & Hna & Hclose_list_res & Hrmap
                     & [%wca0 Hca0] & [%wca1 Hca1] & [%wcsp Hcsp])".
    iModIntro.
    iInsertList "Hrmap" [csp;ca0;ca1].
    iExists _, cstk. iFrame "Hna Hrmap Hcstk".
    iSplit.
    { iPureIntro. intros r. apply elem_of_dom. rewrite !dom_insert_L Hrmap.
      pose proof (all_registers_s_correct r). set_solver. }
    iApply (trap_handler_ok_no_handler with "Hno_handler"); first done.
    iIntros (n rmap' Hfull_rmap' Hca0' Hca1') "HPC Hrmap' Hcstk _ Hna".
    rewrite /registers_pointsto.
    getRegValList [csp].
    iExtractList "Hrmap'" [csp;ca0;ca1] as ["Hcsp";"Hca0";"Hca1"].
    iEval (rewrite -(interp_cont_set_top_count cstk Ws Cs n)) in "HK".
    iApply (switcher_ret_specification _ _ _ _ _ _ _ _ (cstack_set_top_count cstk n) with
             "[$Hswitcher $Hstatic $Hstk $Hcstk $HK $Hworld_interp $Hna $HPC
               $Hclose_list_res $Hrmap' $Hca0 $Hca1 $Hcsp]"); try done.
    { rewrite !dom_delete_L (lregmap_full_dom _ Hfull_rmap'). set_solver. }
    { by apply frame_match_set_top_count. }
    { by apply csp_sync_set_top_count. }
    iSplit; iApply interp_int.
  Qed.

End Switcher.
