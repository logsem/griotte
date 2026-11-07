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
From griotte Require Import map_simpl register_tactics proofmode switcher_registers.
From griotte Require Import switcher_load_spec switcher_trap_safety interp_switcher_return.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseb : ceriseBaseG Σ} {th : Thread} {Cname : CmptNameG} {cthreads : CmptThreads}
    {sealsg: sealStoreG Σ}
    {stsg : STSG Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  #[local] Notation V := (interpO Σ).

  Lemma switcher_ret_specification_gen
    (W0 Wcur : WORLD)
    (C : CmptName)
    (rmap : LReg)
    (csp_e csp_b: Addr)
    (l : list LAddr)
    (stk_mem : list LWord)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (wca0 wca1 wcsp : LWord)
    (h : Z)
    :
    let Wfixed := (close_list (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) Wcur) in
    related_sts_pub_world W0 Wfixed ->
    dom rmap = all_registers_s ∖ ({[ csp ; ca0 ; ca1 ]} ) ->
    frame_match Ws Cs cstk W0 C ->
    csp_sync cstk csp_b csp_e ->
    (* NOTE: there is only one side of the implication... *)
    NoDup (l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (∀ a : LAddr, (std W0) !! a = Some Temporary -> a ∈ l ++ (LNonHeap <$> finz.seq_between csp_b csp_e)) ->
    (* MSHWM is in the callee's stack, or below *)
    (h <= csp_e)%Z ->

    (* The thread runs in the callee's compartment *)
    thread_in th C
    (* Trap safety of the switcher, with its invariant *)
    ∗ switcher_trap_safety
    ∗ interp Wfixed C wca0
    ∗ interp Wfixed C wca1
    ∗ stack_region csp_b csp_e stk_mem
    ∗ hwm_res cstk h
    ∗ ◯(CSTK)[th] cstk
    ∗ interp_continuation cstk Ws Cs
    ∗ world_interp Wcur C
    ∗ na_own (tpool th) ⊤
    ∗ PC ↦ₚ[th] Cap XSRW_ Local b_switcher e_switcher a_switcher_return
    ∗ ▷ RevokedResources Wfixed C l
    ∗ regs[th] rmap
    ∗ ca0 ↦ᵣ[th] wca0
    ∗ ca1 ↦ᵣ[th] wca1
    ∗ csp ↦ᵣ[th] wcsp
    ⊢ safe[th].
  Proof.
    (* Outline of the proof:
       - open the trusted-stack invariant;
       - when the frame to pop is the entry frame, the thread exits:
         [switcher_return_exit_path_spec], [switcher_return_exit_close];
       - otherwise, [switcher_return_path_world_spec]: pop the trusted
         stack; obtain the callee-save area
         ([open_world_interp_cframe_gen]); restore the callee-save
         registers, clear the stack frame and the registers, and jump to
         the caller;
       - close the trusted-stack invariant ([switcher_return_pop_close]) and fix
         the world ([world_interp_stack_fixing]);
       - when the caller is trusted, use the continuation;
       - when the caller is untrusted, [switcher_jump_to_caller_cases_spec]. *)
    intros Wfixed.
    iIntros (Hrelated_pub_W0_Wfixed Hrmap Hframe Hcsp_sync Hnodup_revoked Htemp_revoked Hh_e)
      "(#Hthread & #Hsafety & #Hinterp_Wfixed_wca0 & #Hinterp_Wfixed_wca1 & Hstk & Hhwm & Hcstk & HK
    & Hworld_interp & Hna & HPC & Hclose_list_res & Hrmap & Hca0 & Hca1 & Hcsp)".
    iDestruct "Hhwm" as "[(Hmshwmb & Hmshwm & %Hhwm_ord & Hlocked) #Hts]".
    iPoseProof (switcher_trap_safety_res with "Hsafety") as "[#Hswitcher #Hstatic]".
    iPoseProof "Hstatic" as "[#Hcode _]".
    iPoseProof (switcher_mtcc_vec_safe_of_safety with "Hsafety") as "#Htrap".

    (* Open the trusted-stack invariant *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed trusted_stack_inv_open "Hswitcher_inv".
    iDestruct (switcher_hazard_open with "Hsave_area Hhazard_slots") as "[Hhazard Hsave_area]";
      first done.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    iDestruct (ret_callee_saved_extract with "Hrmap")
      as "([%wcgp_old Hcgp] & [%wcra_old Hcra] & [%wcs0_old Hcs0] & [%wcs1_old Hcs1]
          & %rmap0 & %Hrmap0 & Hrmap)"; first done.
    iDestruct (cstack_agree with "Hcstk_full [$]") as %Heq; subst cstk'.
    iEval (rewrite switcher_return_block_13) in "HPC".
    destruct cstk as [ef [|frm frms] ].
    { (* No caller: the frame to pop is the entry frame, the thread exits *)
      iApply (switcher_return_exit_path_spec with
        "[$HPC $Hrmap $Hmtdc $Hframeoffset $Hhazard $Hcode
          Hna Hclose_switcher_inv Hsave_area HthreadID Htstk Hcstk_full Hstk_interp]");
        first done.
      iIntros "!> (Hmtdc & Hframeoffset & Hhazard)".
      subst hclose_switcher_inv.
      iMod (switcher_return_exit_close ⊤ (entry_cstack ef) with
             "Hsave_mshwmb Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htstk
              Hcstk_full Hstk_interp") as "Hna"; [done|done|].
      iModIntro; iIntros (_); iExact "Hna".
    }
    iEval (rewrite /cstack_interp; cbn) in "Hstk_interp".
    cbn in Hlen_cstk.

    destruct Ws as [|Wprev Ws],Cs;try done. simpl in Hframe.
    destruct Hframe as [Hrelated_pub_Wprev_W0 [<- [Hccrel_known_to_known Hframe] ] ].

    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm as [ [w_csp w_tbl n_cnt] [wret wcgp wcs0 wcs1] ccrel].
    rewrite /cframe_interp.
    iDestruct "Hcframe_interp" as "[>Hcframe_top Hcframe_interp]".
    iNamed "Hcframe_top". iNamed "Hcf_tframe".
    iDestruct "Htf_tbl" as (wtbl) "[Htf_tbl _]".
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "(%b_stk & %e_stk & %a_stk & >%HWF & Hcframe_interp)".
    cbn in HWF.
    destruct HWF as (-> & Hstk_bounds & Hstk_mmio & Hstk_heap & Hret_ok).
    assert (∀ tf, tf.(tf_csp).(lw) = Cap RWL Local b_stk e_stk (stk_saved_a a_stk) →
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
    (* The caller's stack, and the stacks of the frames below, start at the
       base of the thread's stack: so does the floor *)
    iDestruct (interp_cont_bases with "HK") as "[HK %Hbases]".
    apply Forall_cons in Hbases as [Hbase Hbases].
    cbn in Hbase, Hbases.
    pose proof (frames_hwm_floor_base _ _ Hbases) as Hfloor_next.
    rewrite /cstk_hwm_base /cstk_hwm_floor /is_untrusted_caller_frm /= in Hhwm_ord.
    iEval (rewrite /cstk_hwm_base /cstk_hwm_floor /is_untrusted_caller_frm /=)
      in "Hlocked Hts Hmshwmb".
    assert ((if is_untrusted_caller ccrel then frames_hwm_floor ef frms else b_stk) = tf_stk_b ef)
      as Hfloor by (destruct (is_untrusted_caller ccrel); by rewrite ?Hfloor_next).
    rewrite Hfloor in Hhwm_ord.
    iEval (rewrite Hfloor hwm_locked_empty) in "Hlocked".
    destruct Hhwm_ord as [_ Hhwm_ord].
    iEval (cbn) in "HK". rewrite Hspill; last done.
    rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    stk_unfold.
    iDestruct "HK" as "(Hcont_K & #Hinterp_callee_wstk & Htopmost_frm)".
    iDestruct "Hinterp_callee_wstk" as "[%Hstk_nonheap #Hinterp_callee_wstk]".

    (* The cells of the callee's stack below MSHWM hold 0 *)
    iMod (stack_region_below_hwm with "Hstk [$Hmshwmb $Hmshwm]")
      as "(%Hzero & Hstk & Hhwm_regs)"; first solve_addr.

    (* Pop the trusted stack, restore, clear and return *)
    destruct Hlen_cstk as [Hlen_cstk Ha_tstk_e].
    iApply (switcher_return_path_world_spec Wcur Wfixed C ccrel (length frms) with
      "[- $HPC $Hcsp $Hcgp $Hcra $Hcs0 $Hcs1 $Hrmap $Hmtdc $Hframeoffset $Hhazard $Htf_csp
          $Hhwm_regs $Hcode]");
      [done|done|done|done|done|done| split; [solve_addr|lia] |].
    iIntros "!> (Hmtdc & Hframeoffset & Hhazard & Htf_csp & Hlc)".

    (* Obtain the callee-save area *)
    iMod (
        open_world_interp_cframe_gen with "Hinterp_callee_wstk Hcframe_interp Hclose_list_res Hlc")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 &
            Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & %Hwastks & #Hinterp_wfrm & Hrevoked)";eauto.
    stk_unfold.
    iEval (rewrite open_world_interp_empty) in "Hworld_interp".
    iAssert (stack_region (a_stk ^- 4) ((a_stk ^- 4) ^+ SpillSlot_size)
               [wastk; wastk1; wastk2; wastk3])
      with "[Ha_stk Ha_stk1 Ha_stk2 Ha_stk3]" as "Hcells".
    { rewrite /stack_region /SpillSlot_size.
      rewrite (finz_seq_between_cons _ ((a_stk ^- 4) ^+ 4)); last solve_addr.
      rewrite (finz_seq_between_cons _ ((a_stk ^- 4) ^+ 4)); last solve_addr.
      rewrite (finz_seq_between_cons _ ((a_stk ^- 4) ^+ 4)); last solve_addr.
      rewrite (finz_seq_between_cons _ ((a_stk ^- 4) ^+ 4)); last solve_addr.
      rewrite (finz_seq_between_empty _ ((a_stk ^- 4) ^+ 4)); last solve_addr.
      rewrite /= (_ : ((a_stk ^- 4) ^+ 1) ^+ 1 = (a_stk ^- 4) ^+ 2); last solve_addr.
      rewrite (_ : ((a_stk ^- 4) ^+ 2) ^+ 1 = (a_stk ^- 4) ^+ 3); last solve_addr.
      by iFrame "Ha_stk Ha_stk1 Ha_stk2 Ha_stk3". }
    iModIntro.
    iExists [], wastk, wastk1, wastk2, wastk3, stk_mem.
    iFrame "Hcells Hstk Hworld_interp".
    iSplitR.
    { destruct (is_untrusted_caller ccrel); last done.
      iDestruct "Hinterp_wfrm" as "(Hw0 & Hw1 & Hw2 & Hw3)".
      iFrame "Hw2 Hw3 Hw1 Hw0". }
    iNext; iSplit; cycle 1.
    { (* The caller's stack starts at the base of the thread's stack, at or
         below MSHWM: the zeroing does not fault *)
      iIntros (rmap1 rcgp rcra rcs1 rcs0 off) "(_ & %Hlt & _)". exfalso.
      rewrite Hbase in Hlt; lia. }
    iIntros (arg_rmap' rstk3 rstk2 rstk1 rstk0)
      "((%Hr3 & %Hr2 & %Hr1 & %Hr0) & _ & Hworld_interp & Hinterp_loaded & %Harg_rmap'
      & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk' & Hstk & Hhwm_regs & Hrmap & Hlc)".
    (* The spill area is above MSHWM, the cells of the callee's stack below
       MSHWM hold 0: both are zeroed *)
    iEval (rewrite stack_zeroed_from_below; last solve_addr) in "Hstk'".
    iEval (rewrite Hzero) in "Hstk".
    iDestruct (stack_region_length with "Hstk") as %Hlen_stk.
    rewrite length_replicate in Hlen_stk.
    iEval (rewrite (_ : replicate (length stk_mem) (lword_of_word (WInt 0))
                         = region_addrs_zeroes b_stk (a_stk ^- 4));
           last (by rewrite /region_addrs_zeroes -Hlen_stk finz_seq_between_length)) in "Hstk".
    iEval (rewrite (_ : replicate (length [wastk; wastk1; wastk2; wastk3]) (lword_of_word (WInt 0))
                         = region_addrs_zeroes (a_stk ^- 4) ((a_stk ^- 4) ^+ SpillSlot_size));
           last (rewrite /region_addrs_zeroes /SpillSlot_size /finz.dist; f_equal; cbn;
                 solve_addr)) in "Hstk'".
    (* MSHWM is the caller's cursor *)
    iAssert (hwm_res {| cstk_entry := ef; cstk_frames := frms |} a_stk)%I
      with "[Hhwm_regs Hlocked]" as "Hhwm".
    { iDestruct "Hhwm_regs" as "[Hmshwmb Hmshwm]".
      rewrite /hwm_res /hwm_res_at /cstk_hwm_base /cstk_hwm_floor /cstk_hwm_top /= Hfloor_next
        hwm_locked_empty.
      iFrame "Hmshwmb Hmshwm Hts". iPureIntro. split; solve_addr. }
    iEval (rewrite -open_world_interp_empty) in "Hworld_interp".
    iDestruct "Hlc" as "(Hlc & Hlc'')".

    (* Depop the topmost frame of the call-stack, close the switcher's
       invariant and fix the world, after the jump or the exception entry *)
    iAssert (|={⊤}=>
               na_own (tpool th) ⊤ ∗
               cstack_frag {| cstk_entry := ef; cstk_frames := frms |} ∗
               world_interp Wfixed C ∗
               (if is_untrusted_caller ccrel
                then True
                else stack_region (stk_spill_a a_stk) (stk_spill_a a_stk ^+ SpillSlot_size)
                      (region_addrs_zeroes (stk_spill_a a_stk)
                         (stk_spill_a a_stk ^+ SpillSlot_size))))%I
      with "[Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
             Hcstk_full Hstk_interp_next Hcstk Hclose_switcher_inv
             Hworld_interp Hstk' Hstk Hrevoked Hlc'']" as "Hupd".
    { subst hclose_switcher_inv.
      iMod (switcher_return_pop_close ⊤ _ {| cstk_entry := ef; cstk_frames := frms |} with
             "Hsave_mshwmb Hclose_switcher_inv Hna Hmtdc Hsave_area Hframeoffset Hhazard HthreadID Htf_csp Htf_tbl
              Htf_cnt Htstk Hcstk_full Hcstk Hstk_interp_next")
        as "[Hna Hcstk_frag]"; [done|done|done|].
      iMod (world_interp_stack_fixing _ _ _ _ b_stk e_stk a_stk with
             "Htrap Hinterp_callee_wstk Hworld_interp Hstk' Hstk Hrevoked Hlc''") as
        "(Hworld_interp & Hstk')"; eauto.
      by iFrame "Hna Hcstk_frag Hworld_interp Hstk'". }

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
      iDestruct "Htopmost_frm" as "[_ Htopmost_frm]".
      iEval (rewrite /interp_cont_exec /is_untrusted_caller_frm /=)
        in "Htopmost_frm".
      stk_unfold.
      iEval (rewrite -stack_region_temp_cells) in "Hstk".
      (* The caller's cells between the floor and its stack: none *)
      iAssert (hwm_locked (frames_hwm_floor ef frms) b_stk) as "Hlocked'".
      { by rewrite Hfloor_next -Hbase hwm_locked_empty. }
      iApply ("Htopmost_frm" with
               "[] [%] [%] [%] [%] [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_Wfixed_wca0 $Hinterp_Wfixed_wca1
      $Hrmap $Hhwm $Hlocked' $Hworld_interp $Hstk $Hstk' $Hres $Hcont_K $Hcstk_frag $Hna $Hthread]");
        [done|exact Hr3|exact Hr2|exact Hr0|exact Hr1|].
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we jump to the return address *)
      iDestruct "Hinterp_loaded" as
        "#(Hinterp_wstk3 & Hinterp_wstk2 & Hinterp_wstk1 & Hinterp_wstk0)".
      (* The untrusted caller recorded that its topmost compartment is
         untrusted *)
      iDestruct "Htopmost_frm" as "(#Htop_caller & %Hzone & _)".
      iDestruct (top_cmpt_untrusted_mono_pub with "Htop_caller") as "#Htop";
        first exact Hrelated_pub_W0_Wfixed.
      iApply (switcher_jump_to_caller_cases_spec with
               "Htrap Hthread Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk'
                Hinterp_Wfixed_wca0 Hinterp_Wfixed_wca1 Htop Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap [Hhwm] Hcont_K [Hupd]"); first done.
      { eapply frame_match_mono; eauto. }
      { iExists a_stk. iFrame "Hhwm". iPureIntro.
        by eapply zone_temporary_mono_pub. }
      iMod "Hupd" as "(Hna & Hcstk_frag & Hworld_interp & _)".
      by iFrame.
      Unshelve. all: exact Wcur.
  Qed.

  (** [csp_sync] does not read the error handler count of the topmost
      frame. *)
  Lemma csp_sync_set_top_count (cstk : CSTK) (n : Z) (b_stk' e_stk' : Addr) :
    csp_sync (cstack_set_top_count cstk n) b_stk' e_stk' ↔ csp_sync cstk b_stk' e_stk'.
  Proof. by destruct cstk as [ef [|frm frms] ]. Qed.

End Switcher.
