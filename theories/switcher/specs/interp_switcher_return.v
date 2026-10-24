From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From griotte Require Export logrel monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import switcher_return_states.
From griotte.switcher.callback Require Import callback_path.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.

Section fundamental.
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

  Notation E := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LWord) -n> iPropO Σ).
  Notation K := (CSTK -n> list WORLD -n> leibnizO (list CmptName) -n> iPropO Σ).
  Notation R := (WORLD -n> (leibnizO CmptName) -n> (leibnizO LReg) -n> iPropO Σ).
  Implicit Types w : (leibnizO LWord).
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

      We extract the registers used in the code out of the map into individual resources.
      Only the return values [ca0] and [ca1] must be safe-to-share: this is all
      [switcher_return_unwind] asks of the register file, and safe-to-exec
      provides it, since all registers are then safe-to-share.
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
      1) The call-stack is empty: the frame to pop is the entry frame of
         the thread. The switcher exits the thread, and we close the
         invariant of the switcher, which gives back [na_own cerise_nais ⊤].
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

  (** The return routine, from its entry point: from a full register file
      whose return values [ca0] and [ca1] are safe, the switcher pops the
      caller's frame and returns to it, or exits the thread when the frame to
      pop is the entry frame. No other register is read. *)
  Lemma switcher_return_unwind (trusted_fault : CSTK → LWord → LReg → iProp Σ)
    (W : WORLD) (C : CmptName)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (rmap : LReg) (wca0 wca1 : LWord) :
    (∀ r, is_Some (rmap !! r)) ->
    rmap !! ca0 = Some wca0 ->
    rmap !! ca1 = Some wca1 ->
    frame_match Ws Cs cstk W C ->

    PC ↦ₚ WCap true XSRW_ Local b_switcher e_switcher a_switcher_return ∗
    registers_pointsto rmap ∗
    interp W C wca0 ∗
    interp W C wca1 ∗
    na_inv cerise_nais Nswitcher switcher_inv ∗
    switcher_static ∗
    trap_vector_safe trusted_fault (lword_of_word mtcc_vec) ∗
    world_interp W C ∗
    interp_cont interp cstk Ws Cs ∗
    na_own cerise_nais ⊤ ∗
    cstack_frag cstk
    ⊢ interp_conf W C.
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - when the frame to pop is the entry frame, the thread exits:
         [switcher_after_compartment_call_exit_path_spec];
       - [switcher_after_compartment_call_spec]: pop the trusted stack;
       - [open_world_interp_cframe], [open_world_interp_callee_stack]: obtain
         the caller's stack frame;
       - [switcher_restore_spill_path_world_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant;
       - when the caller is trusted, use the continuation relation;
       - when the caller is untrusted, close the world and
         [switcher_jump_to_caller_cases_spec]. *)
    iIntros (Hfull_rmap Hwca0 Hwca1 Hfreq)
      "(HPC & Hrmap & #Hinterp_wca0 & #Hinterp_wca1 & #Hinv_switcher & #[Hcode _] & #Htrap
        & Hworld_interp & Hcont_K & Hna & Hcstk)".
    rewrite /registers_pointsto.

    getRegValList [cra;csp;cgp;ctp;ca2;cs1;cs0;ct0;ct1;ct2].
    iExtractList "Hrmap" [cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1;ct2]
      as ["Hcra";"Hcsp";"Hcgp";"Hca0";"Hca1";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1";"Hct2"].
    set (rmap0 := delete ct2 _).

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    iModNamed switcher_inv_open "Hswitcher_inv".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.

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

    (* A frame pushed above the entry frame *)
    destruct Ws;[done|].
    destruct Cs;[done|].
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm as [ [w_csp w_tbl n_cnt] [wret_saved wcgp_saved wcs0_saved wcs1_saved] ccrel].
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
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hccrel_known_to_known & Hfreq).
    pose proof Hstk_bounds as (Hb_a4 & He_a1 & Ha4).
    stk_unfold. change (4 - 1)%Z with 3%Z in He_a1.

    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "Hcont_K". rewrite Hspill; last done.
    stk_unfold.
    rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    cbn.
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Htopmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".
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

    (* Obtain the caller's stack frame *)
    iDestruct (open_world_interp_cframe with "[$Hcframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3
          & Hstk'
          & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.
    rewrite -/(interp_cont).
    iDestruct (lc_fupd_elim_later with "[$Hlc] [$Hclose_res]") as ">Hclose_res".
    iDestruct "Hclose_res" as "[#Hsave Hstates]".
    iCombine "Hsave Hstates" as "Hclose_res".
    set (s := (a_stk ^+ - (4))%a).
    assert ((s + 4)%a = Some a_stk) as Hs4 by (subst s; solve_addr+Ha4).
    iAssert (if is_untrusted_caller ccrel then
        interp_in_mem RWL W C wastk2 ∗
        interp_in_mem RWL W C wastk3 ∗
        interp_in_mem RWL W C wastk1 ∗
        interp_in_mem RWL W C wastk
      else True)%I as "#Hnormal".
    { destruct (is_untrusted_caller ccrel) eqn:Huntrusted; simpl; last done.
      rewrite /StackWorldResources.
      stk_unfold.
      do 4 (rewrite (finz_seq_between_cons _ (s ^+ 4)%a); last solve_addr+Hs4).
      rewrite (finz_seq_between_empty _ (s ^+ 4)%a); last solve_addr+Hs4.
      replace ((s ^+ 1) ^+ 1)%a with (s ^+ 2)%a by solve_addr+Hs4.
      replace ((s ^+ 2) ^+ 1)%a with (s ^+ 3)%a by solve_addr+Hs4.
      iDestruct (big_sepL2_cons with "Hsave") as "[Hsave0 Hsave_tail1]".
      iDestruct (big_sepL2_cons with "Hsave_tail1") as "[Hsave1 Hsave_tail2]".
      iDestruct (big_sepL2_cons with "Hsave_tail2") as "[Hsave2 Hsave_tail3]".
      iDestruct (big_sepL2_cons with "Hsave_tail3") as "[Hsave3 _]".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave2") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave3") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave1") as "$".
      iDestruct (StackWorldResource_interp_in_mem with "Hsave0") as "$". }
    iDestruct (switcher_stk_cells_region_4 with "Hstk'") as "Hcells";
      first (stk_unfold; solve_addr+Ha4).
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & Hstk & Hres))"; eauto.

    (* Restore, clear and return *)
    iApply (switcher_restore_spill_path_world_spec W W C _ ccrel with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp $Hcells $Hstk
        $Hworld_interp $Hnormal $Hrmap $Hcode]");
      [done|done|done| |].
    { subst rmap0.
      clear -Hfull_rmap.
      rewrite dom_insert_L.
      repeat (rewrite dom_delete_L).
      apply lregmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    iNext; iIntros (arg_rmap' rstk3 rstk2 rstk1 rstk0)
      "(%Hloaded & Hworld_interp & Hinterp_loaded & %Harg_rmap' & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp
      & Hstk_register_save & Hstk & Hrmap & _ & _)".
    destruct Hloaded as (Hr3 & Hr2 & Hr1 & Hr0).

    (* Depop the topmost frame of the call-stack and close the switcher's
       invariant, after the jump or the exception entry *)
    iAssert (|={⊤}=> na_own cerise_nais ⊤ ∗
                     cstack_frag {| cstk_entry := ef; cstk_frames := frms |})%I
      with "[Hna Hmtdc Hsave_area Hframeoffset HthreadID Htf_csp Htf_tbl Htf_cnt Htstk
             Hcstk_full Hstk_interp_next Hcstk Hclose_switcher_inv]" as "Hupd".
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
      by iFrame. }

    set (lv' := region_addrs_zeroes b_stk s).
    assert (Forall (λ y : LWord, y = WInt 0) lv') as Hlv'.
    { subst lv'.
      rewrite /region_addrs_zeroes.
      by apply Forall_replicate.
    }

    destruct (is_untrusted_caller ccrel) eqn:Hccrel ; cycle 1.
    - (* Case where caller is trusted, we use the continuation relation K *)
      destruct Hwastks as (-> & -> & -> & ->).
      iEval (rewrite app_nil_r) in "Hworld_interp".

      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.

      iSplit; cycle 1.
      { (* The return address of a trusted caller is a valid target *)
        iIntros "%Hjalr".
        destruct (Hret_ok Hccrel) as [Hret_jalr Hret_heap].
        apply load_heap_in_world_nonheap in Hr2; last done.
        subst rstk2; congruence. }
      iIntros "[HPC _]".
      iMod "Hupd" as "[Hna Hcstk_frag]".
      iSpecialize ("Htopmost_frm" $! W (related_sts_pub_refl_world W)).
      iEval (rewrite /interp_cont_exec /is_untrusted_caller_frm /= ?Hccrel)
        in "Htopmost_frm".
      stk_unfold.
      iApply ("Htopmost_frm" with "[%] [%] [%] [%]
               [$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hstk_register_save $Hstk $Hworld_interp $Hres $Hcont_K $Hcstk_frag $Hna]");
        [exact Hr3|exact Hr2|exact Hr0|exact Hr1|].
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we close the world and jump to the
         return address *)
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk $Hres]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { clear -He_a1 Ha4 Hs4.
        intros a Ha Ha'.
        apply elem_of_finz_seq_between in Ha, Ha'.
        stk_unfold. solve_addr.
      }
      { subst lv'. by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }

      iDestruct "Hinterp_loaded" as
        "#(Hinterp_wstk3 & Hinterp_wstk2 & Hinterp_wstk1 & Hinterp_wstk0)".

      clear Hlen_lv' Hlv' lv'.
      set (lv' := region_addrs_zeroes s (s ^+ 4)%a).
      assert (Forall (λ y : LWord, y = WInt 0) lv') as Hlv'.
      { subst lv'; rewrite /region_addrs_zeroes; by apply Forall_replicate. }

      iDestruct (big_sepL2_length with "Hstk_register_save") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ _ lv' with "Hclose_res") as "Hclose_res"; auto.
      iEval (rewrite -(app_nil_r (finz.seq_between s (s ^+ 4)%a))) in "Hworld_interp".
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk_register_save $Hclose_res]") as "Hworld_interp".
      { apply finz_seq_between_NoDup. }
      { set_solver. }
      { subst lv'; by rewrite /region_addrs_zeroes length_replicate finz_seq_between_length. }
      rewrite fmap_nil -open_world_interp_empty.

      rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq.
      (* The untrusted caller recorded that its topmost compartment is
         untrusted *)
      iDestruct "Htopmost_frm" as "#Htop_caller".
      iApply (switcher_jump_to_caller_cases_spec with
               "Htrap Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk
                Hinterp_wca0 Hinterp_wca1 Htop_caller Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap Hcont_K [Hupd Hworld_interp]"); [done|done|].
      iMod "Hupd" as "[Hna Hcstk_frag]".
      by iFrame.
  Qed.

End fundamental.
