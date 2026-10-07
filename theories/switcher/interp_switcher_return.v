From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From griotte Require Export logrel monotone.
From griotte Require Import fundamental.
From griotte Require Import switcher_preamble.
From griotte Require Import switcher_return_states switcher_return_blocks_1 switcher_return_blocks_2.
From griotte Require Import map_simpl register_tactics proofmode.
From griotte Require Export world_ghost_theory world_interp_stack switcher_helpers.

Section fundamental.
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
    na_inv cerise_nais Nswitcher switcher_inv
    ⊢ interp_expr interp (interp_cont interp) W C (WCap XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    (* Outline of the proof:
       - open the switcher invariant;
       - when the call-stack is empty: [switcher_return_blocks_1_empty_spec];
       - [switcher_return_blocks_1_spec]: pop the trusted stack;
       - [open_world_interp_cframe], [open_world_interp_callee_stack]: obtain
         the caller's stack frame;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant;
       - when the caller is trusted, use the continuation relation;
       - when the caller is untrusted, close the world and
         [switcher_jump_to_caller_spec]. *)
    iIntros "#Hinv_switcher %cstk %Ws %Cs %rmap [[%Hfull_rmap #Hrmap_interp] (Hrmap & Hworld_interp & Hcont_K & Hna & Hcstk & %Hfreq)]".
    rewrite /registers_pointsto.

    (* --- Extract scratch registers ct2 ctp --- *)
    cbn in Hfull_rmap.

    getRegValList [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1].
    iExtractList "Hrmap" [PC;cra;csp;cgp;ca0;ca1;ctp;ca2;cs1;cs0;ct0;ct1]
      as ["HPC";"Hcra";"Hcsp";"Hcgp";"Hca0";"Hca1";"Hctp";"Hca2";"Hcs1";"Hcs0";"Hct0";"Hct1"].
    iAssert (interp W C wcsp) as "#Hinterp_wcsp".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wca0) as "#Hinterp_wca0".
    { iApply "Hrmap_interp"; eauto; done. }
    iAssert (interp W C wca1) as "#Hinterp_wca1".
    { iApply "Hrmap_interp"; eauto; done. }
    set (rmap0 := delete ct1 _).

    (* Open the switcher invariant *)
    iMod (na_inv_acc with "Hinv_switcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & >Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "[$] [$]") as "%"; simplify_eq.

    destruct cstk as [|frm cstk]; iEval (cbn) in "Hstk_interp"; cbn in Hlen_cstk.
    { (* No caller: the return fails *)
      replace a_tstk with (b_trusted_stack)%a by solve_addr.
      iMod "Hstk_interp".
      iApply (switcher_return_blocks_1_empty_spec with
        "[$HPC $Hctp $Hcsp $Hmtdc $Hstk_interp $Hcode]").
    }

    (* Non empty call-stack *)
    destruct Ws;[done|].
    destruct Cs;[done|].
    iDestruct "Hstk_interp" as "(Hstk_interp_next & Hcframe_interp)".
    destruct frm.
    rewrite /cframe_interp.
    iEval (cbn) in "Hcframe_interp".
    iDestruct "Hcframe_interp" as "[>Ha_tstk (>%HWF & Hcframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    simpl in Hfreq. destruct Hfreq as (Hfrelated & <- & Hccrel_known_to_known & Hfreq).
    pose proof (switcher_stk_bounds_frame b_stk e_stk a_stk Hb_a4 He_a1 (ex_intro _ _ Ha_stk4))
      as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).

    iDestruct (interp_monotone_continuation with "Hcont_K") as "Hcont_K"; eauto.
    rewrite /interp_continuation /interp_cont.
    iEval (cbn) in "Hcont_K"; rewrite Hccrel_known_to_known /is_untrusted_caller_frm /=.
    cbn.
    iDestruct "Hcont_K" as "(Hcont_K & #Hinterp_callee_wstk & Hexec_topmost_frm)".
    iEval (cbn) in "Hinterp_callee_wstk".

    (* Block 12: pop the trusted stack *)
    iApply (switcher_return_blocks_1_spec with
      "[- $HPC $Hctp $Hcsp $Hmtdc $Ha_tstk $Hcode]"); [done|done|].
    iNext; iIntros (a_tstk1)
      "(%Ha_tstk1 & %Htstk_ae & HPC & Hctp & Hcsp & Hmtdc & Ha_tstk & Hcode & Hlc)".

    (* Obtain the caller's stack frame *)
    iDestruct (open_world_interp_cframe with "[$Hcframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3
          & Hstk'
          & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.
    rewrite -/(interp_cont).
    iDestruct (switcher_stk_cells_region_4 with "Hstk'") as "Hcells"; first done.
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & Hstk & Hres))"; eauto.

    (* Blocks 12-15: restore, clear and return *)
    iApply (switcher_return_blocks_2_spec with
      "[- $HPC $Hcgp $Hcra $Hcs1 $Hcs0 $Hct0 $Hct1 $Hca2 $Hctp $Hcsp $Hcells $Hstk $Hrmap $Hcode]");
      first done.
    { subst rmap0.
      clear -Hfull_rmap.
      repeat (rewrite dom_delete_L).
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    iNext; iIntros (arg_rmap')
      "(%Harg_rmap' & HPC & Hcra & Hcgp & Hcs0 & Hcs1 & Hcsp & Hstk_register_save & Hstk & Hrmap & Hcode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iPoseProof (lc_weaken 1 with "Hlc") as "Hlc"; first lia.

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

      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv lv' with "Hres") as "Hres"; auto.

      iSpecialize ("Hexec_topmost_frm" $! W (related_sts_pub_refl_world W)).
      iApply ("Hexec_topmost_frm" with
               "[$HPC $Hcra $Hcsp $Hcgp $Hcs0 $Hcs1 $Hca0 $Hca1 $Hinterp_wca0 $Hinterp_wca1
      $Hrmap $Hstk_register_save $Hstk $Hworld_interp $Hres $Hcont_K $Hcstk_frag $Hna]").
      iPureIntro;rewrite Harg_rmap'; set_solver.

    - (* Case where caller is untrusted, we close the world and jump to the
         return address *)
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
      rewrite -open_world_interp_empty.

      rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq.
      iApply (switcher_jump_to_caller_spec with
               "Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk
                Hinterp_wca0 Hinterp_wca1 HPC Hcra Hcgp Hcs0 Hcs1 Hcsp Hca0 Hca1
                Hrmap Hworld_interp Hcont_K Hcstk_frag Hna Hlc"); done.
  Qed.

  Lemma interp_switcher_return (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_return).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /=.
    iIntros "!> %regs %W' % %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_return with "Hinv").
  Qed.


End fundamental.
