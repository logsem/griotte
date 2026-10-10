From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base list_relations.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary monotone_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import memory_region memory_region_binary rules proofmode.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import switcher_return_states_binary switcher_return_blocks_1_binary
  switcher_return_blocks_2_binary.
From griotte Require Import map_simpl register_tactics register_tactics_binary proofmode_binary.
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
    (* Outline of the proof:
       - open the switcher invariant of both runs;
       - when the call-stack is empty: [switcher_return_blocks_1_empty_spec];
       - [switcher_return_blocks_1_spec]: pop both trusted stacks;
       - [open_world_interp_cframe], [open_world_interp_callee_stack]: obtain
         the caller's stack frame;
       - [switcher_return_blocks_2_spec]: restore the callee-save registers,
         clear the stack frame and the registers, and jump to the caller;
       - close the switcher invariant;
       - when the caller is trusted, use the continuation relation;
       - when the caller is untrusted, close the world and
         [switcher_jump_to_caller_spec]. *)
    iIntros "#Hinv_switcher %stk %Ws %Cs %rmap %smap
      (#Hspec & [%Hfull_rmap [%Hfull_smap #Hrmap_interp]] & Hrmap & Hsmap & Hj & Hworld_interp
      & Hcont_K & Hna & Hcstk & Hcstk_spec & %Hfreq)".
    rewrite /registers_pointsto /spec_registers_pointsto.
    cbn in Hfull_rmap, Hfull_smap.

    (* Extract the registers *)
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

    (* Open the switcher invariant *)
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
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hslen_cstk Hsbounds_tstk_b Hsbounds_tstk_e.

    destruct stk as [|[frm1 frm2] stk]
    ; iEval (cbn) in "Hstk_interp"; iEval (cbn) in "Hsstk_interp"; cbn in Hlen_cstk.
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
    iDestruct "Hcframe_interp" as "[>Ha_tstk (>%HWF & Hcframe_interp)]".
    iDestruct "Hscframe_interp" as "[>Hsa_tstk (_ & Hscframe_interp)]".
    destruct HWF as (Hb_a4 & He_a1 & [a_stk4 Ha_stk4]).
    pose proof (switcher_stk_bounds_frame b_stk e_stk a_stk Hb_a4 He_a1 (ex_intro _ _ Ha_stk4))
      as Hstk_bounds.
    pose proof Hstk_bounds as (_ & _ & Ha4).
    iEval (cbn) in "Hinterp_callee_wstk".
    rewrite /is_untrusted_caller_frm /=.

    (* Block 12: pop both trusted stacks *)
    iApply (switcher_return_blocks_1_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hctp $Hsctp $Hcsp $Hscsp $Hmtdc $Hsmtdc $Ha_tstk $Hsa_tstk
        $Hcode $Hscode]"); [done|done|].
    iNext; iIntros (a_tstk1)
      "(%Ha_tstk1 & %Htstk_ae & Hj & HPC & HsPC & Hctp & Hsctp & Hcsp & Hscsp & Hmtdc & Hsmtdc
      & Ha_tstk & Hsa_tstk & Hcode & Hscode & Hlc)".

    (* Obtain the caller's stack frame *)
    iDestruct (open_world_interp_cframe with
                "[$Hinterp_callee_wstk $Hcframe_interp $Hscframe_interp $Hworld_interp]")
      as "(%wastk & %wastk1 & %wastk2 & %wastk3 & %swastk & %swastk1 & %swastk2 & %swastk3
          & Hstk' & Hsstk' & Hclose_res & %Hwastks & Hworld_interp)";
    eauto.
    iDestruct (switcher_stk_cells_region_4 with "Hstk'") as "Hcells"; first done.
    iDestruct (switcher_stk_cells_region_4_spec with "Hsstk'") as "Hscells"; first done.
    iDestruct (open_world_interp_callee_stack
                with "[$Hinterp_callee_wstk $Hworld_interp]")
      as "(Hworld_interp & (%lv & %slv & Hstk & Hsstk & Hres))"; eauto.

    (* Blocks 12-15: restore, clear and return *)
    iApply (switcher_return_blocks_2_spec with
      "[- $Hspec $Hj $HPC $HsPC $Hcgp $Hscgp $Hcra $Hscra $Hcs1 $Hscs1 $Hcs0 $Hscs0
        $Hct0 $Hsct0 $Hct1 $Hsct1 $Hca2 $Hsca2 $Hctp $Hsctp $Hcsp $Hscsp
        $Hcells $Hscells $Hstk $Hsstk $Hrmap $Hsmap $Hcode $Hscode]"); first done.
    { clear -Hfull_rmap.
      repeat (rewrite dom_delete_L).
      apply regmap_full_dom in Hfull_rmap.
      rewrite Hfull_rmap.
      set_solver.
    }
    { clear -Hfull_smap.
      repeat (rewrite dom_delete_L).
      apply regmap_full_dom in Hfull_smap.
      rewrite Hfull_smap.
      set_solver.
    }
    iNext; iIntros (arg_rmap')
      "(%Harg_rmap' & Hj & HPC & HsPC & Hcra & Hscra & Hcgp & Hscgp & Hcs0 & Hscs0 & Hcs1 & Hscs1
      & Hcsp & Hscsp & Hstk_register_save & Hsstk_register_save & Hstk & Hsstk & Hrmap
      & Hcode & Hscode & Hlc')".
    iCombine "Hlc Hlc'" as "Hlc".
    iPoseProof (lc_weaken 1 with "Hlc") as "Hlc"; first lia.

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
      iApply ("Hexec_topmost_frm" $! (wca0, swca0) (wca1, swca1) arg_rmap' with
               "[$Hspec $HPC $HsPC $Hcra $Hscra $Hcsp $Hscsp $Hcgp $Hscgp $Hcs0 $Hscs0 $Hcs1 $Hscs1
                 $Hca0 $Hsca0 $Hca1 $Hsca1 $Hinterp_wca0 $Hinterp_wca1
                 $Hstk_register_save $Hsstk_register_save $Hstk $Hsstk $Hworld_interp $Hres $Hcont_K
                 $Hcstk_frag $Hcstk_frag_spec $Hj $Hna $Hrmap]").
      iPureIntro; rewrite Harg_rmap'; set_solver.

    - (* The caller is untrusted: close the world and jump to the caller *)
      iDestruct (big_sepL2_length with "Hstk") as "%Hlen_lv'".
      iDestruct (StackOpenWorldResources_zeros _ _ _ lv slv lv' lv' with "Hres") as "Hres"; auto.
      iDestruct (close_world_interp_opening_resources with "[$Hworld_interp $Hstk $Hsstk $Hres]")
        as "Hworld_interp".
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

      iApply (switcher_jump_to_caller_spec W C stk Ws Cs arg_rmap'
                (wastk2, swastk2) (wastk3, swastk3) (wastk, swastk) (wastk1, swastk1)
                (WCap RWL Local b_stk e_stk a_stk, WCap RWL Local b_stk e_stk a_stk)
                (wca0, swca0) (wca1, swca1) with
               "Hspec Hinterp_wstk2 Hinterp_wstk3 Hinterp_wstk0 Hinterp_wstk1 Hinterp_callee_wstk
                Hinterp_wca0 Hinterp_wca1 HPC HsPC Hcra Hscra Hcgp Hscgp Hcs0 Hscs0
                Hcs1 Hscs1 Hcsp Hscsp Hca0 Hsca0 Hca1 Hsca1
                Hrmap Hworld_interp Hcont_K Hcstk_frag Hcstk_frag_spec Hj Hna Hlc"); first done.
      rewrite /is_untrusted_caller_frm /= Hccrel in Hfreq; done.
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
