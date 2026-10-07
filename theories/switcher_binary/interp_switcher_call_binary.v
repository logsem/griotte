From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary region_invariants_binary bitblast.
From griotte Require Import interp_weakening_binary.
From griotte Require Import wp_rules_interp_binary switcher_macros_spec_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import interp_switcher_return_binary switcher_helpers_binary.
From griotte Require Import interp_switcher_call_exhausted_binary interp_switcher_call_tail_binary.
From griotte Require Import map_simpl register_tactics_binary.

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

  (** The switcher-call entry point is safe to execute, in both runs.

      The proof follows the unary one. The stack pointer of the caller is
      related to itself: it is either sealed, and the execution fails in the
      implementation run, or the same capability in both runs. All the
      switcher's checks then take the same branch in both runs. Both trusted
      stacks have the same top address [a_tstk], hence trusted stack
      exhaustion happens in both runs together.
      The switcher pushes the same frame in both call stacks: the caller is
      untrusted, its saved registers are not recorded in the frame (they are
      saved in the shared callee-saved area). *)
  Lemma interp_expr_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp_expr interp (interp_cont interp) W C
        (WCap XSRW_ Local b_switcher e_switcher a_switcher_call,
         WCap XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv_switcher %stk %Ws %Cs %rmap %smap
      (#Hspec & [%Hfull_rmap [%Hfull_smap #Hreg]] & Hrmap & Hsmap & Hj & Hworld_interp
      & Hcont & Hna & Hcstk & Hcstk_spec & %Hframe)".
    rewrite /registers_pointsto /spec_registers_pointsto.
    cbn in Hfull_rmap, Hfull_smap.
    iPoseProof fundamental_ih as "IH". (* used for weakening lemma later *)

    (* --- Extract the code from the invariant --- *)
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
    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %->.
    iDestruct (cstack_agree_spec with "Hcstk_full_spec Hcstk_spec") as %->.
    assert (sa_tstk = a_tstk) as ->.
    { eapply a_tstk_eq; [|exact Hslen_cstk|exact Hlen_cstk]. by rewrite !length_map. }
    clear Hsbounds_tstk_b Hsbounds_tstk_e.
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.

    iExtract "Hrmap" PC as "HPC".
    iExtract "Hsmap" PC as "HsPC".
    iEval (cbn) in "HPC". iEval (cbn) in "HsPC".
    get_rvals_pair Hfull_rmap Hfull_smap [csp;ct2;ctp].
    iExtractList "Hrmap" [csp;ct2;ctp] as ["Hcsp";"Hct2";"Hctp"].
    iExtractList "Hsmap" [csp;ct2;ctp] as ["Hscsp";"Hsct2";"Hsctp"].

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    iDestruct ("Hreg" $! csp with "[//] [//] [//]") as "#Hspv".

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

    (* The stack pointer is either sealed, or the same in both runs *)
    iDestruct (interp_eq_unless_sealed with "Hspv") as %[<-|(o & sb1 & sb2 & -> & ->)]; cycle 1.
    { focus_block_0 "Hcode" as "Hcode" "Hcls".
      (* --- GetP ct2 csp --- *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
      iIntros "!>" (v) "[-> | (%p0 & %Hp0 & %Hcap & -> & HPC & Hi & Hcsp & Hct2)] /=".
      { wp_pure. wp_end. iIntros "%Hcontr";done. }
      done.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0_lockstep "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* --- GetP ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%p0 & %Hp0 & Hcap_wstk & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* --- GetP ct2 csp --- *)
    iInstr_spec "Hscode".
    { exact Hp0. }

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((p0 - encodePerm RWL)%Z = 0)) as [Hp0'|];cycle 1.
    { (* p ≠ RWL *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: intros Hcontr; inversion Hcontr; done.
      subst hcont hscont.
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

      (* -----------------------------------  *)
      (* ------ Lcommon_force_unwind -------  *)
      (* -----------------------------------  *)
      focus_block_lockstep 17 "Hscode" "Hcode" as a_force_unwind Ha_force_unwind
        "Hscode" "Hscls" "Hcode" "Hcls".
      iHide "Hcls" as hcont. iHide "Hscls" as hscont.
      get_rvals_pair Hfull_rmap Hfull_smap [ca0;ca1].
      iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
      iExtractList "Hsmap" [ca0;ca1] as ["Hsca0";"Hsca1"].
      (* Mov ca0 ECOMPARTMENTFAIL; *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Mov ca1 0; *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp Lswitcher_after_compartment_call_z *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: transitivity (Some a_switcher_return); last done;
           pose proof switcher_return_entry_point;
           solve_addr.
      subst hcont hscont.
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
      iMod ("Hclose_switcher_inv"
             with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                    Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
      { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      }

      iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
      iInsertListSpec "Hsmap" [csp;ctp;ct2;ca0;ca1;PC].
      iApply (interp_expr_switcher_return with "Hinv_switcher").
      iFrame "∗%#".
      rewrite /interp_reg /=.
      iSplit; [|iSplit].
      + iIntros (r) ; iPureIntro.
        destruct (decide (r = PC)); first by simplify_map_eq.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_rmap.
      + iIntros (r) ; iPureIntro.
        destruct (decide (r = PC)); first by simplify_map_eq.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_smap.
      + iIntros (r w1 w2 HrPC Hr1 Hr2).
        destruct (decide (r = ca1)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ca0)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ct2)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ctp)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = csp)); simplify_map_eq; first done.
        iApply "Hreg"; eauto.
    }

    (* p = RWL *)
    rewrite Hp0'.
    iInstr_lockstep "Hscode" "Hcode".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block_lockstep 1 "Hscode" "Hcode" as a_csp_check_loc Ha_csp_check_loc
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* --- GetL ct2 csp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_Get_unknown with "[$HPC $Hi $Hct2 $Hcsp]"); try solve_pure.
    iIntros "!>" (v) "[-> | (%g0 & %Hg0 & _ & -> & HPC & Hi & Hcsp & Hct2)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecialize ("Hcode" with "[$]").
    (* --- GetL ct2 csp --- *)
    iInstr_spec "Hscode".
    { exact Hg0. }

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Jnz 2 ct2 --- *)
    destruct (decide ((g0 - encodeLoc Local)%Z = 0)) as [Hg0'|];cycle 1.
    { (* g ≠ Local *)
      iInstr_lockstep "Hscode" "Hcode".
      1,3: intros Hcontr; inversion Hcontr; done.
      1,2: set (Lcommon_force_unwind := default 0 (switcher_labels !! ".Lcommon_force_unwind"));
           transitivity (Some ((a_switcher_call ^+ Lcommon_force_unwind)%a)); auto;
           subst Lcommon_force_unwind; rewrite /switcher_labels; simplify_map_eq;
           solve_addr+Ha_csp_check_loc Hcont_switcher_region.
      iEval (simplify_map_eq) in "HPC".
      iEval (simplify_map_eq) in "HsPC".
      subst hcont hscont.
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

      (* -----------------------------------  *)
      (* ------ Lcommon_force_unwind -------  *)
      (* -----------------------------------  *)
      focus_block_lockstep 17 "Hscode" "Hcode" as a_force_unwind Ha_force_unwind
        "Hscode" "Hscls" "Hcode" "Hcls".
      iHide "Hcls" as hcont. iHide "Hscls" as hscont.
      get_rvals_pair Hfull_rmap Hfull_smap [ca0;ca1].
      iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
      iExtractList "Hsmap" [ca0;ca1] as ["Hsca0";"Hsca1"].
      (* Mov ca0 ECOMPARTMENTFAIL; *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Mov ca1 0; *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp Lswitcher_after_compartment_call_z *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: transitivity (Some a_switcher_return); last done;
           pose proof switcher_return_entry_point;
           solve_addr.
      subst hcont hscont.
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
      iMod ("Hclose_switcher_inv"
             with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                    Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
      { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      }

      iInsertList "Hrmap" [csp;ctp;ct2;ca0;ca1;PC].
      iInsertListSpec "Hsmap" [csp;ctp;ct2;ca0;ca1;PC].
      iApply (interp_expr_switcher_return with "Hinv_switcher").
      iFrame "∗%#".
      rewrite /interp_reg /=.
      iSplit; [|iSplit].
      + iIntros (r) ; iPureIntro.
        destruct (decide (r = PC)); first by simplify_map_eq.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_rmap.
      + iIntros (r) ; iPureIntro.
        destruct (decide (r = PC)); first by simplify_map_eq.
        destruct (decide (r = ca1)); first by simplify_map_eq.
        destruct (decide (r = ca0)); first by simplify_map_eq.
        destruct (decide (r = ct2)); first by simplify_map_eq.
        destruct (decide (r = ctp)); first by simplify_map_eq.
        destruct (decide (r = csp)); first by simplify_map_eq.
        simplify_map_eq.
        apply Hfull_smap.
      + iIntros (r w1 w2 HrPC Hr1 Hr2).
        destruct (decide (r = ca1)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ca0)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ct2)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = ctp)); first (simplify_map_eq ; iApply interp_int).
        destruct (decide (r = csp)); simplify_map_eq; first done.
        iApply "Hreg"; eauto.
    }
    rewrite Hg0'.
    (* g = Local *)
    iInstr_lockstep "Hscode" "Hcode".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    get_rvals_pair Hfull_rmap Hfull_smap [cs0;cs1;cra;cgp;ct1].
    iExtractList "Hrmap" [cs0;cs1;cra;cgp;ct1] as ["Hcs0";"Hcs1";"Hcra";"Hcgp";"Hct1"].
    iExtractList "Hsmap" [cs0;cs1;cra;cgp;ct1] as ["Hscs0";"Hscs1";"Hscra";"Hscgp";"Hsct1"].

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block_lockstep 2 "Hscode" "Hcode" as a_entry_first_spill Ha_entry_first_spill
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_csp_check_loc.

    (* --- Store csp cs0 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_store_interp with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcs0 Hscs0 $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. iFrame "#". by iApply "Hreg";eauto. }
    iIntros "!>" (v) "[-> | (% & % & % & % & % & -> & %Heq_csp & -> & Hj & HPC & HsPC & Hi & Hsi
      & Hcs0 & Hscs0 & Hcsp & Hscsp & Hworld_interp & %Hcanstore & _ & %bounds)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    clear Heq_csp.
    cbn in Hp0,Hg0; simplify_eq.
    assert (encodePerm p = encodePerm RWL)%Z as ?%encodePerm_inj by lia; simplify_eq; clear Hp0'.
    assert (encodeLoc g = encodeLoc Local)%Z as ?%encodeLoc_inj by lia; simplify_eq; clear Hg0'.

    (* --- Lea csp 1 --- *)
    destruct (a + 1)%a eqn:Ha1;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Store csp cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcs1 Hscs1 $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & Hj & HPC & HsPC & Hi & Hsi & Hcs1 & Hscs1
      & Hcsp & Hscsp & Hworld_interp & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f + 1)%a eqn:Ha2;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Store csp cra --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcra Hscra $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & Hj & HPC & HsPC & Hi & Hsi & Hcra & Hscra
      & Hcsp & Hscsp & Hworld_interp & _)] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f0 + 1)%a eqn:Ha3;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Store csp cgp --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_store_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcgp Hscgp $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. iSplit;[by iApply "Hreg";eauto|].
      by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (-> & Hj & HPC & HsPC & Hi & Hsi & Hcgp & Hscgp
      & Hcsp & Hscsp & Hworld_interp & _ & _ & %bounds')] /=".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").

    (* --- Lea csp 1 --- *)
    destruct (f1 + 1)%a eqn:Ha4;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_z with "[$HPC $Hi $Hcsp]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done. }
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block_lockstep 3 "Hscode" "Hcode" as a_tstack_push Ha_tstack_push
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_entry_first_spill.

    (* --- ReadSR ct2 mtdc --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- GetA cs0 ct2 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Add cs0 cs0 1%Z --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- GetE ctp ct2 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Lt ctp cs0 ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Jnz 2%Z ctp --- *)
    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; iEval (cbn) in "Hsctp"
    ; cycle 1.
    {
      (* --- Jnz 2%Z ctp --- *)
      iInstr_lockstep "Hscode" "Hcode".
      (* --- Jmp  Lswitch_trusted_stack_exhausted_z --- *)
      iInstr_lockstep "Hscode" "Hcode".
      1,2: set (Lswitch_trusted_stack_exhausted := default 0 (switcher_labels !! ".Lswitch_trusted_stack_exhausted"));
           transitivity (Some ((a_switcher_call ^+ Lswitch_trusted_stack_exhausted)%a)); auto;
           subst Lswitch_trusted_stack_exhausted; rewrite /switcher_labels; simplify_map_eq;
           solve_addr+Ha_tstack_push Hsize.
      subst hcont hscont.
      unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
      iMod ("Hclose_switcher_inv"
             with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                    Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
      { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
        - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      }
      get_rvals_pair Hfull_rmap Hfull_smap [ca0;ca1].
      iExtractList "Hrmap" [ca0;ca1] as ["Hca0";"Hca1"].
      iExtractList "Hsmap" [ca0;ca1] as ["Hsca0";"Hsca1"].
      iInsertList "Hrmap" [ct1;ctp;ct2].
      iInsertListSpec "Hsmap" [ct1;ctp;ct2].
      iApply (switcher_call_tstk_exhausted
               with "Hinv_switcher Hspec Hspv Hj HPC HsPC Hcsp Hscsp Hcgp Hscgp Hcra Hscra Hcs1 Hscs1
                     Hcs0 Hscs0 Hca0 Hsca0 Hca1 Hsca1 Hrmap Hsmap Hworld_interp Hcont Hna Hcstk Hcstk_spec [//]")
      ; try eassumption.
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
    }
    (* --- Jnz 2%Z ctp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Hastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Store ct2 csp --- *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    iDestruct (big_sepL2_length with "Hststk") as %Hslen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    erewrite finz_incr_eq in Hslen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    rewrite finz_seq_between_length in Hslen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    destruct ststk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hslen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    iDestruct (spec_region_pointsto_cons _ f4 with "Hststk") as "[Hsf3 Hststk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr_lockstep "Hscode" "Hcode".
    1,2: solve_addr.

    (* --- WriteSR mtdc ct2 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* The rest of the switcher-call routine *)
    changePCto (a_switcher_call ^+ 26)%a.
    iDestruct ("Hreg" $! ct1 with "[//] [//] [//]") as "#Hct1v".
    iApply (switcher_call_after_push
             with "Hinv_switcher Hspec Hp_ot_switcher Hspv [] Hct1v Hclose_switcher_inv Hna Hcode Hscode
                   Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk Hcstk_full Hcstk_full_spec
                   Hstk_interp Hsstk_interp Hj HPC HsPC Hcsp Hscsp Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0
                   Hcs1 Hscs1 Hcra Hscra Hcgp Hscgp Hct1 Hsct1 Hrmap Hsmap Hworld_interp Hcont
                   Hcstk Hcstk_spec [//]")
    ; try eassumption.
    { apply Z.ltb_lt in Hsize_tstk. solve_addr+Hsize_tstk Hastk. }
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
    { iIntros (r v1 v2 Hr Hv1 Hv2).
      iApply "Hreg"; iPureIntro; first done.
      - repeat (apply lookup_delete_Some in Hv1 as [_ Hv1]); done.
      - repeat (apply lookup_delete_Some in Hv2 as [_ Hv2]); done.
    }
  Qed.

  Lemma interp_switcher_call (W : WORLD) (C : CmptName) (Nswitcher : namespace) :
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ⊢ interp W C (WSentry XSRW_ Local b_switcher e_switcher a_switcher_call,
                  WSentry XSRW_ Local b_switcher e_switcher a_switcher_call).
  Proof.
    iIntros "#Hinv".
    rewrite fixpoint_interp1_eq /= /interp1_pair /=.
    iSplit; first done.
    iIntros "!> %W' % %g' %".
    destruct g'; first done.
    iNext ; iApply (interp_expr_switcher_call with "Hinv").
  Qed.

End fundamental.
