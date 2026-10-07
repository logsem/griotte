From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary region_invariants_binary.
From griotte Require Import interp_weakening_binary.
From griotte Require Import wp_rules_interp_binary switcher_macros_spec_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import switcher_preamble_binary.
From griotte Require Import interp_switcher_return_binary switcher_helpers_binary.
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

  (** The switcher-call routine when the trusted stack is exhausted, in both
      runs: the switcher restores the caller's callee-saved registers from
      the shared callee-saved area, clears the other registers and returns
      to the caller with the error code [ENOTENOUGHTRUSTEDSTACK]. The
      switcher's state is unchanged. *)
  Lemma switcher_call_tstk_exhausted (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) (rmap smap : Reg)
    (b e a f f0 f1 f2 : Addr)
    (wcgp swcgp wcra swcra wcs1 swcs1 wcs0 swcs0 wca0 swca0 wca1 swca1 : Word) :
    (a + 1)%a = Some f →
    (f + 1)%a = Some f0 →
    (f0 + 1)%a = Some f1 →
    (f1 + 1)%a = Some f2 →
    dom rmap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} →
    dom smap = all_registers_s ∖ {[ PC ; cra ; cgp ; csp ; cs0 ; cs1 ; ca0 ; ca1 ]} →
    na_inv cerise_nais Nswitcher switcher_inv_binary -∗
    spec_ctx -∗
    interp W C (WCap RWL Local b e a, WCap RWL Local b e a) -∗
    ⤇ Seq (Instr Executable) -∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ (default 0%nat (switcher_labels !! ".Lswitch_trusted_stack_exhausted")))%a -∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher
      (a_switcher_call ^+ (default 0%nat (switcher_labels !! ".Lswitch_trusted_stack_exhausted")))%a -∗
    csp ↦ᵣ WCap RWL Local b e f2 -∗
    csp ↣ᵣ WCap RWL Local b e f2 -∗
    cgp ↦ᵣ wcgp -∗ cgp ↣ᵣ swcgp -∗
    cra ↦ᵣ wcra -∗ cra ↣ᵣ swcra -∗
    cs1 ↦ᵣ wcs1 -∗ cs1 ↣ᵣ swcs1 -∗
    cs0 ↦ᵣ wcs0 -∗ cs0 ↣ᵣ swcs0 -∗
    ca0 ↦ᵣ wca0 -∗ ca0 ↣ᵣ swca0 -∗
    ca1 ↦ᵣ wca1 -∗ ca1 ↣ᵣ swca1 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    world_interp W C -∗
    interp_continuation stk Ws Cs -∗
    na_own cerise_nais ⊤ -∗
    cstack_frag (map fst stk) -∗
    cstack_frag_spec (map snd stk) -∗
    ⌜frame_match Ws Cs stk W C⌝ -∗
    interp_conf W C.
  Proof.
    iIntros (Ha1 Ha2 Ha3 Ha4 Hdom_rmap Hdom_smap)
      "#Hinv_switcher #Hspec #Hspv Hj HPC HsPC Hcsp Hscsp Hcgp Hscgp Hcra Hscra Hcs1 Hscs1
       Hcs0 Hscs0 Hca0 Hsca0 Hca1 Hsca1 Hrmap Hsmap Hworld_interp Hcont Hna Hcstk Hcstk_spec %Hframe".
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
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hinv_switcher" as hinv_switcher.
    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
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
    iEval (simplify_map_eq) in "HPC".
    iEval (simplify_map_eq) in "HsPC".

    (* ----------------------------------------------  *)
    (* ------ Lswitch_trusted_stack_exhausted -------  *)
    (* ----------------------------------------------  *)
    focus_block_lockstep 16 "Hscode" "Hcode" as a_tstk_exhausted Ha_tstk_exhausted
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* Lea csp (-1)%Z; *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some f1); auto; solve_addr.
    (* Load cgp csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_load_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcgp Hscgp $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (%wcgp' & %swcgp' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcsp & Hscsp
      & Hcgp & Hscgp & #Hinterp_wcgp & Hworld_interp & _ & _)] /=".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    (* Lea csp (-1)%Z; *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some f0); auto; solve_addr+Ha3.
    (* Load cra csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_load_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcra Hscra $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (%wcra' & %swcra' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcsp & Hscsp
      & Hcra & Hscra & #Hinterp_wcra & Hworld_interp & _ & _)] /=".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    (* Lea csp (-1)%Z; *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some f); auto; solve_addr+Ha2.
    (* Load cs1 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_load_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcs1 Hscs1 $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (%wcs1' & %swcs1' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcsp & Hscsp
      & Hcs1 & Hscs1 & #Hinterp_wcs1 & Hworld_interp & _ & _)] /=".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    (* Lea csp (-1)%Z; *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: transitivity (Some a); auto; solve_addr+Ha1.
    (* Load cs0 csp; *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_load_interp_cap with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi Hcsp Hscsp Hcs0 Hscs0 $Hworld_interp]")
    ; try solve_pure; try solve_ndisj.
    { iFrame. by iApply (interp_lea with "Hspv"). }
    iIntros "!>" (v) "[-> | (%wcs0' & %swcs0' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcsp & Hscsp
      & Hcs0 & Hscs0 & #Hinterp_wcs0 & Hworld_interp & _ & _)] /=".
    { wp_pure; wp_end; iIntros "%Hcontr";done. }
    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").

    (* Mov ca0 ENOTENOUGHTRUSTEDSTACK; *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Mov ca1 0; *)
    iInstr_lockstep "Hscode" "Hcode".
    (* Jmp Lswitch_callee_dead_zeros_z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: set (Lswitch_callee_dead_zeros := default 0 (switcher_labels !! ".Lswitch_callee_dead_zeros"));
         transitivity (Some ((a_switcher_call ^+ Lswitch_callee_dead_zeros)%a)); auto;
         subst Lswitch_callee_dead_zeros; rewrite /switcher_labels; simplify_map_eq;
         solve_addr.
    iEval (simplify_map_eq) in "HPC".
    iEval (simplify_map_eq) in "HsPC".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ---- clear registers  ---- *)
    focus_block_lockstep 14 "Hscode" "Hcode" as a7 Ha7 "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    iApply (clear_registers_post_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hrmap $Hsmap $Hcode $Hscode]")
    ; try solve_pure.
    iNext; iIntros "H".
    iDestruct "H" as (arg_rmap' arg_smap')
      "(%Harg_rmap' & %Harg_smap' & Hj & HPC & HsPC & Hrmap & Hsmap & Hcode & Hscode)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Both register files are cleared: they are the same map *)
    iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hrmap_zero]".
    iDestruct (big_sepM_sep with "Hsmap") as "[Hsmap %Hsmap_zero]".
    assert (arg_smap' = arg_rmap') as ->.
    { symmetry; apply zero_rmaps_eq; auto. by rewrite Harg_rmap' Harg_smap'. }
    clear Hsmap_zero Harg_smap'.

    focus_block_lockstep 15 "Hscode" "Hcode" as a10 Ha10 "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    (* Jalr cnull cra *)
    assert (is_Some (arg_rmap' !! cnull)) as [wcnull Hcnull]
        by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
    iDestruct (big_sepM_delete _ _ cnull with "Hrmap") as "[Hcnull Hrmap]"; first done.
    iDestruct (big_sepM_delete _ _ cnull with "Hsmap") as "[Hscnull Hsmap]"; first done.
    iInstr_spec "Hscode".
    iInstr "Hcode" with "Hlc".
    iDestruct (big_sepM_insert_delete with "[$Hrmap $Hcnull]") as "Hrmap".
    iDestruct (big_sepM_insert_delete with "[$Hsmap $Hscnull]") as "Hsmap".
    pose proof (Hrmap_zero _ _ Hcnull) as Hwcnull; cbn in Hwcnull; subst wcnull.
    rewrite insert_id; last done.
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* Close the switcher's invariant *)
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext. iSplitL "Hmtdc Hcode Hb_switcher Htstk Hcstk_full Hstk_interp".
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
      - iExists _,_,_. iFrame "∗ # %". iPureIntro; split; auto.
    }

    (* Insert the registers in the register files *)
    iInsertList "Hrmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
    iInsertListSpec "Hsmap" [csp;cs1;cs0;ca1;ca0;cgp;cra].
    iDestruct (big_sepM_insert with "[$Hrmap $HPC]") as "Hrmap".
    { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }
    iDestruct (big_sepM_insert with "[$Hsmap $HsPC]") as "Hsmap".
    { apply not_elem_of_dom; rewrite !dom_insert_L Harg_rmap'; set_solver+. }

    iDestruct (interp_updatePcPerm with "Hinterp_wcra") as "Hinterp_wret".
    iMod (lc_fupd_elim_later with "Hlc Hinterp_wret") as "Hinterp_wret'".
    rewrite /interp_expression /interp_expr /=.
    match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↦ᵣ w)%I ] => set (rmap' := m) end.
    match goal with |- context [ ([∗ map] r↦w ∈ ?m, r ↣ᵣ w)%I ] => set (smap' := m) end.
    iApply ("Hinterp_wret'" $! stk Ws Cs rmap' smap'
             with "[- $Hspec $Hworld_interp $Hcont $Hna $Hcstk $Hcstk_spec $Hj]").
    rewrite /registers_pointsto /spec_registers_pointsto /rmap' /smap' !insert_insert_eq.
    iFrame "Hrmap Hsmap".
    iSplit; last (iPureIntro; done).
    iSplit; [|iSplit].
    * iIntros (r); iPureIntro.
      clear -Harg_rmap'.
      destruct (decide (r = PC)); simplify_map_eq; first done.
      destruct (decide (r = csp)); simplify_map_eq; first done.
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first done.
      destruct (decide (r = ca0)); simplify_map_eq; first done.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      apply elem_of_dom.
      rewrite Harg_rmap'.
      pose proof all_registers_s_correct.
      set_solver.
    * iIntros (r); iPureIntro.
      clear -Harg_rmap'.
      destruct (decide (r = PC)); simplify_map_eq; first done.
      destruct (decide (r = csp)); simplify_map_eq; first done.
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first done.
      destruct (decide (r = ca0)); simplify_map_eq; first done.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      apply elem_of_dom.
      rewrite Harg_rmap'.
      pose proof all_registers_s_correct.
      set_solver.
    * iIntros (r rv1 rv2 HrPC Hr1 Hr2); cbn in Hr1, Hr2.
      destruct (decide (r = csp)); simplify_map_eq.
      { iApply (interp_lea with "Hspv"); done. }
      destruct (decide (r = cs1)); simplify_map_eq; first done.
      destruct (decide (r = cs0)); simplify_map_eq; first done.
      destruct (decide (r = ca1)); simplify_map_eq; first iApply interp_int.
      destruct (decide (r = ca0)); simplify_map_eq; first iApply interp_int.
      destruct (decide (r = cgp)); simplify_map_eq; first done.
      destruct (decide (r = cra)); simplify_map_eq; first done.
      repeat match goal with H : arg_rmap' !! r = Some ?v |- _ =>
               apply Hrmap_zero in H; cbn in H; subst v end.
      iApply interp_int.
  Qed.

End fundamental.
