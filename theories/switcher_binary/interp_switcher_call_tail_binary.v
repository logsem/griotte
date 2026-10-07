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

  (** The switcher-call routine after pushing the caller's stack pointer on
      both trusted stacks: the switcher chops the stack, clears the callee's
      stack frame, unseals the entry point (the same in both runs), loads the
      callee's capabilities, clears the registers that are not arguments, and
      jumps to the callee, pushing the same frame on both call stacks. *)
  Lemma switcher_call_after_push (W : WORLD) (C : CmptName) (Nswitcher : namespace)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName) (rmap smap : Reg)
    (b e a f f0 f1 f2 a_tstk f3 f4 : Addr) (tstk_next ststk_next : list Word)
    (wct2 swct2 wctp swctp wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp wct1 swct1 : Word) :
    (b <= a < e)%a →
    (b <= f1 < e)%a →
    (a + 1)%a = Some f →
    (f + 1)%a = Some f0 →
    (f0 + 1)%a = Some f1 →
    (f1 + 1)%a = Some f2 →
    (ot_switcher < ot_switcher ^+ 1)%ot →
    (b_trusted_stack <= a_tstk)%a →
    (a_tstk <= e_trusted_stack)%a →
    (b_trusted_stack + length (map fst stk))%a = Some a_tstk →
    (a_tstk + 1)%a = Some f3 →
    (f3 + 1)%a = Some f4 →
    (f3 < e_trusted_stack)%a →
    dom rmap = all_registers_s ∖ {[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]} →
    dom smap = all_registers_s ∖ {[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]} →
    na_inv cerise_nais Nswitcher switcher_inv_binary -∗
    spec_ctx -∗
    seal_pred ot_switcher ot_switcher_propC -∗
    interp W C (WCap RWL Local b e a, WCap RWL Local b e a) -∗
    (∀ (r : RegName) (v1 v2 : Word),
       ⌜r ≠ PC⌝ → ⌜rmap !! r = Some v1⌝ → ⌜smap !! r = Some v2⌝ → interp W C (v1, v2)) -∗
    interp W C (wct1, swct1) -∗
    (▷ switcher_inv_binary ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) -∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) -∗
    codefrag a_switcher_call switcher_instrs -∗
    spec_codefrag a_switcher_call switcher_instrs -∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack f3 -∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack f3 -∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher -∗
    b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher -∗
    f3 ↦ₐ WCap RWL Local b e f2 -∗
    f3 ↣ₐ WCap RWL Local b e f2 -∗
    [[ f4, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    [[ f4, e_trusted_stack ]] ↣ₐ [[ ststk_next ]] -∗
    cstack_full (map fst stk) -∗
    cstack_full_spec (map snd stk) -∗
    cstack_interp (map fst stk) a_tstk -∗
    cstack_interp_spec (map snd stk) a_tstk -∗
    ⤇ Seq (Instr Executable) -∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 26)%a -∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 26)%a -∗
    csp ↦ᵣ WCap RWL Local b e f2 -∗
    csp ↣ᵣ WCap RWL Local b e f2 -∗
    ct2 ↦ᵣ wct2 -∗ ct2 ↣ᵣ swct2 -∗
    ctp ↦ᵣ wctp -∗ ctp ↣ᵣ swctp -∗
    cs0 ↦ᵣ wcs0 -∗ cs0 ↣ᵣ swcs0 -∗
    cs1 ↦ᵣ wcs1 -∗ cs1 ↣ᵣ swcs1 -∗
    cra ↦ᵣ wcra -∗ cra ↣ᵣ swcra -∗
    cgp ↦ᵣ wcgp -∗ cgp ↣ᵣ swcgp -∗
    ct1 ↦ᵣ wct1 -∗ ct1 ↣ᵣ swct1 -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    world_interp W C -∗
    interp_continuation stk Ws Cs -∗
    cstack_frag (map fst stk) -∗
    cstack_frag_spec (map snd stk) -∗
    ⌜frame_match Ws Cs stk W C⌝ -∗
    interp_conf W C.
  Proof.
    iIntros (bounds bounds' Ha1 Ha2 Ha3 Ha4 Hot_bounds Hbounds_tstk_b Hbounds_tstk_e Hlen_cstk Hastk Hf4
             Hf3_bound Hdom_rmap Hdom_smap)
      "#Hinv_switcher #Hspec #Hp_ot_switcher #Hspv #Hreg #Hct1v Hclose_switcher_inv Hna
       Hcode Hscode Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk
       Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp Hj HPC HsPC Hcsp Hscsp
       Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0 Hcs1 Hscs1 Hcra Hscra Hcgp Hscgp Hct1 Hsct1
       Hrmap Hsmap Hworld_interp Hcont Hcstk Hcstk_spec %Hframe".
    iPoseProof fundamental_ih as "IH".
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

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block_lockstep 4 "Hscode" "Hcode" as a_stack_chop Ha_stack_chop
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* --- GetE cs0 csp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: solve_addr.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block_lockstep 5 "Hscode" "Hcode" as a_clear_stk1 Ha_clear_stk1
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_stack_chop.
    iApply (clear_stack_interp_spec
             with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hcsp $Hscsp $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hworld_interp]")
    ; try solve_pure.
    iSplit.
    { iApply interp_weakeningEO;eauto. all: solve_addr. }
    iSplitL;cycle 1.
    { iIntros "!> %Hcontr"; done. }
    iIntros "!> ((Hj & HPC & HsPC & Hcsp & Hscsp & Hcs0 & Hcs1 & Hscs0 & Hscs1 & Hcode & Hscode) & Hworld_interp)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block_lockstep 6 "Hscode" "Hcode" as a_LoadCapPCC Ha_LoadCapPCC
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_clear_stk1.

    (* --- GetB cs1 PC --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_lea_success_reg with "[$Hspec $Hj $HsPC $Hsi $Hscs0 $Hscs1]")
      as "(Hj & HsPC & Hsi & Hscs1 & Hscs0)";
      [solve_ndisj|solve_pure|solve_pure|solve_pure| |solve_pure|solve_pure|].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]"); auto; [solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:= b_switcher); solve_addr.

    (* --- Load cs0 cs0 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block_lockstep 7 "Hscode" "Hcode" as a_unseal_entry Ha_unseal_entry
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_LoadCapPCC.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    rewrite /load_word. iSimpl in "Hcs0". iSimpl in "Hscs0".
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed
             with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi $Hcs0 $Hscs0 $Hct1 $Hsct1 $Hct1v]")
    ; try solve_pure; try solve_ndisj.
    { clear -Hot_bounds; solve_finz. }
    iIntros "!>" (ret) "[-> | (%wsb & %wsb' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcs0 & Hscs0
      & Hct1 & Hsct1 & -> & ->)]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }

    (* get the seal inv and compare with wsb *)
    iDestruct (interp_sealed_inv with "Hct1v") as "[_ Hsb]".
    iDestruct "Hsb" as (P HpersP) "(HmonoP & HPseal & %Hloc & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,(WSealable wsb, WSealable wsb'))).

    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (??????????? Heq Heq' Htbl_bounds Htbl_b1 Htbl_b1a Hnargs) "(Htbl1 & Htbl2 & Htbl3 & #Hentry & Hexec)".
    simpl fst in Heq, Heq'. simpl snd in Heq'.
    rewrite Heq in Heq'. inversion Heq'. subst wsb'.
    inversion Heq.

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">[Ha_tbl Hsa_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ------------------------------  *)
    (* ---- Lswitch_callee_load -----  *)
    (* ------------------------------  *)
    focus_block_lockstep 8 "Hscode" "Hcode" as a_callee_load Ha_callee_load
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_unseal_entry.

    (* --- GetB cgp ct1 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=b_tbl); solve_addr+Htbl_bounds.

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=(b_tbl ^+ 1)%a); solve_addr+Htbl_b1.

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea cra cs0 --- *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr_lockstep "Hscode" "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block_lockstep 9 "Hscode" "Hcode" as a_clear Ha_clear "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_callee_load.

    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↦ᵣ y)%I ] => set (rmap' := r) end.
    match goal with |- context [ ([∗ map] k↦y ∈ ?r , k ↣ᵣ y)%I ] => set (smap' := r) end.
    set (params := dom_arg_rmap 8).
    set (Pf := ((λ '(r,_), r ∈ params) : RegName * Word → Prop)).
    assert (∀ i, i ∈ dom_arg_rmap 8 → i ∈ all_registers_s ∖ {[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]})
      as Hparams_dom.
    { intros i Hi. apply elem_of_difference. split; [apply all_registers_s_correct|].
      clear -Hi. rewrite /dom_arg_rmap /= in Hi. set_solver. }
    assert (dom (filter Pf rmap') = dom_arg_rmap 8) as Hdom_params.
    { apply dom_filter_L. split.
      - intros Hi.
        assert (is_Some (rmap' !! i)) as [x Hx]
            by (apply elem_of_dom; rewrite /rmap' Hdom_rmap; by apply Hparams_dom).
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    assert (dom (filter Pf smap') = dom_arg_rmap 8) as Hdom_sparams.
    { apply dom_filter_L. split.
      - intros Hi.
        assert (is_Some (smap' !! i)) as [x Hx]
            by (apply elem_of_dom; rewrite /smap' Hdom_smap; by apply Hparams_dom).
        exists x. split;auto.
      - intros [? [? ?] ]. auto. }
    rewrite -(map_filter_union_complement Pf rmap').
    rewrite -(map_filter_union_complement Pf smap').
    iDestruct (big_sepM_union with "Hrmap") as "[Hparams Hrest]".
    { apply map_disjoint_filter_complement. }
    iDestruct (big_sepM_union with "Hsmap") as "[Hsparams Hsrest]".
    { apply map_disjoint_filter_complement. }
    iDestruct (big_sepM2_sepM_2 with "Hparams Hsparams") as "Hparams".
    { intros k. rewrite -!elem_of_dom Hdom_params Hdom_sparams. done. }

    rewrite encode_entry_point_eq_nargs;last lia.
    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ _ _ (nargs+1)
             with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode]"); try solve_pure.
    { exact Hdom_params. }
    { exact Hdom_sparams. }
    { lia. }
    iSplitL "Hct2".
    { replace (Z.of_nat nargs + 1)%Z with (Z.of_nat (nargs + 1))%Z by lia; iFrame. }
    iSplitL "Hsct2".
    { replace (Z.of_nat nargs + 1)%Z with (Z.of_nat (nargs + 1))%Z by lia; iFrame. }
    iSplitL "Hparams".
    { iApply (big_sepM2_impl with "Hparams").
      iIntros "!> %k %w1 %w2 %Hk1 %Hk2 [$ $]".
      destruct ( decide (k ∈ dom_arg_rmap (nargs + 1 - 1)) ); last done.
      apply map_lookup_filter_Some in Hk1 as [Hk1 HPf].
      apply map_lookup_filter_Some in Hk2 as [Hk2 _].
      iApply ("Hreg" $! k); iPureIntro.
      - clear -HPf; rewrite /Pf /params /dom_arg_rmap /= in HPf; set_solver.
      - rewrite map_filter_union_complement; exact Hk1.
      - rewrite map_filter_union_complement; exact Hk2.
    }
    iIntros "!> (%arg_rmap' & %arg_smap' & %Hisarg_rmap' & %Hisarg_smap' & Hj & HPC & HsPC
      & Hct2 & Hsct2 & Hparams & Hcode & Hscode)".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ----------------------------------- *)
    (* ---- clear_registers_pre_call ----- *)
    (* ----------------------------------- *)
    focus_block_lockstep 10 "Hscode" "Hcode" as a_clear' Ha_clear' "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_clear.

    rewrite /rmap' /smap'.
    assert (dom (filter (λ v, ¬ Pf v) rmap)
            = (all_registers_s ∖ {[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]}) ∖ dom_arg_rmap 8)
      as Hdom_rest.
    { rewrite -Hdom_rmap. apply dom_filter_L. intros i. rewrite elem_of_difference elem_of_dom. split.
      - intros [ [x Hx] Hni]. exists x; split; auto.
      - intros (x & Hx & Hni). split; [eauto|done]. }
    assert (dom (filter (λ v, ¬ Pf v) smap)
            = (all_registers_s ∖ {[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]}) ∖ dom_arg_rmap 8)
      as Hdom_srest.
    { rewrite -Hdom_smap. apply dom_filter_L. intros i. rewrite elem_of_difference elem_of_dom. split.
      - intros [ [x Hx] Hni]. exists x; split; auto.
      - intros (x & Hx & Hni). split; [eauto|done]. }
    iDestruct (big_sepM_insert with "[$Hrest $Hct1]") as "Hrest".
    { apply map_lookup_filter_None; left; apply not_elem_of_dom; rewrite Hdom_rmap; set_solver. }
    iDestruct (big_sepM_insert with "[$Hsrest $Hsct1]") as "Hsrest".
    { apply map_lookup_filter_None; left; apply not_elem_of_dom; rewrite Hdom_smap; set_solver. }
    iInsertList "Hrest" [ctp;ct2;cs1;cs0].
    iInsertListSpec "Hsrest" [ctp;ct2;cs1;cs0].

    iApply (clear_registers_pre_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hrest $Hsrest]")
    ; try solve_pure.
    { rewrite !dom_insert_L Hdom_rest. pose proof all_registers_s_correct as Hall.
      rewrite /dom_arg_rmap /=. set_solver. }
    { rewrite !dom_insert_L Hdom_srest. pose proof all_registers_s_correct as Hall.
      rewrite /dom_arg_rmap /=. set_solver. }

    iIntros "!> (%rmap'' & %smap'' & %Hrmap'' & %Hsmap'' & Hj & HPC & HsPC & Hrest & Hsrest
      & Hcode & Hscode)".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* ------------------------------ *)
    (* ---- Lswitch_callee_call ----- *)
    (* ------------------------------ *)
    focus_block_lockstep 11 "Hscode" "Hcode" as a_callee_call Ha_callee_call
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_clear'.

    eset (frame :=
           {| wret := WInt 0;
              wcgp := WInt 0;
              wcs0 := WInt 0;
              wcs1 := WInt 0;
              b_stk := b ;
              a_stk := a ;
              e_stk := e ;
              ccrel := Unknown_to_Unknown
           |}).

    iSpecialize ("Hexec" with "[]").
    { iPureIntro. apply related_sts_priv_refl_world. }
    (* --- Jalr cra cra --- *)
    iInstr_lockstep "Hscode" "Hcode".
    iSpecialize ("Hexec" $! ((frame, frame) :: stk) (W :: Ws) (C :: Cs)).
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    rewrite /load_word. iSimpl in "Hcgp". iSimpl in "Hscgp".

    iMod (cstack_update _ _ (frame :: map fst stk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod (cstack_update_spec _ _ (frame :: map snd stk) with "Hcstk_full_spec Hcstk_spec")
      as "[Hcstk_full_spec Hcstk_spec]".
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk Hf3 Hsf3
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp]") as "Hna".
    { iNext.
      subst frame.
      iSplitL "Hmtdc Hcode Hb_switcher Htstk Hf3 Hcstk_full Hstk_interp".
      - iExists f3, _, _.
        rewrite (finz_incr_eq Hf4).
        iFrame "Hmtdc Hcode Hb_switcher Htstk Hcstk_full". iFrame "#".
        cbn [cstack_interp].
        replace (f3 ^+ -1)%a with a_tstk by solve_addr.
        rewrite /cframe_interp /cframe_stk_own /=.
        replace (a ^+ 4)%a with f2 by solve_addr.
        iFrame "Hf3 Hstk_interp".
        rewrite ?length_map in Hlen_cstk |- *.
        repeat iSplit; iPureIntro; try done; try solve_addr.
      - iExists f3, _, _.
        rewrite (finz_incr_eq Hf4).
        iFrame "Hsmtdc Hscode Hsb_switcher Hststk Hcstk_full_spec". iFrame "#".
        cbn [cstack_interp_spec].
        replace (f3 ^+ -1)%a with a_tstk by solve_addr.
        rewrite /cframe_interp_spec /cframe_stk_own_spec /=.
        replace (a ^+ 4)%a with f2 by solve_addr.
        iFrame "Hsf3 Hsstk_interp".
        rewrite ?length_map in Hlen_cstk |- *.
        repeat iSplit; iPureIntro; try done; try solve_addr.
    }

    iApply ("Hexec" $! _ _ a e).
    iSplitR; first iFrame "#".
    iSplitL "Hcont".
    { iFrame "Hcont". simpl.
      iSplit; first (iPureIntro; apply cframe_pair_cond_diag).
      iSplit.
      - iApply (interp_weakening with "IH Hspv");auto;solve_addr.
      - iIntros (W' HW' ???????) "(_ & HPC & _)".
        rewrite /interp_conf.
        wp_instr.
        iApply (wp_notCorrectPC with "[$]").
        { intros Hcontr;inversion Hcontr. }
        iIntros "!> HPC". wp_pure. wp_end. iIntros (Hcontr);done. }
    iSplitR.
    { iPureIntro. simpl. split;auto. apply related_sts_pub_refl_world. }
    iFrame.
    rewrite /execute_entry_point_register.
    iDestruct (big_sepM_sep with "Hrest") as "[Hrest #Hnil]".
    iDestruct (big_sepM_sep with "Hsrest") as "[Hsrest #Hsnil]".
    iDestruct (big_sepM2_sep with "Hparams") as "[Hparams Hparams']".
    iDestruct (big_sepM2_sep with "Hparams'") as "[Hsparams #Hval]".
    iDestruct (big_sepM2_sep_2 with "Hparams Hsparams") as "Hparams".
    iDestruct (big_sepM2_sepM with "Hparams") as "[Hparams Hsparams]".
    { intros k. rewrite -!elem_of_dom Hisarg_rmap' Hisarg_smap'. done. }
    iDestruct (big_sepM_union with "[$Hparams $Hrest]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap'' Hisarg_rmap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_union with "[$Hsparams $Hsrest]") as "Hsregs".
    { apply map_disjoint_dom. rewrite Hsmap'' Hisarg_smap'.
      rewrite /dom_arg_rmap. clear. set_solver. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscsp] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscra] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hscgp] Hsregs") as "Hsregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HsPC] Hsregs") as "Hsregs";[iFrame|].

    cbn.
    iFrame.
    iSplit;last (iPureIntro; split ;[repeat split|];[reflexivity..|solve_addr]).
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Hisarg_rmap' Hrmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap'' Hisarg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Hisarg_smap' Hsmap''.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hsmap'' Hisarg_smap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver].
    }
    repeat iSplit.
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_callee_call Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_callee_call Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro. clear -Ha4 Ha3 Ha2 Ha1 bounds. simplify_map_eq.
      replace f2 with (a^+4)%a by solve_addr.
      done.
    - iPureIntro. clear -Ha4 Ha3 Ha2 Ha1 bounds. simplify_map_eq.
      replace f2 with (a^+4)%a by solve_addr.
      done.
    - iApply (interp_weakening with "IH Hspv");auto
      ;[solve_addr+bounds' Ha4 Ha3 Ha2 Ha1|solve_addr-].
    - iIntros (r v1 v2 Hr Hv1 Hv2).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv1;[|set_solver+Hr Hr']).
      repeat (rewrite lookup_insert_ne in Hv2;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv1.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      apply lookup_union_Some in Hv2.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_smap' Hsmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv1 as [Hv1|Hv1]; cycle 1.
      { apply elem_of_dom_2 in Hv1; rewrite Hrmap'' in Hv1.
        exfalso; clear -Hr Hv1. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv1|apply IHnargs; set_solver+Hr]. }
      destruct Hv2 as [Hv2|Hv2]; cycle 1.
      { apply elem_of_dom_2 in Hv2; rewrite Hsmap'' in Hv2.
        exfalso; clear -Hr Hv2. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv2|apply IHnargs; set_solver+Hr]. }
      iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
      destruct (decide (r ∈ _)) as [|Hcontra]; first iFrame "#".
      set_solver+Hcontra Hr.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv as [Hv|Hv].
      + assert (is_Some (arg_smap' !! r)) as [v2 Hv2].
        { apply elem_of_dom; rewrite Hisarg_smap' -Hisarg_rmap'. by apply elem_of_dom_2 in Hv. }
        iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last (iDestruct "Hv" as "[$ _]").
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_smap' Hsmap'' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv as [Hv|Hv].
      + assert (is_Some (arg_rmap' !! r)) as [v1 Hv1].
        { apply elem_of_dom; rewrite Hisarg_rmap' -Hisarg_smap'. by apply elem_of_dom_2 in Hv. }
        iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last (iDestruct "Hv" as "[_ $]").
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hsnil") as "%";eauto; simplify_eq.
  Qed.

End fundamental.
