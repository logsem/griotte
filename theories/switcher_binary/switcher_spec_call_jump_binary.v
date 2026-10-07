From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Export logrel_binary region_invariants_binary.
From griotte Require Import interp_weakening_binary memory_region memory_region_binary.
From griotte Require Import wp_rules_interp_binary switcher_macros_spec_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import fundamental_binary.
From griotte Require Import switcher_preamble_binary world_interp_stack_binary.
From griotte Require Import switcher_helpers_binary.
From griotte Require Import map_simpl register_tactics_binary.

Section Switcher.
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

  (** A revoked and cleared stack region becomes safe-to-share once it is
      reinstated as temporary. *)
  Lemma StackRevokedResources_interp (W : WORLD) (C : CmptName) (b e a : Addr) :
    StackRevokedResources W C (finz.seq_between b e) -∗
    interp (std_update_multiple W (finz.seq_between b e) Temporary) C
      (WCap RWL Local b e a, WCap RWL Local b e a).
  Proof.
    rewrite /StackRevokedResources /StackWorldResources zip_with_replicate big_sepL2_replicate_r; last done.
    iIntros "[_ Hres]".
    rewrite /interp fixpoint_interp1_eq interp1_eq /=.
    iSplit; last done.
    iApply (big_sepL_impl with "Hres").
    iIntros "!>" (k a' Ha) "Hr".
    iDestruct "Hr" as (φ p) "(Hφ & Hmono & Hrel & (HmonoR & Hzcond & Hrcond & Hwcond & Hpers) & %Hperm_flow)".
    iExists p,φ.
    iFrame "∗#%".
    iSplit.
    { erewrite readAllowed_flowsto; eauto. }
    iSplit.
    { erewrite writeAllowed_flowsto; eauto. }
    iSplitL "HmonoR".
    { rewrite /monoReq.
      erewrite isWL_flowsto; eauto.
      rewrite std_sta_update_multiple_lookup_in_i; first done.
      apply list_elem_of_lookup. eauto. }
    iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply list_elem_of_lookup. eauto.
  Qed.

  (** The end of the switcher-call routine of a trusted caller: the switcher
      clears the registers that are not arguments, and jumps to the callee in
      both runs. The pair of frames pushed on the call stacks records the
      callee-saved registers of each run, and the same stack bounds. The
      continuation of the caller, run when the callee returns, is given by
      [Hpost]. *)
  Lemma switcher_cc_jump_callee
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (b_stk e_stk a_stk a_stk4 : Addr)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (a_tstk f3 f4 : Addr) (tstk_next ststk_next : list Word)
    (bpcc epcc a_pcc bcgp ecgp : Addr) (nargs : nat)
    (wctp swctp wcs0 swcs0 wcs1 swcs1 wct1 swct1 : Word)
    :
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    (b_stk <= a_stk)%a →
    (a_stk + 4)%a = Some a_stk4 →
    (a_stk ^+ 3 < e_stk)%a →
    (b_trusted_stack <= a_tstk)%a →
    (b_trusted_stack + length (map fst stk))%a = Some a_tstk →
    (a_tstk + 1)%a = Some f3 →
    (f3 + 1)%a = Some f4 →
    (f3 < e_trusted_stack)%a →
    nargs <= 7 →
    dom rmap = all_registers_s ∖ ({[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]} ∪ dom_arg_rmap 8) →
    dom smap = all_registers_s ∖ ({[PC; csp; ct2; ctp; cs0; cs1; cra; cgp; ct1]} ∪ dom_arg_rmap 8) →
    is_arg_rmap arg_rmap 8 →
    is_arg_rmap arg_smap 8 →
    revoked_addresses W callee_stk_region →

    na_inv cerise_nais Nswitcher switcher_inv_binary -∗
    spec_ctx -∗
    seal_pred ot_switcher ot_switcher_propC -∗
    (▷ switcher_inv_binary ∗ na_own cerise_nais (⊤ ∖ ↑Nswitcher) ={⊤}=∗ na_own cerise_nais ⊤) -∗
    na_own cerise_nais (⊤ ∖ ↑Nswitcher) -∗
    codefrag a_switcher_call switcher_instrs -∗
    spec_codefrag a_switcher_call switcher_instrs -∗
    mtdc ↦ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack f3 -∗
    mtdc ↣ₛᵣ WCap RWL Local b_trusted_stack e_trusted_stack f3 -∗
    b_switcher ↦ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher -∗
    b_switcher ↣ₐ WSealRange (true,true) Global ot_switcher (ot_switcher^+1)%ot ot_switcher -∗
    f3 ↦ₐ WCap RWL Local b_stk e_stk a_stk4 -∗
    f3 ↣ₐ WCap RWL Local b_stk e_stk a_stk4 -∗
    [[ f4, e_trusted_stack ]] ↦ₐ [[ tstk_next ]] -∗
    [[ f4, e_trusted_stack ]] ↣ₐ [[ ststk_next ]] -∗
    cstack_full (map fst stk) -∗
    cstack_full_spec (map snd stk) -∗
    cstack_interp (map fst stk) a_tstk -∗
    cstack_interp_spec (map snd stk) a_tstk -∗
    □ (∀ W', ⌜related_sts_priv_world W W'⌝ →
             ▷ execute_entry_point
               (WCap RX Global bpcc epcc a_pcc, WCap RX Global bpcc epcc a_pcc)
               (WCap RW Global bcgp ecgp bcgp, WCap RW Global bcgp ecgp bcgp)
               nargs W' C) -∗
    ⤇ Seq (Instr Executable) -∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 57)%a -∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 57)%a -∗
    csp ↦ᵣ WCap RWL Local a_stk4 e_stk a_stk4 -∗
    csp ↣ᵣ WCap RWL Local a_stk4 e_stk a_stk4 -∗
    ct2 ↦ᵣ WInt (Z.of_nat nargs + 1) -∗
    ct2 ↣ᵣ WInt (Z.of_nat nargs + 1) -∗
    ctp ↦ᵣ wctp -∗ ctp ↣ᵣ swctp -∗
    cs0 ↦ᵣ wcs0 -∗ cs0 ↣ᵣ swcs0 -∗
    cs1 ↦ᵣ wcs1 -∗ cs1 ↣ᵣ swcs1 -∗
    ct1 ↦ᵣ wct1 -∗ ct1 ↣ᵣ swct1 -∗
    cra ↦ᵣ WCap RX Global bpcc epcc a_pcc -∗
    cra ↣ᵣ WCap RX Global bpcc epcc a_pcc -∗
    cgp ↦ᵣ WCap RW Global bcgp ecgp bcgp -∗
    cgp ↣ᵣ WCap RW Global bcgp ecgp bcgp -∗
    ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
        rarg ↦ᵣ warg
        ∗ rarg ↣ᵣ sarg
        ∗ if decide (rarg ∈ dom_arg_rmap nargs)
          then interp W C (warg, sarg)
          else True ) -∗
    ([∗ map] r↦w ∈ rmap, r ↦ᵣ w) -∗
    ([∗ map] r↦w ∈ smap, r ↣ᵣ w) -∗
    a_stk ↦ₐ wcs0_caller.1 -∗
    (a_stk ^+ 1)%a ↦ₐ wcs1_caller.1 -∗
    (a_stk ^+ 2)%a ↦ₐ wcra_caller.1 -∗
    (a_stk ^+ 3)%a ↦ₐ wcgp_caller.1 -∗
    a_stk ↣ₐ wcs0_caller.2 -∗
    (a_stk ^+ 1)%a ↣ₐ wcs1_caller.2 -∗
    (a_stk ^+ 2)%a ↣ₐ wcra_caller.2 -∗
    (a_stk ^+ 3)%a ↣ₐ wcgp_caller.2 -∗
    [[ a_stk4 , e_stk ]] ↦ₐ [[ region_addrs_zeroes a_stk4 e_stk ]] -∗
    [[ a_stk4 , e_stk ]] ↣ₐ [[ region_addrs_zeroes a_stk4 e_stk ]] -∗
    world_interp W C -∗
    StackRevokedResources W C callee_stk_region -∗
    cstack_frag (map fst stk) -∗
    cstack_frag_spec (map snd stk) -∗
    interp_continuation stk Ws Cs -∗
    £ 1 -∗
    ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word),
        ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
        ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
        ∗ na_own cerise_nais ⊤
        ∗ ⤇ Seq (Instr Executable)
        ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4, WCap RWL Local a_stk4 e_stk a_stk4)
        ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
        ∗ world_interp_open W2 C callee_stk_region
        ∗ StackOpenWorldResources interp W2 C callee_stk_region stk_mem_h stk_mem_h_spec
        ∗ cstack_frag (map fst stk)
        ∗ cstack_frag_spec (map snd stk)
        ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
        ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
        ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
        ∗ cgp ↦ᵣ wcgp_caller.1
        ∗ cgp ↣ᵣ wcgp_caller.2
        ∗ cra ↦ᵣ wcra_caller.1
        ∗ cra ↣ᵣ wcra_caller.2
        ∗ cs0 ↦ᵣ wcs0_caller.1
        ∗ cs0 ↣ᵣ wcs0_caller.2
        ∗ cs1 ↦ᵣ wcs1_caller.1
        ∗ cs1 ↣ᵣ wcs1_caller.2
        ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
        ∗ (∃ warg0, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)
        ∗ (∃ warg1, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)
        ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
        ∗ [[ a_stk , a_stk4 ]] ↦ₐ [[ stk_mem_l ]]
        ∗ [[ a_stk , a_stk4 ]] ↣ₐ [[ stk_mem_l_spec ]]
        ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem_h ]]
        ∗ [[ a_stk4 , e_stk ]] ↣ₐ [[ stk_mem_h_spec ]]
        ∗ interp_continuation stk Ws Cs
        ∗ £ 2
        -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}
    ) -∗
    WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    intros callee_stk_region.
    iIntros (Hb_astk Ha_stk4 Ha_stk3 Hbounds_tstk_b Hlen_cstk Hastk Hf4 Hf3_bound Hnargs
             Hdom_rmap Hdom_smap Hargs_rmap Hargs_smap Hrevoked)
      "#Hinv_switcher #Hspec #Hp_ot_switcher Hclose_switcher_inv Hna
       Hcode Hscode Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk
       Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp #Hexec Hj HPC HsPC Hcsp Hscsp
       Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0 Hcs1 Hscs1 Hct1 Hsct1 Hcra Hscra Hcgp Hscgp
       Hargs Hrmap Hsmap Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3
       Hstk Hsstk Hworld_interp #Hstk_val Hcstk Hcstk_spec Hcont Hlc Hpost".
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

    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block_lockstep 9 "Hscode" "Hcode" as a_clear Ha_clear "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    iApply (clear_registers_pre_call_skip_spec _ _ _ _ _ arg_rmap arg_smap (nargs+1)
             with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode]"); try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame "Hct2 Hsct2 Hargs".
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

    iInsertList "Hrmap" [ct1;ctp;ct2;cs1;cs0].
    iInsertListSpec "Hsmap" [ct1;ctp;ct2;cs1;cs0].

    iApply (clear_registers_pre_call_spec with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hrmap $Hsmap]")
    ; try solve_pure.
    { rewrite !dom_insert_L Hdom_rmap. pose proof all_registers_s_correct as Hall.
      rewrite /dom_arg_rmap /=. set_solver. }
    { rewrite !dom_insert_L Hdom_smap. pose proof all_registers_s_correct as Hall.
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

    set (frm1 :=
           {| wret := wcra_caller.1;
              wcgp := wcgp_caller.1;
              wcs0 := wcs0_caller.1;
              wcs1 := wcs1_caller.1;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).
    set (frm2 :=
           {| wret := wcra_caller.2;
              wcgp := wcgp_caller.2;
              wcs0 := wcs0_caller.2;
              wcs1 := wcs1_caller.2;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).
    set (W' := std_update_multiple W callee_stk_region Temporary).

    (* Reinstate the cleared stack frame of the callee in the world *)
    iMod (world_interp_reinstate_stack with "Hworld_interp Hstk_val Hstk Hsstk") as "Hworld_interp".
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }
    { apply Forall_replicate_eq. }
    { done. }
    iAssert (interp W' C (WCap RWL Local a_stk4 e_stk a_stk, WCap RWL Local a_stk4 e_stk a_stk))
      as "#Hstk4v".
    { iApply (StackRevokedResources_interp with "Hstk_val"). }

    iSpecialize ("Hexec" $! W' with "[]").
    { iPureIntro.
      apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp. auto. }

    (* Jalr cra cra *)
    iInstr_spec "Hscode".
    (* Jalr cra cra *)
    iInstr "Hcode" with "Hlc".
    iSpecialize ("Hexec" $! ((frm1, frm2) :: stk) (W' :: Ws) (C :: Cs)).
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    rewrite /load_word. iSimpl in "Hcgp". iSimpl in "Hscgp".

    iMod (cstack_update _ _ (frm1 :: map fst stk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod (cstack_update_spec _ _ (frm2 :: map snd stk) with "Hcstk_full_spec Hcstk_spec")
      as "[Hcstk_full_spec Hcstk_spec]".
    iMod ("Hclose_switcher_inv"
           with "[$Hna Hmtdc Hsmtdc Hcode Hscode Hb_switcher Hsb_switcher Htstk Hststk Hf3 Hsf3
                  Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp
                  Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3]") as "Hna".
    { iNext.
      iSplitL "Hmtdc Hcode Hb_switcher Htstk Hf3 Hcstk_full Hstk_interp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3".
      - iExists f3, _, _.
        rewrite (finz_incr_eq Hf4).
        iFrame "Hmtdc Hcode Hb_switcher Htstk Hcstk_full". iFrame "#".
        cbn [cstack_interp].
        replace (f3 ^+ -1)%a with a_tstk by solve_addr.
        rewrite /cframe_interp /cframe_stk_own /=.
        replace (a_stk ^+ 4)%a with a_stk4 by solve_addr.
        iFrame.
        rewrite ?length_map in Hlen_cstk |- *.
        iPureIntro. pose proof ot_switcher_size. repeat split; try done; try solve_addr; eauto.
      - iExists f3, _, _.
        rewrite (finz_incr_eq Hf4).
        iFrame "Hsmtdc Hscode Hsb_switcher Hststk Hcstk_full_spec".
        cbn [cstack_interp_spec].
        replace (f3 ^+ -1)%a with a_tstk by solve_addr.
        rewrite /cframe_interp_spec /cframe_stk_own_spec /=.
        replace (a_stk ^+ 4)%a with a_stk4 by solve_addr.
        iFrame.
        rewrite ?length_map in Hlen_cstk |- *.
        iPureIntro. pose proof ot_switcher_size. repeat split; try done; try solve_addr; eauto.
    }

    iApply ("Hexec" $! _ _ a_stk e_stk).
    iSplitR; first iFrame "#".
    iSplitL "Hcont Hpost Hlc".
    { iFrame "Hcont". simpl.
      iSplit; first (iPureIntro; done).
      replace (a_stk ^+ 4)%a with a_stk4 by solve_addr.
      iSplit; first iFrame "Hstk4v".
      iIntros (W2 HW2 wca0 wca1 regs stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec)
        "(_ & HPC & HsPC & Hcra & Hscra & Hcsp & Hscsp & Hcgp & Hscgp & Hcs0 & Hscs0 & Hcs1 & Hscs1
          & Hca0 & Hsca0 & #Hv0 & Hca1 & Hsca1 & #Hv1 & %Hdom_regs & Hregs
          & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h & Hworld_interp & Hres & Hcont' & Hcstk & Hcstk_spec
          & Hj & Hna)".
      iApply ("Hpost" $! W2 regs).
      iFrame "∗#%".
      iSplit.
      { iApply interp_monotone; first done.
        iApply (interp_lea with "Hstk4v"); done. }
      iSplit.
      { iPureIntro; repeat split; solve_addr. }
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp;[apply HW2|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto.
    }
    iSplitR.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world.
    }
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
    - iPureIntro. clear. simplify_map_eq. done.
    - iPureIntro. clear. simplify_map_eq. done.
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
    - iPureIntro. clear -Ha_stk4. simplify_map_eq.
      replace a_stk4 with (a_stk^+4)%a by solve_addr.
      done.
    - iPureIntro. clear -Ha_stk4. simplify_map_eq.
      replace a_stk4 with (a_stk^+4)%a by solve_addr.
      done.
    - replace (a_stk ^+ 4)%a with a_stk4 by solve_addr.
      iApply (interp_lea with "Hstk4v"); done.
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
      destruct Hv1 as [Hv1|Hv1]; cycle 1.
      { apply elem_of_dom_2 in Hv1; rewrite Hrmap'' in Hv1.
        exfalso; clear -Hr Hv1. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv1|apply IHnargs; set_solver+Hr]. }
      destruct Hv2 as [Hv2|Hv2]; cycle 1.
      { apply elem_of_dom_2 in Hv2; rewrite Hsmap'' in Hv2.
        exfalso; clear -Hr Hv2. do 8 (destruct nargs; first set_solver).
        induction nargs; [set_solver+Hr Hv2|apply IHnargs; set_solver+Hr]. }
      iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
      destruct (decide (r ∈ _)) as [|Hcontra].
      + iApply (interp_monotone with "[] Hv").
        iPureIntro; apply related_sts_pub_update_multiple_temp; auto.
      + set_solver+Hcontra Hr.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Hisarg_rmap' Hrmap'' /=; set_solver+.
      }
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
      destruct Hv as [Hv|Hv].
      + assert (is_Some (arg_rmap' !! r)) as [v1 Hv1].
        { apply elem_of_dom; rewrite Hisarg_rmap' -Hisarg_smap'. by apply elem_of_dom_2 in Hv. }
        iDestruct (big_sepM2_lookup with "Hval") as "Hv"; eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last (iDestruct "Hv" as "[_ $]").
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hsnil") as "%";eauto; simplify_eq.
  Qed.

End Switcher.
