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
From griotte Require Import switcher_spec_call_jump_binary.
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

  (** The switcher-call routine of a trusted caller, after pushing the
      caller's stack pointer on both trusted stacks: the switcher chops the
      stack, clears the callee's stack frame, unseals the entry point (the
      same in both runs), loads the callee's capabilities, clears the
      registers that are not arguments, and jumps to the callee.
      The pair of frames pushed on the call stacks records the callee-saved
      registers of each run, and the same stack bounds. *)
  Lemma switcher_cc_after_push
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk a_stk4 : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    (a_tstk f3 f4 : Addr) (tstk_next ststk_next : list Word)
    (wct2 swct2 wctp swctp wcs0 swcs0 wcs1 swcs1 wcra swcra wcgp swcgp : Word)
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
    ⤇ Seq (Instr Executable) -∗
    PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 26)%a -∗
    PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher (a_switcher_call ^+ 26)%a -∗
    csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk4 -∗
    csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk4 -∗
    ct2 ↦ᵣ wct2 -∗ ct2 ↣ᵣ swct2 -∗
    ctp ↦ᵣ wctp -∗ ctp ↣ᵣ swctp -∗
    cs0 ↦ᵣ wcs0 -∗ cs0 ↣ᵣ swcs0 -∗
    cs1 ↦ᵣ wcs1 -∗ cs1 ↣ᵣ swcs1 -∗
    cra ↦ᵣ wcra -∗ cra ↣ᵣ swcra -∗
    cgp ↦ᵣ wcgp -∗ cgp ↣ᵣ swcgp -∗
    ct1 ↦ᵣ wct1_caller -∗ ct1 ↣ᵣ wct1_caller -∗
    (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True) -∗
    (if is_entry_point_known
     then ∃ nargs, wct1_caller ↦□ₑ nargs
                   ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                         rarg ↦ᵣ warg
                         ∗ rarg ↣ᵣ sarg
                         ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                           then interp W C (warg, sarg)
                           else True )
     else ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
              rarg ↦ᵣ warg
              ∗ rarg ↣ᵣ sarg
              ∗ interp W C (warg, sarg) )
    ) -∗
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
    [[ a_stk4 , e_stk ]] ↦ₐ [[ stk_mem ]] -∗
    [[ a_stk4 , e_stk ]] ↣ₐ [[ stk_mem_spec ]] -∗
    world_interp W C -∗
    StackRevokedResources W C callee_stk_region -∗
    cstack_frag (map fst stk) -∗
    cstack_frag_spec (map snd stk) -∗
    interp_continuation stk Ws Cs -∗
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
    iIntros (Hb_astk Ha_stk4 Ha_stk3 Hbounds_tstk_b Hlen_cstk Hastk Hf4 Hf3_bound
             Hdom_rmap Hdom_smap Hargs_rmap Hargs_smap Hrevoked)
      "#Hinv_switcher #Hspec #Hp_ot_switcher Hclose_switcher_inv Hna
       Hcode Hscode Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk
       Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp Hj HPC HsPC Hcsp Hscsp
       Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0 Hcs1 Hscs1 Hcra Hscra Hcgp Hscgp Hct1 Hsct1
       #Htarget_v Hargs Hrmap Hsmap Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3
       Hstk Hsstk Hworld_interp #Hstk_val Hcstk Hcstk_spec Hcont Hpost".
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

    (* GetE cs0 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetA cs1 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Subseg csp cs1 cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /isWithin; solve_addr.

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block_lockstep 5 "Hscode" "Hcode" as a_clear_stk1 Ha_clear_stk1
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_stack_chop.
    iApply (clear_stack_spec
             with "[- $Hspec $Hj $HPC $HsPC $Hcode $Hscode $Hcsp $Hscsp $Hcs0 $Hscs0 $Hcs1 $Hscs1 $Hstk $Hsstk]")
    ; try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    iIntros "!> (Hj & HPC & HsPC & Hcsp & Hscsp & Hcs0 & Hcs1 & Hscs0 & Hscs1 & Hcode & Hscode & Hstk & Hsstk)".
    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block_lockstep 6 "Hscode" "Hcode" as a_LoadCapPCC Ha_LoadCapPCC
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_clear_stk1.

    (* GetB cs1 PC *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetA cs0 PC *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Sub cs1 cs1 cs0 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov cs0 PC *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea cs0 cs1 *)
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    iMod (step_lea_success_reg with "[$Hspec $Hj $HsPC $Hsi $Hscs0 $Hscs1]")
      as "(Hj & HsPC & Hsi & Hscs1 & Hscs0)";
      [solve_ndisj|solve_pure|solve_pure|solve_pure| |solve_pure|solve_pure|].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iSpecSeq.
    iSpecialize ("Hscode" with "[$]").
    (* Lea cs0 cs1 *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]"); auto; [solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* Lea cs0 (-2)%Z *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:= b_switcher); solve_addr.

    (* Load cs0 cs0 *)
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

    (* UnSeal ct1 cs0 ct1 *)
    rewrite /load_word. iSimpl in "Hcs0". iSimpl in "Hscs0".
    destruct (is_sealed_with_o wct1_caller ot_switcher) eqn:Hwct1_caller; cycle 1.
    { (* wct1_caller is not sealed with ot_switcher, the implementation fails *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_unseal_nomatch_r2 with "[$HPC $Hi $Hct1 $Hcs0]") ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    iInstr_spec_lookup "Hscode" as "Hsi" "Hscode".
    wp_instr.
    iApply (wp_unseal_unknown_sealed
             with "[$Hspec $Hj $HPC $HsPC $Hi $Hsi $Hcs0 $Hscs0 $Hct1 $Hsct1 $Htarget_v]")
    ; try solve_pure; try solve_ndisj.
    { pose proof ot_switcher_size. solve_finz. }
    iIntros "!>" (ret) "[-> | (%wsb & %wsb' & -> & Hj & HPC & HsPC & Hi & Hsi & Hcs0 & Hscs0
      & Hct1 & Hsct1 & %Hwsb & %Hwsb')]".
    { wp_pure. wp_end. iIntros "%Hcontr";done. }
    rewrite Hwsb in Hwsb'. inversion Hwsb'. subst wsb' wct1_caller.

    (* get the seal inv and compare with wsb *)
    iDestruct (interp_sealed_inv with "Htarget_v") as "[_ Hsb]".
    iDestruct "Hsb" as (P HpersP) "(HmonoP & HPseal & %Hloc & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,(WSealable wsb, WSealable wsb))).

    wp_pure.
    iSpecSeq.
    iSpecialize ("Hcode" with "[$]").
    iSpecialize ("Hscode" with "[$]").
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (??????????? Heq Heq' Htbl_bounds Htbl_b1 Htbl_b1a Hnargs)
                        "(Htbl1 & Htbl2 & Htbl3 & #Hentry & Hexec)".
    simpl fst in Heq, Heq'. simpl snd in Heq'.
    inversion Heq.

    (* Load cs0 ct1 *)
    wp_instr.
    iInv "Htbl3" as ">[Ha_tbl Hsa_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* LAnd ct2 cs0 7 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* LShiftR cs0 cs0 3 *)
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

    (* GetB cgp ct1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetA cs1 ct1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Sub cs1 cgp cs1 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lea ct1 cs1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=b_tbl); solve_addr+Htbl_bounds.

    (* Load cra ct1 *)
    wp_instr.
    iInv "Htbl1" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* Lea ct1 1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: instantiate (1:=(b_tbl ^+ 1)%a); solve_addr+Htbl_b1.

    (* Load cgp ct1 *)
    wp_instr.
    iInv "Htbl2" as ">[Hb_tbl Hsb_tbl]" "Hcls_tbl".
    iInstr_lockstep "Hscode" "Hcode".
    1,2: split;auto; solve_addr+Htbl_bounds Htbl_b1 Htbl_b1a.
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* Lea cra cs0 *)
    destruct (bpcc + encode_entry_point nargs off ≫ 3)%a as [a_pcc|] eqn:Hentry;cycle 1.
    { iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_Lea_fail_none_reg with "[$HPC $Hi $Hcs0 $Hcra]")
      ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    iInstr_lockstep "Hscode" "Hcode".

    (* Add ct2 ct2 1 *)
    iInstr_spec "Hscode".
    (* Add ct2 ct2 1 *)
    iInstr "Hcode" with "Hlc".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* The callee's entry point and number of arguments *)
    rewrite encode_entry_point_eq_nargs;last lia.
    rewrite encode_entry_point_eq_off in Hentry.
    replace (bpcc ^+ off)%a with a_pcc by solve_addr.
    iAssert ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
                rarg ↦ᵣ warg
                ∗ rarg ↣ᵣ sarg
                ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                  then interp W C (warg, sarg)
                  else True )%I with "[Hargs]" as "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(%nargs0 & Hentry' & Hargs)".
        iEval (cbn) in "Hentry".
        iDestruct (entry_agree _ nargs nargs0 with "Hentry Hentry'") as "<-".
        iFrame.
      + iApply (big_sepM2_impl with "Hargs").
        iIntros "!> %k %w1 %w2 _ _ ($ & $ & Hinterp)".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }

    changePCto (a_switcher_call ^+ 57)%a.
    iApply (switcher_cc_jump_callee
             with "Hinv_switcher Hspec Hp_ot_switcher Hclose_switcher_inv Hna Hcode Hscode
                   Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk
                   Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp [] Hj HPC HsPC Hcsp Hscsp
                   Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0 Hcs1 Hscs1 Hct1 Hsct1 Hcra Hscra Hcgp Hscgp
                   Hargs Hrmap Hsmap Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3
                   Hstk Hsstk Hworld_interp Hstk_val Hcstk Hcstk_spec Hcont Hlc Hpost")
    ; try eassumption.
    { lia. }
    iModIntro. iIntros (W' HW').
    iApply "Hexec". iPureIntro. exact HW'.
  Qed.

End Switcher.
