From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From stdpp Require Import base.
From griotte Require Import sts_multiple_updates.
From griotte Require Import logrel_binary fundamental_binary memory_region memory_region_binary.
From griotte Require Import rules proofmode_binary monotone_binary.
From griotte Require Import region_invariants_revocation_binary.
From griotte Require Export switcher switcher_preamble_binary.
From griotte Require Import map_simpl register_tactics_binary.
From griotte Require Export world_ghost_theory_binary world_interp_stack_binary switcher_helpers_binary.
From griotte Require Import switcher_spec_call_exhausted_binary switcher_spec_call_tail_binary.

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

  (** Specification of the switcher-call routine, for a trusted caller
      calling the same entry point in both runs (lockstep).

      The caller-saved registers [cgp], [cra], [cs0] and [cs1] may contain
      different words in the two runs: they are pairs of words. The stack
      pointer is the same in both runs, but the contents of the stack frame
      may differ. The entry point [wct1_caller] is the same in both runs. The
      argument registers are related when they are passed to the callee.

      The switcher pushes on both call stacks a pair of frames with the same
      stack bounds, each recording the callee-saved registers of its own run.
      As both trusted stacks have the same depth, the call either goes
      through in both runs, or fails in both runs because the trusted stack
      is exhausted. *)
  Lemma switcher_cc_specification_gen
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be related *)
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
      )
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec : list Word),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4, WCap RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C callee_stk_region
              ∗ StackOpenWorldResources interp W2 C callee_stk_region stk_mem_h stk_mem_h_spec
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
              ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
              (* cgp is restored, cra points to the next  *)
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
          )
          ∨
            ( (* POST-CONDITION --- the call didn't go through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ na_own cerise_nais ⊤
              ∗ ⤇ Seq (Instr Executable)
              (* Registers are preserved *)
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
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca0 ↣ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ca1 ↣ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ r ↣ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , a_stk4 ]] ↦ₐ [[ [wcs0_caller.1; wcs1_caller.1; wcra_caller.1; wcgp_caller.1] ]]
              ∗ [[ a_stk , a_stk4 ]] ↣ₐ [[ [wcs0_caller.2; wcs1_caller.2; wcra_caller.2; wcgp_caller.2] ]]
              ∗ [[ a_stk4 , e_stk ]] ↦ₐ [[ drop 4 stk_mem ]]
              ∗ [[ a_stk4 , e_stk ]] ↣ₐ [[ drop 4 stk_mem_spec ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag (map fst stk)
              ∗ cstack_frag_spec (map snd stk)
              ∗ interp_continuation stk Ws Cs
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}
  )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hargs & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & #Hstk_val & %Hstk_revoked & Hcstk & Hcstk_spec & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.

    assert (is_Some (rmap !! ct2)) as [??].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    assert (is_Some (rmap !! ctp)) as [??].
    { apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    iExtractList "Hregs" [ct2;ctp] as ["Hct2";"Hctp"].
    assert (is_Some (smap !! ct2)) as [??].
    { apply elem_of_dom. rewrite Hsdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    assert (is_Some (smap !! ctp)) as [??].
    { apply elem_of_dom. rewrite Hsdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|rewrite /dom_arg_rmap /=; set_solver]. }
    iExtractList "Hsregs" [ct2;ctp] as ["Hsct2";"Hsctp"].

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
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
    iHide "Hswitcher" as hinv_switcher.

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

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0_lockstep "Hscode" "Hcode" as "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* GetP ct2 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov ctp (encodePerm RWL) *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Sub ct2 ct2 ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    replace ( match MP with
                 | {| encodePerm := encodePerm |} => encodePerm
                 end  ) with encodePerm by done.
    replace ( (if decide (ctp = cnull) then 0 else encodePerm RWL)%Z )
      with ( encodePerm RWL ) by (destruct (decide _); done).
    replace (encodePerm RWL - encodePerm RWL)%Z with 0%Z by lia.
    (* Jnz 2 ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block_lockstep 1 "Hscode" "Hcode" as a_csp_check_loc Ha_csp_check_loc
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.

    (* GetL ct2 csp *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Mov ctp (encodeLoc Local) *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Sub ct2 ct2 ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    replace ( match MP with
                 | {| encodeLoc := encodeLoc |} => encodeLoc
                 end  ) with encodeLoc by done.
    replace ( (if decide (ctp = cnull) then 0 else encodeLoc Local )%Z )
      with ( encodeLoc Local ) by (destruct (decide _); done).
    replace (encodeLoc Local - encodeLoc Local)%Z with 0%Z by lia.
    (* Jnz 2 ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block_lockstep 2 "Hscode" "Hcode" as a_entry_first_spill Ha_entry_first_spill
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_csp_check_loc.

    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    iDestruct (big_sepL2_length with "Hsstk") as %Hsstklen.
    rewrite finz_seq_between_length in Hstklen.
    rewrite finz_seq_between_length in Hsstklen.
    destruct (decide (b_stk <= a_stk < e_stk)%a) as [Hastk_inbounds|Hastk_inbounds]; cycle 1.
    { (* Store csp cs0 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk_inbounds.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw0 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hastk_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk Hsstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }

    (* Store csp cs0 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 1)%a < e_stk)%a) as [Hastk1_inbounds|Hastk1_inbounds]; cycle 1.
    { (* Store csp cs1 *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs1 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk1_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk1_inbounds.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw1 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hastk1 Hastk1_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk1 Hstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk1 Hsstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }

    (* Store csp cs1 *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 2)%a < e_stk)%a) as [Hastk2_inbounds|Hastk2_inbounds]; cycle 1.
    { (* Store csp cra *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcra $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk2_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk2_inbounds.
    destruct stk_mem as [|w2 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw2 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk2 + 1)%a) as [a_stk3 Hastk3];[solve_addr+Hastk1 Hastk2 Hastk2_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk2 Hstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk2 Hsstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }

    (* Store csp cra *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk)%a) as [Hastk3_inbounds|Hastk3_inbounds]; cycle 1.
    { (* Store csp cgp *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk3_inbounds.
    rewrite finz_dist_S in Hsstklen; last solve_addr+Hastk3_inbounds.
    destruct stk_mem as [|w3 stk_mem]; simplify_eq.
    destruct stk_mem_spec as [|sw3 stk_mem_spec]; simplify_eq.
    assert (is_Some (a_stk3 + 1)%a) as [a_stk4 Hastk4];[solve_addr+Hastk1 Hastk2 Hastk3 Hastk3_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk3 Hstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    iDestruct (spec_region_pointsto_cons with "Hsstk") as "[Hsa_stk3 Hsstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by solve_addr.
    assert ((a_stk ^+4)%a = a_stk4) as -> by solve_addr.

    (* Store csp cgp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* Lea csp 1 *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".
    replace a_stk1 with (a_stk ^+ 1)%a by solve_addr.
    replace a_stk2 with (a_stk ^+ 2)%a by solve_addr.
    replace a_stk3 with (a_stk ^+ 3)%a by solve_addr.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block_lockstep 3 "Hscode" "Hcode" as a_tstack_push Ha_tstack_push
      "Hscode" "Hscls" "Hcode" "Hcls".
    iHide "Hcls" as hcont. iHide "Hscls" as hscont.
    clear dependent Ha_entry_first_spill.

    (* ReadSR ct2 mtdc *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetA cs0 ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Add cs0 cs0 1%Z *)
    iInstr_lockstep "Hscode" "Hcode".

    (* GetE ctp ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    (* Lt ctp cs0 ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; iEval (cbn) in "Hsctp"
    ; cycle 1.
    { (* The trusted stack is exhausted *)
      (* Jnz 2%Z ctp *)
      iInstr_lockstep "Hscode" "Hcode".
      (* Jmp Lswitch_trusted_stack_exhausted_z *)
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

      (* Gather the registers that are not restored *)
      iAssert (([∗ map] r↦w ∈ arg_rmap, r ↦ᵣ w) ∗ ([∗ map] r↦w ∈ arg_smap, r ↣ᵣ w))%I
        with "[Hargs]" as "[Hargs Hsargs]".
      { iAssert ([∗ map] r↦w;sw ∈ arg_rmap;arg_smap, r ↦ᵣ w ∗ r ↣ᵣ sw)%I with "[Hargs]" as "Hargs".
        { destruct is_entry_point_known.
          + iDestruct "Hargs" as "(% & _ & Hargs)".
            iApply (big_sepM2_impl with "Hargs").
            iIntros "!> %rk %rv1 %rv2 _ _ ($ & $ & _)".
          + iApply (big_sepM2_impl with "Hargs").
            iIntros "!> %rk %rv1 %rv2 _ _ ($ & $ & _)".
        }
        iDestruct (big_sepM2_sepM with "Hargs") as "$".
        intros k. rewrite -!elem_of_dom Hrdom Hsrdom. done.
      }
      assert (is_Some (arg_rmap !! ca0)) as [??].
      { apply elem_of_dom. rewrite Hrdom /dom_arg_rmap /=. set_solver+. }
      assert (is_Some (arg_rmap !! ca1)) as [??].
      { apply elem_of_dom. rewrite Hrdom /dom_arg_rmap /=. set_solver+. }
      iExtractList "Hargs" [ca0;ca1] as ["Hca0";"Hca1"].
      assert (is_Some (arg_smap !! ca0)) as [??].
      { apply elem_of_dom. rewrite Hsrdom /dom_arg_rmap /=. set_solver+. }
      assert (is_Some (arg_smap !! ca1)) as [??].
      { apply elem_of_dom. rewrite Hsrdom /dom_arg_rmap /=. set_solver+. }
      iExtractList "Hsargs" [ca0;ca1] as ["Hsca0";"Hsca1"].
      iInsertList "Hregs" [ct1;ctp;ct2].
      iInsertListSpec "Hsregs" [ct1;ctp;ct2].
      iDestruct (big_sepM_union with "[$Hregs $Hargs]") as "Hregs".
      { apply map_disjoint_dom. rewrite !dom_insert_L !dom_delete_L Hdom Hrdom /dom_arg_rmap /=. set_solver. }
      iDestruct (big_sepM_union with "[$Hsregs $Hsargs]") as "Hsregs".
      { apply map_disjoint_dom. rewrite !dom_insert_L !dom_delete_L Hsdom Hsrdom /dom_arg_rmap /=. set_solver. }

      iApply (switcher_cc_tstk_exhausted
               with "Hswitcher Hspec Hna Hj HPC HsPC Hcsp Hscsp Hcgp Hscgp Hcra Hscra Hcs1 Hscs1
                     Hcs0 Hscs0 Hca0 Hsca0 Hca1 Hsca1 Hregs Hsregs
                     Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3
                     [Hpost Hworld_interp Hcstk Hcstk_spec Hcont Hstk Hsstk]")
      ; try eassumption.
      { solve_addr. }
      { solve_addr. }
      { rewrite dom_union_L !dom_insert_L !dom_delete_L Hdom Hrdom /dom_arg_rmap /=.
        pose proof all_registers_s_correct as Hall. set_solver. }
      { rewrite dom_union_L !dom_insert_L !dom_delete_L Hsdom Hsrdom /dom_arg_rmap /=.
        pose proof all_registers_s_correct as Hall. set_solver. }
      iIntros (rmap') "(%Hdom' & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0
        & Hcs1 & Hscs1 & Hcsp & Hscsp & Hca0 & Hsca0 & Hca1 & Hsca1 & Hrmap'
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hsa_stk & Hsa_stk1 & Hsa_stk2 & Hsa_stk3 & Hlc)".
      iApply ("Hpost" $! W rmap' [] [] [] []).
      iRight. cbn [drop]. iFrame "∗#%".
      iSplit.
      { iPureIntro. repeat split; solve_addr. }
      iSplitL "Ha_stk Ha_stk1 Ha_stk2 Ha_stk3".
      { iApply (region_pointsto_cons _ (a_stk ^+ 1)%a); [solve_addr|solve_addr|iFrame "Ha_stk"].
        iApply (region_pointsto_cons _ (a_stk ^+ 2)%a); [solve_addr|solve_addr|iFrame "Ha_stk1"].
        iApply (region_pointsto_cons _ (a_stk ^+ 3)%a); [solve_addr|solve_addr|iFrame "Ha_stk2"].
        iApply (region_pointsto_cons _ a_stk4); [solve_addr|solve_addr|iFrame "Ha_stk3"].
        rewrite /region_pointsto (finz_seq_between_empty a_stk4 a_stk4); [done|solve_addr].
      }
      iApply (spec_region_pointsto_cons _ (a_stk ^+ 1)%a); [solve_addr|solve_addr|iFrame "Hsa_stk"].
      iApply (spec_region_pointsto_cons _ (a_stk ^+ 2)%a); [solve_addr|solve_addr|iFrame "Hsa_stk1"].
      iApply (spec_region_pointsto_cons _ (a_stk ^+ 3)%a); [solve_addr|solve_addr|iFrame "Hsa_stk2"].
      iApply (spec_region_pointsto_cons _ a_stk4); [solve_addr|solve_addr|iFrame "Hsa_stk3"].
      rewrite /spec_region_pointsto (finz_seq_between_empty a_stk4 a_stk4); [done|solve_addr].
    }
    (* Jnz 2%Z ctp *)
    iInstr_lockstep "Hscode" "Hcode".

    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Hastk'] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    (* Lea ct2 1 *)
    iInstr_lockstep "Hscode" "Hcode".

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
    (* Store ct2 csp *)
    iInstr_lockstep "Hscode" "Hcode".
    1,2: rewrite /withinBounds; solve_addr.

    (* WriteSR mtdc ct2 *)
    iInstr_lockstep "Hscode" "Hcode".

    subst hcont hscont.
    unfocus_block_lockstep "Hscode" "Hscls" "Hcode" "Hcls" as "Hscode" "Hcode".

    (* The rest of the switcher-call routine *)
    changePCto (a_switcher_call ^+ 26)%a.
    iAssert (StackRevokedResources W C (finz.seq_between a_stk a_stk4 ++ finz.seq_between a_stk4 e_stk))
      as "Hstk_val_split".
    { rewrite -(finz_seq_between_split a_stk a_stk4 e_stk); [iFrame "Hstk_val"|solve_addr]. }
    iDestruct (StackRevokedResources_app with "Hstk_val_split") as "[_ #Hstk_val']".
    iApply (switcher_cc_after_push
             with "Hswitcher Hspec Hp_ot_switcher Hclose_switcher_inv Hna Hcode Hscode
                   Hmtdc Hsmtdc Hb_switcher Hsb_switcher Hf3 Hsf3 Htstk Hststk
                   Hcstk_full Hcstk_full_spec Hstk_interp Hsstk_interp Hj HPC HsPC Hcsp Hscsp
                   Hct2 Hsct2 Hctp Hsctp Hcs0 Hscs0 Hcs1 Hscs1 Hcra Hscra Hcgp Hscgp Hct1 Hsct1
                   Htarget_v Hargs Hregs Hsregs
                   Ha_stk Ha_stk1 Ha_stk2 Ha_stk3 Hsa_stk Hsa_stk1 Hsa_stk2 Hsa_stk3
                   Hstk Hsstk Hworld_interp Hstk_val' Hcstk Hcstk_spec Hcont [Hpost]")
    ; try eassumption.
    { solve_addr. }
    { solve_addr. }
    { apply Z.ltb_lt in Hsize_tstk. solve_addr+Hsize_tstk Hastk'. }
    { rewrite !dom_delete_L Hdom /dom_arg_rmap /=. set_solver. }
    { rewrite !dom_delete_L Hsdom /dom_arg_rmap /=. set_solver. }
    { rewrite /revoked_addresses in Hstk_revoked |- *.
      eapply revoked_addresses_weaken; [|exact Hstk_revoked].
      intros a Ha. rewrite !elem_of_finz_seq_between in Ha |- *. solve_addr. }
    iIntros (W2 rmap' stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec) "H".
    iApply "Hpost". iLeft. iExact "H".
  Qed.


  (** This specification unifies the two possible outcomes of the switcher
      call. It closes the world, and then revokes it. *)
  Lemma switcher_cc_specification_gen_revoked
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be related *)
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
      )
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
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
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hargs & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iApply (switcher_cc_specification_gen with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
    iIntros (W' rmap' stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec).
    iNext; iIntros "[H|H]".
    + clear stk_mem stk_mem_spec.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap & Hna & Hj & #Hinterp_W2_csp & %Hcsp_bounds
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hcstk_frag_spec & Hrel_stk_C
      & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
      & Hca0 & Hca1 & Hrmap & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h & HK & [Hlc Hlc'])".

      iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
      iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
      iDestruct ( big_sepL2_length with "Hsstk_l" ) as "%Hslen_stk_l".
      iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hworld_interp_C".

      iDestruct (close_world_interp_opening_resources
                  with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h $Hsstk_h]")
        as "Hworld_interp_C".
      { apply finz_seq_between_NoDup. }
      { set_solver+. }
      { by rewrite Hlen_stk_h. }
      rewrite -open_world_interp_empty.

      iMod (world_interp_revoked_by_separation_many with "[$Hworld_interp_C $Hstk_l]")
        as "(Hworld_interp_C & Hstk_l & %Hstk_l_revoked)".
      {
        apply Forall_forall; intros a Ha.
        eapply elem_of_mono_pub;eauto.
        rewrite elem_of_dom.
        rewrite std_sta_update_multiple_lookup_same_i; cycle 1.
        { intro Hcontra.
          apply elem_of_finz_seq_between in Ha, Hcontra.
          solve_addr.
        }
        assert ( a ∈ finz.seq_between a_stk e_stk).
        { rewrite elem_of_finz_seq_between.
          rewrite elem_of_finz_seq_between in Ha.
          solve_addr.
        }
        rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
        apply Hrevoked_stk in H.
        done.
      }

      iMod (world_interp_revoke_stack with "[$Hinterp_W2_csp $Hworld_interp_C]")
        as (l') "(%Hl_unk' & Hworld_interp_C & Hstack_revoked_W2 & Hrevoked_W2
                 & >(%stk_mem_h' & %stk_mem_h_spec' & Hstk_h & Hsstk_h)
                 & [Hrevoked_l' %Hrevoked_W2_l'])".
      iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
      { solve_addr+ Hcsp_bounds. }
      { by rewrite finz_seq_between_length in Hlen_stk_l. }
      iDestruct (spec_region_pointsto_split with "[$Hsstk_l $Hsstk_h]") as "Hsstk"; auto.
      { solve_addr+ Hcsp_bounds. }
      { by rewrite finz_seq_between_length in Hslen_stk_l. }
      iCombine "Hstack_revoked_W2 Hrevoked_W2" as "Hstack_revoked_W2".
      iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l']") as ">Hrevoked_l'".
      iDestruct (lc_fupd_elim_later with "[$] [$Hstack_revoked_W2]") as ">[Hstack_revoked_W2 %]".
      iApply "Hpost"; iFrame "∗%#".
      iSplitL "Hstack_revoked_W2"; cycle 1.
      { iPureIntro.
        rewrite (finz_seq_between_split a_stk (a_stk^+4)%a); last (split; solve_addr).
        rewrite !/revoked_addresses !Forall_forall in H,Hstk_l_revoked |- *.
        intros x Hx; cbn.
        apply elem_of_app in Hx; destruct Hx as [Hx|Hx].
        + apply revoke_lookup_Revoked; apply Hstk_l_revoked; done.
        + apply H; done.
      }
      iApply (StackRevokedResources_mono_priv with "Hstk_val").
      eapply related_sts_priv_pub_trans_world; eauto.
      apply related_sts_pub_priv_world.
      eapply related_sts_pub_update_multiple_temp.
      rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
      apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.

    + clear W' stk_mem_l stk_mem_h stk_mem_l_spec stk_mem_h_spec.
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna & Hj
           & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hcsp & Hscsp
           & Hca0 & Hsca0 & Hca1 & Hsca1
           & Hrmap & Hstk_l & Hsstk_l & Hstk_h & Hsstk_h
           & Hworld_interp_C & Hclose
           & Hcstk_frag & Hcstk_frag_spec & HK & [Hlc Hlc'])".
      pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].

      iMod ( world_interp_revoke _ _ l_unk with "[$Hworld_interp_C]") as
        "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l)"; auto.
      { split; auto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".

      assert (length [wcs0_caller.1; wcs1_caller.1; wcra_caller.1; wcgp_caller.1]
              = finz.dist a_stk (a_stk ^+ 4)%a) as Hlen4.
      { cbn.
        destruct Hcsp_bounds as (?&?&Ha4).
        pose proof (finz_incr_iff_dist a_stk (a_stk ^+ 4)%a 4) as [Hdist _].
        by apply Hdist in Ha4 as [? ?].
      }
      iDestruct (region_pointsto_split a_stk e_stk (a_stk ^+ 4)%a with "[$Hstk_l $Hstk_h]") as "Hstk".
      { solve_addr+ Hcsp_bounds. }
      { done. }
      iDestruct (spec_region_pointsto_split a_stk e_stk (a_stk ^+ 4)%a with "[$Hsstk_l $Hsstk_h]") as "Hsstk".
      { solve_addr+ Hcsp_bounds. }
      { done. }

      set (W2 := std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary).
      iAssert (∃ warg0 : Word * Word, ca0 ↦ᵣ warg0.1 ∗ ca0 ↣ᵣ warg0.2 ∗ interp W2 C warg0)%I
        with "[Hca0 Hsca0]" as "Hca0".
      { iExists (WInt ENOTENOUGHTRUSTEDSTACK, WInt ENOTENOUGHTRUSTEDSTACK). iFrame. iApply interp_int. }
      iAssert (∃ warg1 : Word * Word, ca1 ↦ᵣ warg1.1 ∗ ca1 ↣ᵣ warg1.2 ∗ interp W2 C warg1)%I
        with "[Hca1 Hsca1]" as "Hca1".
      { iExists (WInt 0, WInt 0). iFrame. iApply interp_int. }

      iSpecialize ("Hpost" $! W2 rmap' _ _ l_unk).
      subst W2.
      rewrite revoke_std_update_multiple_eq.
      2: { apply Forall_forall.
           intros a Ha.
           assert (a ∈ finz.seq_between a_stk e_stk) as Ha'.
           { rewrite elem_of_finz_seq_between.
             rewrite elem_of_finz_seq_between in Ha.
             solve_addr.
           }
           rewrite list_elem_of_lookup in Ha'; destruct Ha' as [? ?].
           rewrite /revoked_addresses Forall_forall in Hrevoked_stk.
           eapply Hrevoked_stk; eauto.
           by apply list_elem_of_lookup_2 in H.
      }
      iApply "Hpost"; iFrame "∗%#".
      iSplit.
      { iPureIntro.
        split.
        - apply NoDup_app; split; auto.
          split; last by apply finz_seq_between_NoDup.
          intros a Ha. apply Hlunk in Ha.
          intro Ha'.
          rewrite /revoked_addresses  Forall_forall in Hrevoked_stk.
           assert (a ∈ finz.seq_between a_stk e_stk) as Ha''.
           { rewrite elem_of_finz_seq_between.
             rewrite elem_of_finz_seq_between in Ha'.
             solve_addr.
           }
           apply Hrevoked_stk in Ha''.
           simplify_eq.
        - intros a; cbn.
          rewrite elem_of_app.
          split; intro Ha.
          + destruct ( decide ( a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk )); first (right; done).
            rewrite std_sta_update_multiple_lookup_same_i in Ha; auto.
            apply Hlunk in Ha.
            left; done.
          + destruct Ha as [Ha|Ha]; cycle 1.
            * rewrite std_sta_update_multiple_lookup_in_i; auto.
            * destruct ( decide ( a ∈ finz.seq_between (a_stk ^+ 4)%a e_stk )); first (rewrite std_sta_update_multiple_lookup_in_i; auto).
              rewrite std_sta_update_multiple_lookup_same_i; auto.
              apply Hlunk in Ha; done.
      }
      iSplitL "Hrevoked_l".
      {
        iApply (RevokedResources_mono_pub with "Hrevoked_l"); auto.
        eapply related_sts_pub_update_multiple_temp.
        rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
        apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.
      }
      iSplit.
      {
        iPureIntro.
        apply related_sts_pub_refl_world.
      }
      iSplit.
      {
        iPureIntro.
        intros k a Ha; cbn.
        apply std_sta_update_multiple_lookup_in_i.
        apply list_elem_of_lookup; eauto.
      }
      iSplitL "Hclose".
      { iApply (StackRevokedResources_mono_priv with "Hclose"); auto.
        apply related_sts_pub_priv_world.
        eapply related_sts_pub_update_multiple_temp.
        rewrite (finz_seq_between_split a_stk (a_stk^+4)%a) in Hrevoked_stk; last (split; solve_addr).
        apply revoked_addresses_app in Hrevoked_stk as [? ?]; auto.
      }
      iPureIntro.
      eapply Forall_impl; eauto.
      cbn; intros a Ha.
      apply revoke_lookup_Revoked; done.
  Qed.


  (** Specification of the switcher-call routine, for a trusted caller
      calling a known entry point of a compartment, the same in both runs.
      Only the arguments of the entry point need to be related. *)
  Lemma switcher_cc_specification
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ interp W C (wct1_caller, wct1_caller)
    ∗ wct1_caller ↦□ₑ nargs
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* Argument registers, need to be related *)
    ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
          rarg ↦ᵣ warg
          ∗ rarg ↣ᵣ sarg
          ∗ if decide (rarg ∈ dom_arg_rmap nargs)
            then interp W C (warg, sarg)
            else True )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
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
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 target callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & #Hentry & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hargs & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked
              Nswitcher W C wcgp_caller wcra_caller wcs0_caller wcs1_caller target
              b_stk e_stk a_stk stk_mem stk_mem_spec arg_rmap arg_smap rmap smap stk Ws Cs true
             with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
    subst target; cbn.
    destruct ( (ot_switcher =? ot_switcher)%Z ); eauto.
  Qed.


  (** Specification of the switcher-call routine, for a trusted caller
      calling an arbitrary entry point, the same in both runs. All the
      argument registers need to be related. *)
  Lemma switcher_cc_specification_alt
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word * Word)
    (wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem stk_mem_spec : list Word)
    (arg_rmap arg_smap rmap smap : Reg)
    (stk : cstack_pair) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    dom smap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->
    is_arg_rmap arg_smap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv_binary
    ∗ spec_ctx

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    ∗ ⤇ Seq (Instr Executable)
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ PC ↣ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller.1
    ∗ cgp ↣ᵣ wcgp_caller.2
    ∗ cra ↦ᵣ wcra_caller.1
    ∗ cra ↣ᵣ wcra_caller.2
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    ∗ csp ↣ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ ct1 ↣ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C (wct1_caller, wct1_caller) else True)
    ∗ cs0 ↦ᵣ wcs0_caller.1
    ∗ cs0 ↣ᵣ wcs0_caller.2
    ∗ cs1 ↦ᵣ wcs1_caller.1
    ∗ cs1 ↣ᵣ wcs1_caller.2
    (* Argument registers, need to be related *)
    ∗ ( [∗ map] rarg↦warg;sarg ∈ arg_rmap;arg_smap,
          rarg ↦ᵣ warg
          ∗ rarg ↣ᵣ sarg
          ∗ interp W C (warg, sarg) )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )
    ∗ ( [∗ map] r↦w ∈ smap, r ↣ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
    ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag (map fst stk)
    ∗ cstack_frag_spec (map snd stk)
    ∗ interp_continuation stk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem stk_mem_spec : list Word) l',
            (* We receive a public future world of the world pre switcher call *)
            ⌜ extract_temporaries_condition W2 (l' ++ finz.seq_between (a_stk ^+ 4)%a e_stk) ⌝
            ∗ RevokedResources W2 C l'
            ∗ ⌜ revoked_addresses (revoke W2) l' ⌝
            ∗ ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
            ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
            ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
            ∗ StackRevokedResources W2 C (finz.seq_between a_stk e_stk)
            ∗ ⌜ revoked_addresses (revoke W2) (finz.seq_between a_stk e_stk) ⌝
            ∗ na_own cerise_nais ⊤
            ∗ ⤇ Seq (Instr Executable)
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag (map fst stk)
            ∗ cstack_frag_spec (map snd stk)
            ∗ PC ↦ᵣ updatePcPerm wcra_caller.1
            ∗ PC ↣ᵣ updatePcPerm wcra_caller.2
            (* cgp is restored, cra points to the next  *)
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
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ [[ a_stk , e_stk ]] ↣ₐ [[ stk_mem_spec ]]
            ∗ interp_continuation stk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → ⤇ Seq (Instr Halted) ∗ na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hsdom Hrdom Hsrdom)
      "(#Hswitcher & #Hspec & Hna & Hj & HPC & HsPC & Hcgp & Hscgp & Hcra & Hscra & Hcsp & Hscsp
        & Hct1 & Hsct1 & #Htarget_v & Hcs0 & Hscs0 & Hcs1 & Hscs1 & Hargs & Hregs & Hsregs
        & Hstk & Hsstk & Hworld_interp & Hstk_val & %Hrevoked_stk & Hcstk & Hcstk_spec & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked
              Nswitcher W C wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller
              b_stk e_stk a_stk stk_mem stk_mem_spec arg_rmap arg_smap rmap smap stk Ws Cs false
             with "[-]");
      [exact Hdom|exact Hsdom|exact Hrdom|exact Hsrdom|].
    iFrame "∗#%".
  Qed.

End Switcher.
