From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From griotte Require Import ftlr_base interp_weakening interp_switcher_return.
From griotte Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From griotte Require Import sts_multiple_updates region_invariants_revocation.
From griotte Require Export switcher switcher_preamble switcher_macros_spec switcher_helpers.
From griotte Require Import switcher_spec_call_blocks world_ghost_theory world_interp_stack.
From griotte Require Import map_simpl register_tactics proofmode.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type OType Word Σ} {cstackg : CSTACKG Σ} {relg : relGS Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout} {swlayoutwf : switcherLayoutWf}
  .

  Implicit Types W : WORLD.
  Implicit Types C : CmptName.
  Notation V := (WORLD -n> (leibnizO CmptName) -n> (leibnizO Word) -n> iPropO Σ).

  Lemma switcher_cc_specification_gen
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be safe-to-share *)
                     ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                           rarg ↦ᵣ warg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C warg
                             else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h : list Word),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own cerise_nais ⊤
              ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ world_interp_open W2 C callee_stk_region
              ∗ StackOpenWorldResources interp W2 C callee_stk_region stk_mem_h
              ∗ cstack_frag cstk
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              (* cgp is restored, cra points to the next  *)
              ∗ cgp ↦ᵣ wcgp_caller ∗ cra ↦ᵣ wcra_caller ∗ cs0 ↦ᵣ wcs0_caller ∗ cs1 ↦ᵣ  wcs1_caller
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
              ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              ∗ [[ a_stk , (a_stk ^+ 4)%a ]] ↦ₐ [[ stk_mem_l ]]
              ∗ [[ (a_stk ^+ 4)%a , e_stk ]] ↦ₐ [[ stk_mem_h ]]
              ∗ interp_continuation cstk Ws Cs
              ∗ £ 2
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ na_own cerise_nais ⊤
              (* Registers are preserved *)
              ∗ PC ↦ᵣ updatePcPerm wcra_caller
              ∗ cgp ↦ᵣ wcgp_caller
              ∗ cra ↦ᵣ wcra_caller
              ∗ cs0 ↦ᵣ wcs0_caller
              ∗ cs1 ↦ᵣ wcs1_caller
              ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
              ∗ ca0 ↦ᵣ WInt ENOTENOUGHTRUSTEDSTACK
              ∗ ca1 ↦ᵣ WInt 0
              ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
              (* Stack frame *)
              ∗ [[ a_stk , (a_stk ^+4)%a ]] ↦ₐ [[ [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller] ]]
              ∗ [[ (a_stk ^+4)%a , e_stk ]] ↦ₐ [[ (drop 4 stk_mem) ]]

              (* Interpretation of the world and stack, at the moment of the switcher_call *)
              ∗ world_interp W C
              ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
              ∗ £ 2
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}
  )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.

    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & Hstk_val & %Hstk_revoked & Hcstk & Hcont & Hpost)".
    subst callee_stk_region.

    assert ( exists wr0, rmap !! ct2 = Some wr0) as [wr0 Hwr0].
    { rewrite -/(is_Some (rmap !! ct2)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ct2 with "Hregs") as "[Hct2 Hregs]"; first by simplify_map_eq.
    assert ( exists wr1, rmap !! ctp = Some wr1) as [wr1 Hwr1].
    { rewrite -/(is_Some (rmap !! ctp)).
      apply elem_of_dom. rewrite Hdom.
      apply elem_of_difference; split; [apply all_registers_s_correct|set_solver].
    }
    iDestruct (big_sepM_delete _ _ ctp with "Hregs") as "[Hctp Hregs]"; first by simplify_map_eq.

    (* --- Extract the code from the invariant --- *)
    iMod (na_inv_acc with "Hswitcher Hna")
      as "(Hswitcher_inv & Hna & Hclose_switcher_inv)" ; auto.
    rewrite /switcher_inv.
    iDestruct "Hswitcher_inv"
      as (a_tstk cstk' tstk_next)
           "(>Hmtdc & >%Hot_bounds & >Hcode & >Hb_switcher & >Htstk & >[%Hbounds_tstk_b %Hbounds_tstk_e]
           & Hcstk_full & >%Hlen_cstk & Hstk_interp & #Hp_ot_switcher)".
    codefrag_facts "Hcode".
    rename H into Hcont_switcher_region.
    iHide "Hclose_switcher_inv" as hclose_switcher_inv.
    iHide "Hswitcher" as hinv_switcher.

    set (Hcall := switcher_call_entry_point).
    set (Hsize := switcher_size).
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+(length switcher_instrs))%a)
      by solve_addr.

    rewrite /switcher_instrs /assembled_switcher.
    repeat (iEval (cbn [fmap list_fmap]) in "Hcode").
    repeat (iEval (cbn [concat]) in "Hcode").
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_0_spec with
      "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls"; iHide "Hcls" as hcont.
    iApply (switcher_call_block_1_spec with
      "[- $HPC $Hctp $Hct2 $Hcsp $Hcode]"); eauto; iFrame; iNext.
    iIntros "(HPC & Hctp & Hct2 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block 2 "Hcode" as a_entry_first_spill Ha_entry_first_spill "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_csp_check_loc.
    iApply (switcher_call_block_2_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcra $Hcgp $Hcsp $Hstk $Hcode]"); eauto; iNext.
    iIntros (stk_mem')
      "(HPC & Hcs0 & Hcs1 & Hcra & Hcgp & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hstk
        & %Hastk_bounds_all & %Hstk_mem' & Hcode)".
    destruct Hastk_bounds_all as [Hastk_bstk Hastk_bounds_all].
    destruct Hastk_bounds_all as [Hastk_bounds Hastk_some].
    destruct Hastk_some as [a_stk4' Hastk_some].
    subst stk_mem'.
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by
      (unfold a_stk4; rewrite (finz_incr_eq Hastk_some); exact Hastk_some).

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block 3 "Hcode" as a_tstack_push Ha_tstack_push "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_entry_first_spill.
    iApply (switcher_call_block_3_spec with
      "[- $HPC $Hcs0 $Hctp $Hct2 $Hcsp $Hmtdc $Htstk $Hcode]"); eauto.
    { solve_addr+Ha_tstack_push Hcont_switcher_region. }
    iNext.
    iIntros "[
      (%tstk_next' & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc
        & Ha_tstk1 & Htstk & %Ha_tstk1_facts & %Htstk_next' & Hcode & Hlc)
      |
      (%Htskt & HPC & Hcs0 & Hctp & Hct2 & Hcsp & Hmtdc & Htstk & Hcode)
    ]"
    ; [destruct Ha_tstk1_facts as [Ha_tstk2 Ha_tstk1_bound] | ]
    ; unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont
    ; cycle 1.
    {
      (* ----------------------------------------------  *)
      (* ------ Lswitch_trusted_stack_exhausted -------  *)
      (* ----------------------------------------------  *)
      iAssert ([∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg)%I
        with "[Hargs]" as "Hargs".
      { destruct is_entry_point_known.
        + iDestruct "Hargs" as "(% & _ & Hargs)".
          iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]".
        + iApply (big_sepM_impl with "Hargs"); eauto.
          iIntros (r w Hr) "!> [$ _]".
      }
      iExtractList "Hargs" [ca0; ca1] as ["Hca0"; "Hca1"].

      focus_block 16 "Hcode" as a_tstk_exhausted Ha_tstk_exhausted "Hcode" "Hcls"; iHide "Hcls" as hcont.
      iApply (switcher_call_block_16_spec with
        "[- $HPC $Hcs0 $Hcs1 $Hcgp $Hcra $Hca0 $Hca1 $Hcsp
          $Ha_stk $Ha_stk1 $Ha_stk2 $Ha_stk3 $Hcode]"); eauto.
      { solve_addr+Ha_tstk_exhausted Hcont_switcher_region. }
      iNext.
      iIntros "(HPC & Hcs0 & Hcs1 & Hcgp & Hcra & Hca0 & Hca1 & Hcsp
        & Ha_stk & Ha_stk1 & Ha_stk2 & Ha_stk3 & Hcode & Hlc)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* ---- clear registers  ---- *)
      focus_block 14 "Hcode" as a7 Ha7 "Hcode" "Hcls"; iHide "Hcls" as hcont.

      iExtractList "Hargs" [ca2; ca3; ca4; ca5; ct0]
        as ["Hca2"; "Hca3"; "Hca4"; "Hca5"; "Hct0"].
      iClear "Hargs".

      iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_eq.
      rewrite -delete_insert_ne; last done.
      iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_eq.
      iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca2] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca3] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca4] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hca5] Hregs") as "Hregs";[iFrame|].
      iDestruct (big_sepM_insert_2 with "[Hct0] Hregs") as "Hregs";[iFrame|].

      iApply (clear_registers_post_call_spec with "[- $HPC $Hregs $Hcode]"); try solve_pure.
      { clear -Hdom Hrdom.
        repeat (rewrite -delete_insert_ne //).
        repeat (rewrite dom_delete_L).
        repeat (rewrite dom_insert_L).
        rewrite Hdom /=.
        set_solver.
      }
      iNext; iIntros "H".
      iDestruct "H" as (arg_rmap') "(%Harg_rmap' & HPC & Hrmap & Hcode)".
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      focus_block 15 "Hcode" as a10 Ha10 "Hcode" "Hcsl"; iHide "Hcsl" as hcont.
      (* Jalr cnull cra *)
      iAssert (⌜map_Forall (λ (_ : RegName) (x : Word), x = WInt 0) arg_rmap' ⌝)%I as
        "%Harg_rmap'_zeroes".
      { iDestruct (big_sepM_sep with "Hrmap") as "[_ %]"; auto. }
      iExtract "Hrmap" cnull as "[Hcnull %]".
      iInstr "Hcode" with "Hlc".
      iAssert ( ∃ wnull, cnull ↦ᵣ wnull ∗ ⌜ wnull = WInt 0⌝ )%I with "[Hcnull]" as (wnull) "Hcnull".
      { iFrame; done. }
      iInsert "Hrmap" cnull.
      iAssert (⌜ <[cnull := wnull]> arg_rmap' = arg_rmap' ⌝)%I as "%Harg_rmap'_id".
      { iDestruct (big_sepM_sep with "Hrmap") as "[Hrmap %Hint]".
        iPureIntro.
        clear -Harg_rmap' Hint Harg_rmap'_zeroes.
        assert (is_Some (arg_rmap' !! cnull)) as [? Hcnull] by (rewrite -elem_of_dom Harg_rmap' ; set_solver).
        apply insert_id.
        pose proof (map_Forall_insert_1_1 _ _ _ _ Hint); cbn in *.
        rewrite H.
        rewrite Hcnull.
        by eapply map_Forall_lookup in Hcnull; eauto; cbn in *; simplify_map_eq.
      }
      rewrite Harg_rmap'_id.
      clear dependent Harg_rmap'_id Harg_rmap'_zeroes wcnull wnull.
      unfocus_block "Hcode" "Hcsl" as "Hcode"; subst hcont.

    (* Close the switcher's invariant *)
      iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hstk_interp]") as "HH".
      { iNext. iExists _,_. iFrame "∗ # %".
        iPureIntro; split; auto.
      }
      iEval (cbn) in "HPC".
      iEval (cbn) in "Hcra".
      iApply ("Hpost" $! W _ [] [] with "[-]"); iRight; iFrame "∗%".
      iSplit.
      { iPureIntro.
        split; first solve_addr+Hastk Hastk_bstk.
        split; first solve_addr+Hastk Hastk_bounds Hastk_bstk.
        done.
      }
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 1)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 2)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 3)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      iApply region_pointsto_cons; eauto.
      { instantiate (1 := (a_stk ^+ 4)%a); solve_addr+Hastk. }
      { solve_addr+Hastk. }
      iFrame.
      rewrite /region_pointsto.
      rewrite (finz_seq_between_empty a_stk4 a_stk4); last solve_addr.
      done.
    }
    subst tstk_next'.

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block 4 "Hcode" as a_stack_chop Ha_stack_chop "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_push.
    iApply (switcher_call_block_4_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hcsp $Hcode]"); eauto; [|iNext].
    { rewrite /isWithin; solve_addr+Hastk_bounds. }
    iIntros "(HPC & Hcs0 & Hcs1 & Hcsp & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block 5 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_stack_chop.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]"); try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block 6 "Hcode" as a_LoadCapPCC Ha_LoadCapPCC "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear_stk1.
    iApply (switcher_call_block_6_spec with
      "[- $HPC $Hcs0 $Hcs1 $Hb_switcher $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hb_switcher & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block 7 "Hcode" as a_unseal_entry Ha_unseal_entry "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_LoadCapPCC.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    destruct (is_sealed_with_o wct1_caller ot_switcher) eqn:Hwct1_caller; cycle 1.
    { (* wct1_caller is not sealed with ot_switcher, so the next instruction will fail *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_unseal_nomatch_r2 with "[$HPC $Hi $Hct1 $Hcs0]") ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    assert (∃ w_entry_point, wct1_caller = WSealed ot_switcher w_entry_point ) as [w_entry_point ->].
    { destruct wct1_caller as [ | [] | |]; cbn in Hwct1_caller; try discriminate.
      exists sb. apply Z.eqb_eq in Hwct1_caller.
      replace ot with ot_switcher by solve_addr.
      done.
    }
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher w_entry_point)).
    iEval (cbn) in "Htarget_v".
    rewrite /interp_sb.
    iAssert (sts_seals_std C ot_switcher {[WSealable w_entry_point]}) as "#Htarget_v'".
    { iApply sts_seals_std_weaken; last iFrame "Htarget_v"; last set_solver+. }
    iDestruct (world_interp_seal_pred_singleton with "Hp_ot_switcher Htarget_v' Hworld_interp")
      as "(Hworld_interp & #HP)".
    iInstr "Hcode"; [done|..].
    { rewrite /withinBounds; solve_addr. }
    iDestruct "HP" as (??????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & #Hentry' & #Hentry'_borrow & Hexec)".
    simpl fst; simpl snd.
    destruct w_entry_point; cbn in Heq; simplify_eq.
    iEval (cbn) in "Hentry'"; iEval (cbn) in "Hentry'_borrow".
    iApply (switcher_call_block_7_after_unseal_spec with
      "[- $Htbl3 $HPC $Hcs0 $Hct1 $Hct2 $Hcode]"); eauto; iNext.
    iIntros "(HPC & Hcs0 & Hct1 & Hct2 & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_callee_load -----  *)
    (* ------------------------------  *)
    focus_block 8 "Hcode" as a_callee_load Ha_callee_load "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_unseal_entry.
    iApply (switcher_call_block_8_spec with
      "[- $Htbl1 $Htbl2 $HPC $Hcs0 $Hcs1 $Hct1 $Hct2 $Hcgp $Hcra $Hcode]");
      eauto; iNext.
    iIntros "(HPC & Hcs0 & Hcs1 & Hct1 & Hct2 & Hcgp & Hcra & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block 9 "Hcode" as a_clear Ha_clear "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_callee_load.

    iApply (clear_registers_pre_call_skip_spec
              _ _ _ _ _ arg_rmap (nargs+1)
             with "[- $HPC $Hcode]")
    ; try solve_pure.
    { lia. }
    replace (Z.of_nat (nargs + 1))%Z with (Z.of_nat nargs + 1)%Z by lia.
    replace (nargs + 1 - 1) with nargs by lia.
    iFrame.
    iSplitL "Hargs".
    { destruct is_entry_point_known.
      + iDestruct "Hargs" as "(%nargs0 & Hentry & Hargs)".
        destruct g.
        * iDestruct (entry_agree _ nargs nargs0 with "Hentry' Hentry") as "<-"; iFrame.
        * iDestruct (entry_agree _ nargs nargs0 with "Hentry'_borrow Hentry") as "<-"; iFrame.
      + iApply (big_sepM_impl with "Hargs").
        iIntros "!> %k %w' _ [$ Hinterp]".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ----------------------------------- *)
    (* ---- clear_registers_pre_call ----- *)
    (* ----------------------------------- *)
    focus_block 10 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear.

    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    rewrite -delete_insert_ne; last done.
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_eq.
    iDestruct (big_sepM_insert_2 with "[Hcs1] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcs0] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hct1] Hregs") as "Hregs";[iFrame|].

    iApply (clear_registers_pre_call_spec with "[- $HPC $Hcode $Hregs]"); try solve_pure.
    { rewrite !dom_insert_L Hdom. set_solver-. }

    iIntros "!> (%rmap' & %Hrmap' & HPC & Hregs & Hcode)".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    (* ------------------------------ *)
    (* ---- Lswitch_callee_call ----- *)
    (* ------------------------------ *)
    focus_block 11 "Hcode" as a_callee_call Ha_callee_call "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear'.


    set (frame :=
           {| wret := wcra_caller;
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              b_stk := b_stk;
              a_stk := a_stk;
              e_stk := e_stk;
              ccrel := Known_to_Unknown
           |}).

    (* --- Close the world with the cleared stack --- *)

    rewrite {1}(finz_seq_between_split _ (a_stk ^+ 4)%a);[|solve_addr].
    iDestruct (StackRevokedResources_app with "Hstk_val") as "[#Hstk_val_save #Hstk_val']".

    assert (revoked_addresses W (finz.seq_between (a_stk ^+ 4)%a e_stk)) as Hrev.
    { clear-Hstk_revoked Hastk_some.
      rewrite /revoked_addresses Forall_forall in Hstk_revoked.
      rewrite /revoked_addresses Forall_forall.
      intros a Ha.
      apply Hstk_revoked.
      rewrite !elem_of_finz_seq_between in Ha |- *.
      solve_addr.
    }

    iMod (world_interp_reinstate_stack with "Hworld_interp Hstk_val' Hstk") as "Hworld_interp"; auto.
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }

    iSpecialize ("Hexec" $!
                   (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary)
                  with "[]").
    { iPureIntro.
      apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp. auto. }
    iInstr "Hcode".
    iSpecialize ("Hexec" $!
                   (frame :: cstk)
                   ((std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) :: Ws)
                   (C::Cs)).
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with
      "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Ha_tstk1 Hstk_interp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3]") as "HH".
    { iNext. iExists (a_tstk ^+ 1)%a,(drop 1 tstk_next).
      iFrame "Hmtdc Hb_switcher Hp_ot_switcher".
      rewrite (finz_incr_eq Ha_tstk2). simpl.
      replace ((a_tstk ^+ 1)%a ^+ -1)%a with a_tstk by solve_addr+Ha_tstk2.
      iSplit;[auto|]. iFrame "Htstk Hstk_interp".
      iSplit;[iPureIntro; solve_addr+Hbounds_tstk_b Ha_tstk2 Ha_tstk1_bound|].
      iSplit;[iPureIntro; solve_addr+Ha_tstk2 Hlen_cstk|].
      iFrame; cbn.
      iFrame. iPureIntro.
      rewrite Hastk_some. split;[solve_addr|]. split;[solve_addr|eauto]. }

    iApply "Hexec".
    iAssert (interp (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk) Temporary) C
      (WCap RWL Local (a_stk ^+ 4)%a e_stk a_stk)) as "Hstk4v".
    { iApply fixpoint_interp1_eq. iSimpl.
      rewrite {2}/StackRevokedResources /StackWorldResources big_sepL2_replicate_r; last done.
      iApply (big_sepL_impl with "Hstk_val'").
      iIntros "!>" (k a Ha) "Hr".
      iDestruct "Hr" as (φ p) "(Hφ & Hmono & Hrel & (HmonoR & Hzcond & Hrcond & Hwcond & Hpers) & %Hperm_flow)".
      iExists p,φ.
      iFrame "∗#%".
      iSplit.
      { erewrite readAllowed_flowsto; eauto. }
      iSplit.
      { erewrite writeAllowed_flowsto; eauto. }
      iSplitL "Hmono HmonoR".
      {
        rewrite /monoReq /monotonicity_guarantees_region.
        erewrite isWL_flowsto; eauto.
        rewrite std_sta_update_multiple_lookup_in_i.
        2: { apply list_elem_of_lookup. eauto. }
        done.
      }
      iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply list_elem_of_lookup. eauto.
    }
    iSplitL "Hpost Hlc Hcont".
    { simpl.
      iFrame.
      iEval (cbn).
      iSplitR.
      { iFrame "Hstk4v". }
      iIntros (W' HW' ?????) "(HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
      & Hca1 & #Hv' & % & Hregs & Hstk & Hstk' & Hworld_interp & Hcls & Hcont & Hcstk & Own)".
      iApply "Hpost";iLeft. simplify_eq.
      iFrame "∗#%".
      iSplit.
      {
        iApply interp_monotone; first done.
        iApply (interp_lea with "Hstk4v"); done.
      }
      iSplit.
      { iPureIntro; repeat split; solve_addr+Hastk_bstk Hastk_bounds Hastk_some. }

      clear -Hrev HW'.
      iPureIntro; intros k a Ha; cbn.
      eapply region_state_pub_temp;[apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply list_elem_of_lookup; eauto.
    }
    iSplitR.
    { iPureIntro; simpl; split; [|split]; auto.
      apply related_sts_pub_refl_world.
    }

    iFrame.
    rewrite /execute_entry_point_register.

    iDestruct (big_sepM_sep with "Hregs") as "[Hregs #Hnil]".
    iDestruct (big_sepM_sep with "Hargs") as "[Hargs #Hval]".
    iDestruct (big_sepM_union with "[$Hargs $Hregs]") as "Hregs".
    { apply map_disjoint_dom. rewrite Hrmap' Harg_rmap'.
      set_solver+. }
    iDestruct (big_sepM_insert_2 with "[Hcsp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcra] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[Hcgp] Hregs") as "Hregs";[iFrame|].
    iDestruct (big_sepM_insert_2 with "[HPC] Hregs") as "Hregs";[iFrame|].

    cbn.
    iFrame.
    iSplit;last (iPureIntro; split ;[split|];[reflexivity|reflexivity|solve_addr]).
    iSplit.
    { iPureIntro. simpl. intros rr. clear -Harg_rmap' Hrmap'.
      destruct (decide (rr = PC));simplify_map_eq;[eauto|].
      destruct (decide (rr = cgp));simplify_map_eq;[eauto|].
      destruct (decide (rr = cra));simplify_map_eq;[eauto|].
      destruct (decide (rr = csp));simplify_map_eq;[eauto|].
      apply elem_of_dom. rewrite dom_union_L Hrmap' Harg_rmap'.
      rewrite difference_union_distr_r_L union_intersection_l.
      rewrite -union_difference_L;[|apply all_registers_subseteq].
      apply elem_of_intersection. split;[apply all_registers_s_correct|].
      apply elem_of_union. right.
      apply elem_of_difference. split;[apply all_registers_s_correct|set_solver]. }

    repeat iSplit.
    - iPureIntro. simplify_map_eq. reflexivity.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_callee_call Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro. clear -Hastk_some. simplify_map_eq. done.
    - iApply (interp_lea with "Hstk4v"); first done.
    - iIntros (r v Hr Hv).
      assert (r ∉ ({[ PC ; cgp ; cra ; csp ]} : gset RegName)) as Hr'.
      {
        clear -Hr.
        do 8 (destruct nargs; first set_solver).
        induction nargs.
        + set_solver+Hr.
        + apply IHnargs; set_solver+Hr.
      }
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr Hr']).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Harg_rmap' Hrmap' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv as [Hv|Hv].
      + iDestruct (big_sepM_lookup with "Hval") as "Hv";[apply Hv|].
        destruct (decide (r ∈ _)) as [|Hcontra]; last set_solver+Hcontra Hr.
        iApply (interp_monotone with "[] Hv").
        iPureIntro; apply related_sts_pub_update_multiple_temp; auto.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
        iApply interp_int.
    - iIntros (r v Hr Hv).
      repeat (rewrite lookup_insert_ne in Hv;[|set_solver+Hr]).
      apply lookup_union_Some in Hv.
      2: {
        apply map_disjoint_dom_2.
        rewrite Harg_rmap' Hrmap' /=; set_solver+.
      }
      replace (nargs + 1 - 1) with nargs by lia.
      destruct Hv.
      + iDestruct (big_sepM_lookup with "Hval") as "?";eauto.
        destruct (decide (r ∈ _)) as [Hcontra|]; last iFrame "#".
        set_solver+Hcontra Hr.
      + iDestruct (big_sepM_lookup with "Hnil") as "%";eauto; simplify_eq.
  Qed.

  (* This specification unifies the two possible outcomes of the switcher call.
     It closes the world, and then revokes it.
   *)
  Lemma switcher_cc_specification_gen_revoked
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (is_entry_point_known : bool)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller
    ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C wct1_caller else True)
    ∗ (if is_entry_point_known
       then ∃ nargs, wct1_caller ↦□ₑ nargs
                     (* Argument registers, need to be safe-to-share *)
                     ∗ ( [∗ map] rarg↦warg ∈ arg_rmap,
                           rarg ↦ᵣ warg
                           ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                             then interp W C warg
                             else True )
       else ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
      )
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l',
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
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ᵣ updatePcPerm wcra_caller
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller
            ∗ cra ↦ᵣ wcra_caller
            ∗ cs0 ↦ᵣ wcs0_caller
            ∗ cs1 ↦ᵣ  wcs1_caller
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})


    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hworld_interp & #Hstk_val & %Hrevoked_stk & Hcstk & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iApply switcher_cc_specification_gen; eauto; iFrame "∗#%".
    iIntros (W' rmap' stk_mem_l stk_mem_h).
    iNext; iIntros "[H|H]".
    + clear stk_mem.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds
      & Hworld_interp_C & Hstack_revoked_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 #Hinterp_wca0] ] & [%warg1 [Hca1 #Hinterp_wca1] ]
      & Hrmap & Hstk_l & Hstk_h & HK & [Hlc Hlc'])".

      iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
      iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
      iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hworld_interp_C".

      iDestruct (close_world_interp_opening_resources
                  with "[$Hworld_interp_C $Hstack_revoked_W2 $Hstk_h]")
        as "Hworld_interp_C".
      { apply finz_seq_between_NoDup. }
      { set_solver+. }
      { by rewrite finz_seq_between_length in Hlen_stk_l. }
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
      as (l') "(%Hl_unk' & Hworld_interp_C & Hstack_revoked_W2 & Hrevoked_W2 & >[%stk_mem_h' Hstk_h] & [Hrevoked_l' %Hrevoked_W2_l'])".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
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

    + clear W' stk_mem_l stk_mem_h.
      set (stk_mem_l := [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller]).
      set (stk_mem_h := drop 4 stk_mem).
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h
           & Hworld_interp_C & Hclose
           & Hcstk_frag & HK & [Hlc Hlc'])".
      pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].

      iMod ( world_interp_revoke _ _ l_unk with "[$Hworld_interp_C]") as
        "(Hworld_interp_C & Hrevoked_l & %Hrevoked_l)"; auto.
      { split; auto. }
      iDestruct (lc_fupd_elim_later with "[$] [$Hrevoked_l]") as ">Hrevoked_l".

      iSpecialize ("Hpost" $! (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk)
                                 Temporary) rmap' (stk_mem_l++stk_mem_h) l_unk).
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
      iSplit; first iPureIntro.
      { eapply Forall_impl; eauto.
        cbn; intros a Ha.
        apply revoke_lookup_Revoked; done.
      }
      iSplit; first iApply interp_int.
      iSplit; first iApply interp_int.
      iApply (region_pointsto_split _ _ (a_stk ^+4)%a); last iFrame.
      { solve_addr+ Hcsp_bounds. }
      { subst stk_mem_l. cbn.
        destruct Hcsp_bounds as (?&?&Ha4).
        pose proof (finz_incr_iff_dist a_stk (a_stk ^+ 4)%a 4) as [Hdist _].
        by apply Hdist in Ha4 as [? ?].
      }
  Qed.

  Lemma switcher_cc_specification
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (w_entry_point : Sealable)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    (nargs : nat)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let wct1_caller := WSealed ot_switcher w_entry_point in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ interp W C wct1_caller ∗ wct1_caller ↦□ₑ nargs
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg
                                      ∗ if decide (rarg ∈ dom_arg_rmap nargs)
                                        then interp W C warg
                                        else True )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l',
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
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ᵣ updatePcPerm wcra_caller
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller
            ∗ cra ↦ᵣ wcra_caller
            ∗ cs0 ↦ᵣ wcs0_caller
            ∗ cs1 ↦ᵣ  wcs1_caller
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 target callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ true)
            ; eauto; iFrame "∗#%".
    subst target; cbn.
    destruct ( (ot_switcher =? ot_switcher)%Z ); eauto.
  Qed.

  Lemma switcher_cc_specification_alt
    (Nswitcher : namespace)
    (W : WORLD)
    (C : CmptName)
    (wcgp_caller wcra_caller wcs0_caller wcs1_caller wct1_caller : Word)
    (b_stk e_stk a_stk : Addr)
    (stk_mem : list Word)
    (arg_rmap rmap : Reg)
    (cstk : CSTK) (Ws : list WORLD) (Cs : list CmptName)
    :
    let a_stk4 := (a_stk ^+ 4)%a in
    let callee_stk_region := finz.seq_between a_stk4 e_stk in
    dom rmap = all_registers_s ∖ ({[ PC ; cgp ; cra ; csp ; ct1 ; cs0 ; cs1 ]} ∪ dom_arg_rmap 8) ->
    is_arg_rmap arg_rmap 8 ->

    (* Switcher Invariant *)
    na_inv cerise_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own cerise_nais ⊤
    (* Registers *)
    ∗ PC ↦ᵣ WCap XSRW_ Local b_switcher e_switcher a_switcher_call
    ∗ cgp ↦ᵣ wcgp_caller
    ∗ cra ↦ᵣ wcra_caller
    (* Stack register *)
    ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
    (* Entry point of the target compartment *)
    ∗ ct1 ↦ᵣ wct1_caller ∗ (if is_sealed_with_o wct1_caller ot_switcher then interp W C wct1_caller else True)
    ∗ cs0 ↦ᵣ wcs0_caller
    ∗ cs1 ↦ᵣ wcs1_caller
    (* Argument registers, need to be safe-to-share *)
    ∗ ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg ∗ interp W C warg )
    (* All the other registers *)
    ∗ ( [∗ map] r↦w ∈ rmap, r ↦ᵣ w )

    (* Stack frame *)
    ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]

    (* Interpretation of the world and stack, at the moment of the switcher_call *)
    ∗ world_interp W C
    ∗ StackRevokedResources W C (finz.seq_between a_stk e_stk)
    ∗ ⌜ revoked_addresses W (finz.seq_between a_stk e_stk) ⌝
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word) l',
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
            ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
            (* Interpretation of the world *)
            ∗ world_interp (revoke W2) C
            ∗ cstack_frag cstk
            ∗ PC ↦ᵣ updatePcPerm wcra_caller
            (* cgp is restored, cra points to the next  *)
            ∗ cgp ↦ᵣ wcgp_caller
            ∗ cra ↦ᵣ wcra_caller
            ∗ cs0 ↦ᵣ wcs0_caller
            ∗ cs1 ↦ᵣ  wcs1_caller
            ∗ csp ↦ᵣ WCap RWL Local b_stk e_stk a_stk
            ∗ (∃ warg0, ca0 ↦ᵣ warg0 ∗ interp W2 C warg0)
            ∗ (∃ warg1, ca1 ↦ᵣ warg1 ∗ interp W2 C warg1)
            ∗ ( [∗ map] r↦w ∈ rmap', r ↦ᵣ w ∗ ⌜ w = WInt 0 ⌝ )
            ∗ [[ a_stk , e_stk ]] ↦ₐ [[ stk_mem ]]
            ∗ interp_continuation cstk Ws Cs
              -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own cerise_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hworld_interp & Hstk_val & % & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false)
            ; eauto; iFrame "∗#%".
  Qed.

End Switcher.
