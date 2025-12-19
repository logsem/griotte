From iris.algebra Require Import frac excl_auth.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre adequacy lifting.
From cap_machine Require Import ftlr_base interp_weakening interp_switcher_return.
From cap_machine Require Import logrel fundamental interp_weakening memory_region rules proofmode monotone.
From cap_machine Require Import multiple_updates region_invariants_revocation.
From cap_machine Require Export switcher switcher_preamble.
From stdpp Require Import base.
From cap_machine Require Import logrel_extra switcher_macros_spec.
From cap_machine.proofmode Require Import map_simpl register_tactics proofmode.


Section Switcher.
  Context
    {Σ:gFunctors}
    {ceriseg:ceriseG Σ} {sealsg: sealStoreG Σ}
    {Cname : CmptNameG}
    {stsg : STSG Addr region_type Σ} {cstackg : CSTACKG Σ} {heapg : heapGS Σ}
    {nainv: logrel_na_invs Σ}
    `{MP: MachineParameters}
    {swlayout : switcherLayout}
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
    na_inv logrel_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own logrel_nais ⊤
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
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem_l stk_mem_h : list Word),
        ( ( (* POST-CONDITION --- the call went through *)
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ na_own logrel_nais ⊤
              ∗ interp W2 C (WCap RWL Local a_stk4 e_stk a_stk4)
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ sts_full_world W2 C
              ∗ open_region_many W2 C callee_stk_region
              ∗ ([∗ list] a ; v ∈ callee_stk_region ; stk_mem_h, closing_resources interp W2 C a v)
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
          )
          ∨
            ( (* POST-CONDITION --- the call didn't went through, trusted stack exhausted *)
              ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              ∗ na_own logrel_nais ⊤
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
              ∗ sts_full_world W C
              ∗ region W C
              ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
              ∗ cstack_frag cstk
              ∗ interp_continuation cstk Ws Cs
            )
          )
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}
  )

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.

    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hsts & Hr & Hstk_val & Hcstk & Hcont & Hpost)".
    subst a_stk4.
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

    rewrite /switcher_instrs /switcher_call_instrs /switcher_return_instrs.
    rewrite -!app_assoc.
    assert (SubBounds b_switcher e_switcher a_switcher_call (a_switcher_call ^+ (length switcher_instrs))%a).
    { pose proof switcher_size.
      pose proof switcher_call_entry_point.
      solve_addr.
    }

    (* -----------------------------------  *)
    (* ----- Lswitch_csp_check_perm ------  *)
    (* -----------------------------------  *)
    focus_block_0 "Hcode" as "Hcode" "Hcls"; iHide "Hcls" as hcont.

    (* --- GetP ct2 csp --- *)
    iInstr "Hcode".

    (* ---  Mov ctp (encodePerm RWL) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    replace (encodePerm RWL - encodePerm RWL)%Z with 0%Z by lia.
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ------ Lswitch_csp_check_loc ------  *)
    (* -----------------------------------  *)
    focus_block 1 "Hcode" as a_csp_check_loc Ha_csp_check_loc "Hcode" "Hcls"; iHide "Hcls" as hcont.

    (* --- GetL ct2 csp --- *)
    iInstr "Hcode".

    (* --- Mov ctp (encodeLoc Local) --- *)
    iInstr "Hcode".

    (* --- Sub ct2 ct2 ctp --- *)
    iInstr "Hcode".

    (* --- Jnz 2 ct2 --- *)
    replace (encodeLoc Local - encodeLoc Local)%Z with 0%Z by lia.
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------------------  *)
    (* ---- Lswitch_entry_first_spill ----  *)
    (* -----------------------------------  *)
    focus_block 2 "Hcode" as a_entry_first_spill Ha_entry_first_spill "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_csp_check_loc.

    (* --- Store csp cs0 --- *)
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen.
    rewrite finz_seq_between_length in Hstklen.
    destruct (decide (b_stk <= a_stk < e_stk)%a) as [Hastk_inbounds|Hastk_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs0 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk_inbounds.
    destruct stk_mem as [|w0 stk_mem]; simplify_eq.
    assert (is_Some (a_stk + 1)%a) as [a_stk1 Hastk1];[solve_addr+Hastk_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk Hstk]"; eauto.
    { solve_addr+Hastk_inbounds Hastk1. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".


    (* --- Store csp cs1 --- *)
    destruct (decide (b_stk <= (a_stk ^+ 1)%a < e_stk)%a) as [Hastk1_inbounds|Hastk1_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcs1 $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk1_inbounds.
    destruct stk_mem as [|w1 stk_mem]; simplify_eq.
    assert (is_Some (a_stk1 + 1)%a) as [a_stk2 Hastk2];[solve_addr+Hastk1 Hastk1_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk1 Hstk]"; eauto.
    { solve_addr+Hastk1_inbounds Hastk1 Hastk2. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    (* --- Store csp cra --- *)
    destruct (decide (b_stk <= (a_stk ^+ 2)%a < e_stk)%a) as [Hastk2_inbounds|Hastk2_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcra $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk2_inbounds.
    destruct stk_mem as [|w2 stk_mem]; simplify_eq.
    assert (is_Some (a_stk2 + 1)%a) as [a_stk3 Hastk3];[solve_addr+Hastk1 Hastk2 Hastk2_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk2 Hstk]"; eauto.
    { solve_addr+Hastk2_inbounds Hastk1 Hastk2 Hastk3. }

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    (* --- Store csp cgp --- *)
    destruct (decide (b_stk <= (a_stk ^+ 3)%a < e_stk)%a) as [Hastk3_inbounds|Hastk3_inbounds]; cycle 1.
    {
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_store_fail_reg with "[$HPC $Hi $Hcgp $Hcsp]") ; try solve_pure.
      { rewrite /withinBounds; solve_addr. }
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    rewrite finz_dist_S in Hstklen; last solve_addr+Hastk3_inbounds.
    destruct stk_mem as [|w3 stk_mem]; simplify_eq.
    assert (is_Some (a_stk3 + 1)%a) as [a_stk4 Hastk4];[solve_addr+Hastk1 Hastk2 Hastk3 Hastk3_inbounds|].
    iDestruct (region_pointsto_cons with "Hstk") as "[Ha_stk3 Hstk]"; eauto.
    { solve_addr+Hastk3_inbounds Hastk1 Hastk2 Hastk3 Hastk4. }
    assert ((a_stk + 4)%a = Some a_stk4) as Hastk by solve_addr.
    assert ((a_stk ^+4)%a = a_stk4) as -> by solve_addr.

    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- Lea csp 1 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* -- Lswitch_trusted_stack_check_size --  *)
    (* --------------------------------------  *)
    focus_block 3 "Hcode" as a_tstack_ckeck_size Ha_tstack_ckeck_size "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_entry_first_spill.

    (* --- ReadSR ct2 mtdc --- *)
    iInstr "Hcode".

    (* --- GetA cs0 ct2 --- *)
    iInstr "Hcode".

    (* --- Add cs0 cs0 1%Z --- *)
    iInstr "Hcode".

    (* --- GetE ctp ct2 --- *)
    iInstr "Hcode".

    (* --- Sub ctp ctp cs0 --- *)
    iInstr "Hcode".

    (* --- Jnz 2%Z ctp --- *)
    destruct ( (a_tstk + 1 <? e_trusted_stack)%Z) eqn:Hsize_tstk
    ; iEval (cbn) in "Hctp"
    ; cycle 1.
    {
      iInstr "Hcode".
      (* --- Jmp  Lswitch_trusted_stack_exhausted_z --- *)
      iInstr "Hcode".
      { transitivity (Some ((a_switcher_call ^+ Lswitch_trusted_stack_exhausted_z)%a)); auto.
        rewrite /Lswitch_trusted_stack_exhausted_z.
        solve_addr+Ha_tstack_ckeck_size Hsize.
      }
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
      rewrite /switcher_fail_path_instrs /switcher_fail_path_instrs.

      (* ----------------------------------------------  *)
      (* ------ Lswitch_trusted_stack_exhausted -------  *)
      (* ----------------------------------------------  *)
      rewrite /Lswitch_trusted_stack_exhausted_z.
      focus_block 17 "Hcode" as a_tstk_exhausted Ha_tstk_exhausted "Hcode" "Hcls"; iHide "Hcls" as hcont.
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some a_stk3); auto; solve_addr+Hastk4. }
      (* Load cgp csp; *)
      iInstr "Hcode".
      { split; auto. solve_addr. }
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some a_stk2); auto; solve_addr+Hastk3. }
      (* Load cra csp; *)
      iInstr "Hcode".
      { split; auto. solve_addr. }
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some a_stk1); auto; solve_addr+Hastk2. }
      (* Load cra cs1; *)
      iInstr "Hcode".
      { split; auto. solve_addr. }
      (* Lea csp (-1)%Z; *)
      iInstr "Hcode".
      { transitivity (Some a_stk); auto; solve_addr+Hastk1. }
      (* Load cra cs0; *)
      iInstr "Hcode".
      { split; auto. solve_addr. }


      iAssert (
          (∃ wca0, ca0 ↦ᵣ wca0)
          ∗ (∃ wca1, ca1 ↦ᵣ wca1)
          ∗ (∃ wca2, ca2 ↦ᵣ wca2)
          ∗ (∃ wca3, ca3 ↦ᵣ wca3)
          ∗ (∃ wca4, ca4 ↦ᵣ wca4)
          ∗ (∃ wca5, ca5 ↦ᵣ wca5)
          ∗ (∃ wct0, ct0 ↦ᵣ wct0)
        )%I with "[Hargs]" as
          "([%wca0 Hca0]
          & [%wca1 Hca1]
          & [%wca2 Hca2]
          & [%wca3 Hca3]
          & [%wca4 Hca4]
          & [%wca5 Hca5]
          & [%wct0 Hct0]
          )".
      { iAssert ( [∗ map] rarg↦warg ∈ arg_rmap, rarg ↦ᵣ warg )%I with "[Hargs]" as "Hargs".
        { destruct is_entry_point_known.
          + iDestruct "Hargs" as "(% & _ & Hargs)".
            iApply (big_sepM_impl with "Hargs"); eauto.
            iIntros (r w Hr) "!> [$ _]".
          + iApply (big_sepM_impl with "Hargs"); eauto.
            iIntros (r w Hr) "!> [$ _]".
        }
        assert (∃ wca0, arg_rmap !! ca0 = Some wca0) as [wca0 Hwca0].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wca1, arg_rmap !! ca1 = Some wca1) as [wca1 Hwca1].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wca2, arg_rmap !! ca2 = Some wca2) as [wca2 Hwca2].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wca3, arg_rmap !! ca3 = Some wca3) as [wca3 Hwca3].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wca4, arg_rmap !! ca4 = Some wca4) as [wca4 Hwca4].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wca5, arg_rmap !! ca5 = Some wca5) as [wca5 Hwca5].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        assert (∃ wct0, arg_rmap !! ct0 = Some wct0) as [wct0 Hwct0].
        { apply elem_of_dom; rewrite Hrdom /=; set_solver+. }
        rewrite -(insert_id arg_rmap ca0 wca0); auto.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca0 _) ca1 wca1); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca1 _) ca2 wca2); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca2 _) ca3 wca3); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca3 _) ca4 wca4); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca4 _) ca5 wca5); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
        rewrite -(insert_id (delete ca5 _) ct0 wct0); last by simplify_map_eq.
        iDestruct (big_sepM_insert_delete with "Hargs") as "[$ Hargs]".
      }

      (* Mov ca0 ENOTENOUGHTRUSTEDSTACK; *)
      iInstr "Hcode".
      (* Mov ca1 0; *)
      iInstr "Hcode".
      (* Jmp Lswitch_callee_dead_zeros_z *)
      iInstr "Hcode".
      { transitivity (Some (a_switcher_call ^+ Lswitch_callee_dead_zeros_z)%a); auto.
        rewrite /Lswitch_callee_dead_zeros_z.
        solve_addr.
      }
      unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

      (* ---- clear registers  ---- *)
      rewrite /Lswitch_callee_dead_zeros_z.
      focus_block 15 "Hcode" as a7 Ha7 "Hcode" "Hcls"; iHide "Hcls" as hcont.

      iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_insert.
      rewrite -delete_insert_ne; last done.
      iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
      rewrite insert_delete_insert.
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

      focus_block 16 "Hcode" as a10 Ha10 "Hcode" "Hcsl"; iHide "Hcsl" as hcont.
      (* JmpCap cra *)
      iInstr "Hcode" with "Hlc".
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
        split; first solve_addr+Hastk Hastk_inbounds.
        split; first solve_addr+Hastk Hastk3_inbounds Hastk_inbounds.
        done.
      }
      iApply region_pointsto_cons; eauto; first solve_addr.
      iFrame.
      iApply region_pointsto_cons; eauto; first solve_addr.
      iFrame.
      iApply region_pointsto_cons; eauto; first solve_addr.
      iFrame.
      iApply region_pointsto_cons; eauto; first solve_addr.
      iFrame.
      rewrite /region_pointsto.
      rewrite (finz_seq_between_empty a_stk4 a_stk4); last solve_addr.
      done.
    }
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* --------------------------------------  *)
    (* ----- Lswitch_trusted_stack_push -----  *)
    (* --------------------------------------  *)
    focus_block 4 "Hcode" as a_tstack_push Ha_tstack_push "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_ckeck_size.

    (* --- Lea ct2 1 --- *)
    assert ( ∃ f3, (a_tstk + 1)%a = Some f3) as [f3 Htastk] by (exists (a_tstk ^+ 1)%a; solve_addr+Hsize_tstk).
    iInstr "Hcode".

    (* --- Store ct2 csp --- *)
    iDestruct (big_sepL2_length with "Htstk") as %Hlen.
    erewrite finz_incr_eq in Hlen;[|eauto].
    rewrite finz_seq_between_length in Hlen.
    destruct tstk_next.
    { exfalso.
      rewrite /= /finz.dist Z2Nat.inj_sub in Hlen;[|solve_addr].
      assert (e_trusted_stack = f3) as Heq;[solve_addr|].
      subst. solve_addr. }
    assert (is_Some (f3 + 1)%a) as [f4 Hf4];[solve_addr|].
    iDestruct (region_pointsto_cons _ f4 with "Htstk") as "[Hf3 Htstk]";[solve_addr|solve_addr|].
    replace (a_tstk ^+ 1)%a with f3 by solve_addr.
    iInstr "Hcode".
    { rewrite /withinBounds. solve_addr. }

    (* --- WriteSR mtdc ct2 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ----- Lswitch_stack_chop -----  *)
    (* ------------------------------  *)
    focus_block 5 "Hcode" as a_stack_chop Ha_stack_chop "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_tstack_push.

    (* --- GetE cs0 csp --- *)
    iInstr "Hcode".

    (* --- GetA cs1 csp --- *)
    iInstr "Hcode".

    (* --- Subseg csp cs1 cs0 --- *)
    iInstr "Hcode".
    { rewrite /isWithin. solve_addr. }

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- Clear stack -----  *)
    (* -----------------------  *)
    focus_block 6 "Hcode" as a_clear_stk1 Ha_clear_stk1 "Hcode" "Hcls"; iHide "Hcls" as hcont; clear dependent Ha_stack_chop.
    iApply (clear_stack_spec with "[- $HPC $Hcode $Hcsp $Hcs0 $Hcs1 $Hstk]"); try solve_pure.
    { solve_addr+. }
    { solve_addr. }
    iSplitL;[|iIntros "!> %Hcontr"; done].
    iIntros "!> (HPC & Hcsp & Hcs0 & Hcs1 & Hcode & Hstk)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* -----------------------  *)
    (* ----- LoadCapPCC ------  *)
    (* -----------------------  *)
    focus_block 7 "Hcode" as a_LoadCapPCC Ha_LoadCapPCC "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear_stk1.

    (* --- GetB cs1 PC --- *)
    iInstr "Hcode".

    (* --- GetA cs0 PC --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cs1 cs0 --- *)
    iInstr "Hcode".

    (* --- Mov cs0 PC --- *)
    iInstr "Hcode".

    (* --- Lea cs0 cs1 --- *)
    iInstr_lookup "Hcode" as "Hi" "Hcode".
    wp_instr.
    iApply (wp_lea_success_reg with "[$HPC $Hi $Hcs0 $Hcs1]");[solve_pure..| |].
    { instantiate (1:=(b_switcher ^+ 2)%a). solve_addr. }
    iIntros "!> (HPC & Hi & Hcs1 & Hcs0)".
    wp_pure.
    iSpecialize ("Hcode" with "[$]").

    (* --- Lea cs0 -2 --- *)
    iInstr "Hcode".
    { instantiate (1:= b_switcher). solve_addr. }

    (* --- Load cs0 cs0 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_unseal_entry ----  *)
    (* ------------------------------  *)
    focus_block 8 "Hcode" as a_unseal_entry Ha_unseal_entry "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_LoadCapPCC.

    (* --- UnSeal ct1 cs0 ct1 --- *)
    destruct (is_sealed_with_o wct1_caller ot_switcher) eqn:Hwct1_caller; cycle 1.
    { (* wct1_caller is not sealed with ot_switcher, so the next instruction will fail *)
      iInstr_lookup "Hcode" as "Hi" "Hcode".
      wp_instr.
      iApply (wp_unseal_nomatch_r2 with "[$HPC $Hi $Hct1 $Hcs0 $Hcs1]") ; try solve_pure.
      iIntros "!> _". wp_pure. wp_end. iIntros "%Hcontr";done.
    }
    assert (∃ w_entry_point, wct1_caller = WSealed ot_switcher w_entry_point ) as [w_entry_point ->].
    { destruct wct1_caller as [ | [] | |]; cbn in Hwct1_caller; try discriminate.
      exists sb. apply Z.eqb_eq in Hwct1_caller.
      replace ot with ot_switcher by solve_addr.
      done.
    }
    rewrite (fixpoint_interp1_eq _ _ (WSealed ot_switcher w_entry_point)).
    iDestruct "Htarget_v" as (P HpersP) "(HmonoP & HPseal & HP & HPborrow)".
    iDestruct (seal_pred_agree with "Hp_ot_switcher HPseal") as "Hagree".
    iSpecialize ("Hagree" $! (W,C,WSealable w_entry_point)).
    iInstr "Hcode";[done|..].
    { rewrite /withinBounds. solve_addr. }
    rewrite /safeC.
    iSimpl in "Hagree".
    iRewrite -"Hagree" in "HP".
    iDestruct "HP" as (??????????? Heq????) "(Htbl1 & Htbl2 & Htbl3 & #Hentry' & Hexec)". simpl fst. simpl snd.
    inversion Heq.

    (* iDestruct (entry_agree _ nargs nargs0 with "Hentry Hentry'") as "<-". *)

    (* --- Load cs0 ct1 --- *)
    wp_instr.
    iInv "Htbl3" as ">Ha_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- LAnd ct2 cs0 7 --- *)
    iInstr "Hcode".

    (* --- LShiftR cs0 cs0 3 --- *)
    iInstr "Hcode".

    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ------------------------------  *)
    (* ---- Lswitch_callee_load -----  *)
    (* ------------------------------  *)
    focus_block 9 "Hcode" as a_callee_load Ha_callee_load "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_unseal_entry.


    (* --- GetB cgp ct1 --- *)
    iInstr "Hcode".

    (* --- GetA cs1 ct1 --- *)
    iInstr "Hcode".

    (* --- Sub cs1 cgp cs1 --- *)
    iInstr "Hcode".

    (* --- Lea ct1 cs1 --- *)
    iInstr "Hcode".
    { instantiate (1:=b_tbl); solve_addr. }

    (* --- Load cra ct1 --- *)
    wp_instr.
    iInv "Htbl1" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
    iMod ("Hcls_tbl" with "[$]") as "_". iModIntro.
    wp_pure.

    (* --- Lea ct1 1 --- *)
    iInstr "Hcode".
    { instantiate (1:=(b_tbl ^+ 1)%a). solve_addr. }

    (* --- Load cgp ct1 --- *)
    wp_instr.
    iInv "Htbl2" as ">Hb_tbl" "Hcls_tbl".
    iInstr "Hcode".
    { split;auto. rewrite /withinBounds. solve_addr. }
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
    iInstr "Hcode".

    (* --- Add ct2 ct2 1 --- *)
    iInstr "Hcode".

    (* clear registers except parameters *)
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ---------------------------------------- *)
    (* ---- clear_registers_pre_call_skip ----- *)
    (* ---------------------------------------- *)
    focus_block 10 "Hcode" as a_clear Ha_clear "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_callee_load.

    rewrite encode_entry_point_eq_nargs;last lia.
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
        iEval (cbn) in "Hentry'".
        iDestruct (entry_agree _ nargs nargs0 with "Hentry' Hentry") as "<-".
        iFrame.
      + iApply (big_sepM_impl with "Hargs").
        iIntros "!> %k %w' _ [$ Hinterp]".
        destruct ( decide (k ∈ dom_arg_rmap nargs) ) ; auto.
    }
    iIntros "!> (%arg_rmap' & %Harg_rmap' & HPC & Hct2 & Hargs & Hcode)".
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.

    (* ----------------------------------- *)
    (* ---- clear_registers_pre_call ----- *)
    (* ----------------------------------- *)
    focus_block 11 "Hcode" as a_clear' Ha_clear' "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear.

    iDestruct (big_sepM_insert_2 with "[Hctp] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_insert.
    rewrite -delete_insert_ne; last done.
    iDestruct (big_sepM_insert_2 with "[Hct2] Hregs") as "Hregs";[iFrame|].
    rewrite insert_delete_insert.
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
    focus_block 12 "Hcode" as a_callee_call Ha_callee_call "Hcode" "Hcls"; iHide "Hcls" as hcont
    ; clear dependent Ha_clear'.


    set (frame :=
           {| wret := wcra_caller;
              wstk := (WCap RWL Local b_stk e_stk a_stk);
              wcgp := wcgp_caller;
              wcs0 := wcs0_caller;
              wcs1 := wcs1_caller;
              is_untrusted_caller := false
           |}).


    (* --- Close the world with the cleared stack --- *)

    rewrite {1}(finz_seq_between_split _ a_stk4);[|solve_addr].
    iDestruct (big_sepL_app with "Hstk_val") as "[#Hstk_val_save Hstk_val']".
    iDestruct (big_sepL2_length with "Hstk") as %Hstklen'.
    iAssert (
       [∗ list] y1 ∈ finz.seq_between a_stk4 e_stk,
         closing_revoked_resources W C y1 ∗ ⌜W.1 !! y1 = Some Revoked⌝
      )%I with "[Hstk_val']" as "#Hstk_val0".
    { iClear "#".
      replace ((((a_stk ^+ 1) ^+ 1) ^+ 1) ^+ 1)%a with a_stk4 in Hstklen by solve_addr.
      clear-Hstklen' Hstklen.
      iStopProof.
      revert Hstklen'.
      cbn in Hstklen.
      simplify_eq.
      revert Hstklen.
      rewrite -finz_seq_between_length.
      revert stk_mem.
      generalize (finz.seq_between a_stk4 e_stk) as la.
      clear.
      induction la as [|a la]
      ; iIntros (lv Hlv Hlen) "H"
      ; destruct lv ; simplify_eq
      ; cbn; first done.
      iDestruct "H" as "[ [$ $] $]".
    }
    iAssert (
        [∗ list] y1;y2 ∈ finz.seq_between a_stk4 e_stk;region_addrs_zeroes a_stk4 e_stk,
          (closing_revoked_resources W C y1 ∗ ⌜W.1 !! y1 = Some Revoked⌝) ∗ y1 ↦ₐ y2
      )%I with "[Hstk_val0 Hstk]" as "Hstk_val0'".
    { iDestruct "Hstk_val0" as "-#Hstk_val0".
      iClear "#".
      rewrite /region_pointsto.
      iDestruct (big_sepL2_to_big_sepL_l with "Hstk_val0") as "H"; eauto.
      iApply ( big_sepL2_sep); iFrame.
    }


    iMod (update_region_revoked_temp_pwl_multiple' with "Hsts Hr [$Hstk_val0']") as "[Hr Hsts]".
    { apply finz_seq_between_NoDup. }
    { apply Forall_replicate_eq. }

    iAssert (⌜Forall (λ k : finz MemNum, W.1 !! k = Some Revoked) (finz.seq_between a_stk4 e_stk)⌝)%I as %Hrev.
    { rewrite Forall_forall. iIntros (a Ha).
      iClear "∗".
      iDestruct (big_sepL_sep with "Hstk_val0") as "[_ H]".
      iDestruct (big_sepL_elem_of with "H") as "?"; eauto.
    }
    iSpecialize ("Hexec" $!
                   (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary)
                  with "[]").
    { iPureIntro.
      apply related_sts_pub_priv_world.
      apply related_sts_pub_update_multiple_temp. auto. }
    iInstr "Hcode".
    iSpecialize ("Hexec" $!
                   (frame :: cstk)
                   ((std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) :: Ws)
                   (C::Cs)).
    unfocus_block "Hcode" "Hcls" as "Hcode"; subst hcont.
    rewrite /load_word. iSimpl in "Hcgp".

    iDestruct (cstack_agree with "Hcstk_full Hcstk") as %Heq'. subst.
    iMod (cstack_update _ _ (frame :: cstk) with "Hcstk_full Hcstk") as "[Hcstk_full Hcstk]".
    iMod ("Hclose_switcher_inv" with "[$Hcode $Hna Hb_switcher $Hcstk_full Hmtdc Htstk Hf3 Hstk_interp Ha_stk Ha_stk1 Ha_stk2 Ha_stk3]") as "HH".
    { iNext. iExists f3,tstk_next.
      iFrame "Hmtdc Hb_switcher Hp_ot_switcher".
      rewrite (finz_incr_eq Hf4). simpl.
      replace (f3 ^+ -1)%a with a_tstk by solve_addr+Htastk.
      iSplit;[auto|]. iFrame "Htstk Hstk_interp".
      iSplit;[iPureIntro;solve_addr|].
      iSplit;[iPureIntro;solve_addr|].
      iFrame.
      replace (a_stk ^+ 1)%a with a_stk1 by solve_addr+Hastk1.
      replace (a_stk ^+ 2)%a with a_stk2 by solve_addr+Hastk1 Hastk2.
      replace (a_stk ^+ 3)%a with a_stk3 by solve_addr+Hastk1 Hastk2 Hastk3.
      iFrame. iPureIntro.
      replace (a_stk ^+ 4)%a with a_stk4 by solve_addr+Hastk.
      rewrite Hastk. split;auto. split;[solve_addr|]. split;[solve_addr|eauto]. }

    iApply "Hexec".
    iAssert (interp (std_update_multiple W (finz.seq_between a_stk4 e_stk) Temporary) C (WCap RWL Local a_stk4 e_stk a_stk)) as "Hstk4v".
    { iApply fixpoint_interp1_eq. iSimpl.
      iApply (big_sepL_impl with "Hstk_val0").
      iIntros "!>" (k a Ha) "(Hr & _)".
      iDestruct "Hr" as (φ p Hpers) "(Hφ & Hmono & HmonoR & Hzcond & Hrcond & Hwcond & Hrel & %Hperm_flow)".
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
        2: { apply elem_of_list_lookup. eauto. }
        done.
      }
      iPureIntro. apply std_sta_update_multiple_lookup_in_i. apply elem_of_list_lookup. eauto.
    }
    iSplitL "Hpost Hcont".
    { simpl.
      iFrame.
      iEval (cbn).
      replace (a_stk ^+ 4)%a with a_stk4 by solve_addr. iSplitR.
      { iNext. iFrame "Hstk4v". }
      iIntros "!>" (W' HW' ???????) "(HPC & Hcra & Hcsp & Hgp & Hcs0 & Hcs1 & Ha0 & #Hv
      & Hca1 & #Hv' & % & Hregs & % & % & Hstk & Hstk' & Hr & Hcls & Hsts & Hcont & Hcstk & Own)".
      iApply "Hpost";iLeft. simplify_eq.
      replace (a_stk0 ^+ 4)%a with a_stk4 by solve_addr.
      iFrame "∗#%".
      iSplit.
      {
        iApply interp_monotone; first done.
        iApply (interp_lea with "Hstk4v"); done.
      }
      iSplit.
      { iPureIntro; repeat split; solve_addr+Hastk_inbounds Hastk3_inbounds Hastk. }

      iDestruct (big_sepL_sep with "Hstk_val0") as "[_ H]".
      iApply (big_sepL_mono with "H").
      iIntros (?? Hin) "%". iPureIntro.
      eapply region_state_pub_temp;[apply HW'|].
      apply std_sta_update_multiple_lookup_in_i.
      apply elem_of_list_lookup. eauto.
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
    - clear-Hentry. iPureIntro. simplify_map_eq. repeat f_equiv.
      rewrite encode_entry_point_eq_off in Hentry. solve_addr.
    - iPureIntro. clear. simplify_map_eq. auto.
    - iPureIntro.
      simplify_map_eq.
      clear -Ha_callee_call Hcall.
      pose proof switcher_return_entry_point.
      cbn in *.
      do 2 (f_equal; auto). solve_addr.
    - iPureIntro. clear -Hastk. simplify_map_eq.
      replace a_stk4 with (a_stk^+4)%a by solve_addr+Hastk.
      done.
    - replace a_stk4 with (a_stk^+4)%a by solve_addr+Hastk.
      iApply (interp_lea with "Hstk4v"); first done.
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
    na_inv logrel_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own logrel_nais ⊤
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
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs


    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ▷ ([∗ list] a ∈ finz.seq_between a_stk e_stk,
                   closing_revoked_resources W2 C a ∗ ⌜(revoke W2).1 !! a = Some Revoked⌝)
              ∗ na_own logrel_nais ⊤
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ sts_full_world (revoke W2) C
              ∗ region (revoke W2) C
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
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})


    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hargs & Hcs0 & Hcs1 & Hregs & Hstk & Hsts & Hr & #Hstk_val & Hcstk & Hcont & Hpost)".
    subst a_stk4.
    subst callee_stk_region.
    iAssert (⌜Forall (fun a => W.1 !! a = Some Revoked) (finz.seq_between a_stk e_stk)⌝)%I as "%Hrevoked_stk".
    {
      iDestruct (big_sepL_sep with "Hstk_val") as "[_ %]".
      iPureIntro.
      apply Forall_forall.
      intros a Ha.
      apply elem_of_list_lookup in Ha; destruct Ha as [k Ha].
      eapply H; eauto.
    }
    iApply switcher_cc_specification_gen; eauto; iFrame "∗#".
    iIntros (W' rmap' stk_mem_l stk_mem_h).
    iNext; iIntros "[H|H]".
    + clear stk_mem.
      iDestruct "H" as
        "(%Hrelated_pub_Wext_W2 & %Hdom_rmap
      & Hna & #Hinterp_W2_csp & %Hcsp_bounds
      & Hsts_C & Hr_C & Hfrm_close_W2
      & Hcstk_frag & Hrel_stk_C
      & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp
      & [%warg0 [Hca0 #Hinterp_wca0] ] & [%warg1 [Hca1 #Hinterp_wca1] ]
      & Hrmap & Hstk_l & Hstk_h & HK)".

      iDestruct ( big_sepL2_length with "Hstk_h" ) as "%Hlen_stk_h".
      iDestruct ( big_sepL2_length with "Hstk_l" ) as "%Hlen_stk_l".
      iAssert (
          [∗ list] a ; v ∈ finz.seq_between (a_stk ^+ 4)%a e_stk ; stk_mem_h, a ↦ₐ v ∗ closing_resources interp W' C a v
        )%I with "[Hfrm_close_W2 Hstk_h]" as "Hfrm_close_W2".
      { rewrite /region_pointsto.
        iDestruct (big_sepL2_sep  with "[$Hstk_h $Hfrm_close_W2]") as "$".
      }
      iEval (rewrite <- (app_nil_r (finz.seq_between (a_stk ^+ 4)%a e_stk))) in "Hr_C".
      iDestruct (region_close_list_interp_gen with "[$Hr_C $Hfrm_close_W2]") as "Hr_C".
      { apply finz_seq_between_NoDup. }
      { set_solver+. }
      { by rewrite finz_seq_between_length in Hlen_stk_l. }
      rewrite -region_open_nil.
      iMod (revoked_by_separation_many with "[$Hr_C $Hsts_C $Hstk_l]")
        as "(Hr_C & Hsts_C & Hstk_l & %Hstk_l_revoked)".
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
        rewrite Forall_forall in Hrevoked_stk.
        apply Hrevoked_stk in H.
        done.
    }
    iMod (monotone_revoke_stack_alt with "[$Hinterp_W2_csp $Hsts_C $Hr_C]")
      as (l') "(%Hl_unk' & Hsts_C & Hr_C & Hfrm_close_W2 & >[%stk_mem_h' Hstk_h] & Hrevoked_l')".
    iDestruct (region_pointsto_split with "[$Hstk_l $Hstk_h]") as "Hstk"; auto.
    { solve_addr+ Hcsp_bounds. }
    { by rewrite finz_seq_between_length in Hlen_stk_l. }
    iApply "Hpost"; iFrame "∗%#".
    iNext.
    rewrite (finz_seq_between_split a_stk (a_stk^+4)%a); last (split; solve_addr).
    iEval (rewrite big_sepL_app).
    iFrame "Hfrm_close_W2".
    iApply big_sepL_sep.
    iSplitL; cycle 1.
      * iPureIntro. intros k a Ha.
        apply elem_of_list_lookup_2 in Ha.
        rewrite Forall_forall in Hstk_l_revoked.
        apply Hstk_l_revoked in Ha.
        apply revoke_lookup_Revoked; eauto.
      * iDestruct (big_sepL_app with "Hstk_val") as "[Hstk _]".
        iApply (big_sepL_impl with "Hstk").
        iIntros "!> %k %a %Ha [H%]".
        rewrite /closing_revoked_resources.
        iDestruct "H" as (P p ?) "(HP & $ & $ & #Hz & $ & $ & $ & $)"; iFrame "Hz".
        iExists Hpers.
        iApply "Hz"; eauto.

    + clear W' stk_mem_l stk_mem_h.
      set (stk_mem_l := [wcs0_caller; wcs1_caller; wcra_caller; wcgp_caller]).
      set (stk_mem_h := drop 4 stk_mem).
      iDestruct "H" as
        "( %Hdom_rmap & %Hcsp_bounds
           & Hna
           & HPC & Hcgp & Hcra & Hcs0 & Hcs1 & Hcsp & Hca0 & Hca1
           & Hrmap & Hstk_l & Hstk_h
           & Hsts_C & Hr_C & Hclose
           & Hcstk_frag & HK)".
      pose proof (extract_temps W) as [l_unk [Hlunk_nodup Hlunk] ].
      iMod ( monotone_revoke_keep _ _ l_unk with "[$Hsts_C $Hr_C]") as
        "(Hsts_C & Hr_C & Hrevoked_l)"; auto.
      { iPureIntro; intros; auto.
        apply Hlunk.
        by apply elem_of_list_lookup_2 in H.
      }
      iSpecialize ("Hpost" $! (std_update_multiple W (finz.seq_between (a_stk ^+ 4)%a e_stk)
                                 Temporary) rmap' (stk_mem_l++stk_mem_h)).
      iDestruct (big_sepL_sep with "Hclose") as "[Hclose %]".
      rewrite revoke_std_update_multiple_eq.
      2: { apply Forall_forall.
           intros a Ha.
           assert (a ∈ finz.seq_between a_stk e_stk) as Ha'.
           { rewrite elem_of_finz_seq_between.
             rewrite elem_of_finz_seq_between in Ha.
             solve_addr.
           }
           rewrite elem_of_list_lookup in Ha'; destruct Ha' as [? ?].
           eapply H; eauto.
      }
      iApply "Hpost"; iFrame "∗%#".
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
        apply elem_of_list_lookup; eauto.
      }
      iSplitL "Hclose".
      { iApply big_sepL_sep.
        iSplitL "Hclose"; cycle 1.
        - iPureIntro; intros k a Ha.
          apply H in Ha.
          by apply revoke_lookup_Revoked.
        - iApply (big_sepL_impl with "Hclose").
          iIntros "!>!> %k %a %Ha Hclose".
          rewrite /closing_revoked_resources.
          iDestruct "Hclose" as (P p ?) "(HP & $ & #Hmono & $ & $ & $ & $ & $)"; iFrame "Hmono".
          iExists Hpers.
          iApply "Hmono"; eauto.
          iPureIntro.
          apply related_sts_pub_update_multiple_temp.
          apply Forall_forall.
          intros a' Ha'.
          assert ( a' ∈ finz.seq_between a_stk e_stk ) as Ha''.
          {
            apply elem_of_finz_seq_between in Ha'.
            apply elem_of_finz_seq_between.
            solve_addr.
          }
          apply elem_of_list_lookup in Ha''.
          destruct Ha'' as [? Ha''].
          eapply H; eauto.
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
    na_inv logrel_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own logrel_nais ⊤
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
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ▷ ([∗ list] a ∈ finz.seq_between a_stk e_stk,
                   closing_revoked_resources W2 C a ∗ ⌜(revoke W2).1 !! a = Some Revoked⌝)
              ∗ na_own logrel_nais ⊤
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ sts_full_world (revoke W2) C
              ∗ region (revoke W2) C
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
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 target callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & #Hentry & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hsts & Hr & Hstk_val & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ true)
            ; eauto; iFrame "∗#".
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
    na_inv logrel_nais Nswitcher switcher_inv

    (* PRE-CONDITION *)
    ∗ na_own logrel_nais ⊤
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
    ∗ sts_full_world W C
    ∗ region W C
    ∗ ([∗ list] a ∈ (finz.seq_between a_stk e_stk), closing_revoked_resources W C a ∗ ⌜(std W) !! a = Some Revoked⌝)
    ∗ cstack_frag cstk
    ∗ interp_continuation cstk Ws Cs

    (* POST-CONDITION *)
    ∗ ▷ ( ∀ (W2 : WORLD) (rmap' : Reg) (stk_mem : list Word),
              (* We receive a public future world of the world pre switcher call *)
              ⌜ related_sts_pub_world (std_update_multiple W callee_stk_region Temporary) W2 ⌝
              ∗ ([∗ list] a ∈ callee_stk_region, ⌜ std W2 !! a = Some Temporary ⌝ )
              ∗ ⌜ dom rmap' = all_registers_s ∖ {[ PC ; cgp ; cra ; csp ; ca0 ; ca1 ; cs0 ; cs1 ]} ⌝
              ∗ ▷ ([∗ list] a ∈ finz.seq_between a_stk e_stk,
                   closing_revoked_resources W2 C a ∗ ⌜(revoke W2).1 !! a = Some Revoked⌝)
              ∗ na_own logrel_nais ⊤
              ∗ ⌜ (b_stk <= a_stk4 ∧ a_stk4 <= e_stk ∧ (a_stk + 4) = Some a_stk4)%a ⌝
              (* Interpretation of the world *)
              ∗ sts_full_world (revoke W2) C
              ∗ region (revoke W2) C
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
            -∗ WP Seq (Instr Executable) {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }})

    ⊢ WP Seq (Instr Executable)
      {{ v, ⌜v = HaltedV⌝ → na_own logrel_nais ⊤ }}.
  Proof.
    iIntros (a_stk4 callee_stk_region Hdom Hrdom) "(#Hswitcher & Hna & HPC & Hcgp & Hcra & Hcsp & Hct1 & #Htarget_v
    & Hcs0 & Hcs1 & Hargs & Hregs & Hstk & Hsts & Hr & Hstk_val & Hcstk & Hcont & Hpost)".
    iApply (switcher_cc_specification_gen_revoked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ false)
            ; eauto; iFrame "∗#".
  Qed.

  (* TODO I need a way to get rid off the disjunction of output and meet the specification together,
     because the examples do not rely on the call to actually go through...
   *)

End Switcher.
